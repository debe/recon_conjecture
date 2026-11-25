//! recon-relay: the live-event relay behind the fleet's canvas page.
//!
//! Not authoritative: git + CI hold the truth. The relay only fans events out fast.
//!
//! * `POST /events`  body: one compact JSON object `{"id": "...", "kind": "...", ...}`,
//!   header `Authorization: Bearer <token>`. The principal comes from the token.
//! * `GET /stream`   Server-Sent Events; replays the last events (or those after
//!   `Last-Event-ID` / `?since=`), then streams live ones.
//! * `GET /recent?limit=N`   the last N envelopes as a JSON array.
//! * `GET /health`
//!
//! Zero copy: the request body (`Bytes`) is never re-encoded. Each event becomes one
//! `Arc<Frame>` holding a small envelope head, the original body and a tail; every
//! subscriber and the append-only log receive clones of those `Bytes` (a refcount bump),
//! never a copy of the payload. Events persisted on disk are read back as slices of one
//! buffer.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet, VecDeque};
use std::convert::Infallible;
use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use axum::body::{Body, Bytes};
use axum::extract::{DefaultBodyLimit, Query, State};
use axum::http::{HeaderMap, HeaderValue, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::Router;
use futures_util::stream;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use subtle::ConstantTimeEq;
use tokio::sync::{broadcast, mpsc};

const MAX_BODY: usize = 16 * 1024;
const RING: usize = 5000;
const REPLAY_DEFAULT: usize = 200;
const MAX_CONNS: usize = 256;
const RATE_PER_SEC: f64 = 20.0;
const BURST: f64 = 100.0;
const PING: Duration = Duration::from_secs(20);

// --------------------------------------------------------------------------- frames

/// One event as it travels: `head ++ body ++ tail` is the envelope JSON line.
struct Frame {
    seq: u64,
    head: Bytes,
    body: Bytes,
    tail: Bytes,
}

impl Frame {
    fn new(seq: u64, principal: &str, received_ms: u128, body: Bytes) -> Self {
        let head = format!(
            "{{\"seq\":{seq},\"principal\":{},\"received_ms\":{received_ms},\"event\":",
            serde_json::to_string(principal).expect("string serializes")
        );
        Frame { seq, head: Bytes::from(head), body, tail: Bytes::from_static(b"}") }
    }

    /// A line read back from the log: the whole envelope is one slice of the file buffer.
    fn from_line(seq: u64, line: Bytes) -> Self {
        Frame { seq, head: line, body: Bytes::new(), tail: Bytes::new() }
    }

    fn parts(&self) -> [&Bytes; 3] {
        [&self.head, &self.body, &self.tail]
    }

    fn sse_chunks(&self) -> [Bytes; 5] {
        [
            Bytes::from(format!("id: {}\ndata: ", self.seq)),
            self.head.clone(),
            self.body.clone(),
            self.tail.clone(),
            Bytes::from_static(b"\n\n"),
        ]
    }
}

#[derive(Deserialize)]
struct Incoming<'a> {
    #[serde(borrow)]
    id: Cow<'a, str>,
    #[serde(borrow)]
    kind: Cow<'a, str>,
}

#[derive(Deserialize)]
struct Logged<'a> {
    seq: u64,
    #[serde(borrow)]
    event: Incoming<'a>,
}

fn valid_kind(kind: &str) -> bool {
    !kind.is_empty() && kind.len() <= 32 && kind.bytes().all(|b| b.is_ascii_lowercase() || b == b'_')
}

// --------------------------------------------------------------------------- auth

struct Tokens(Vec<(String, [u8; 32])>);

impl Tokens {
    /// File format: one `principal sha256hex(token)` per line; `#` starts a comment.
    fn parse(text: &str) -> io::Result<Self> {
        let mut out = Vec::new();
        for (n, line) in text.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let bad = || io::Error::new(io::ErrorKind::InvalidData, format!("tokens line {}", n + 1));
            let (who, hash) = line.split_once(char::is_whitespace).ok_or_else(bad)?;
            let mut digest = [0u8; 32];
            hex::decode_to_slice(hash.trim(), &mut digest).map_err(|_| bad())?;
            out.push((who.to_owned(), digest));
        }
        Ok(Tokens(out))
    }

    /// Constant time in the token and over every entry.
    fn principal(&self, token: &[u8]) -> Option<&str> {
        let digest: [u8; 32] = Sha256::digest(token).into();
        let mut found = None;
        for (who, want) in &self.0 {
            if bool::from(digest.ct_eq(want)) {
                found = Some(who.as_str());
            }
        }
        found
    }
}

fn bearer(headers: &HeaderMap) -> Option<&[u8]> {
    let v = headers.get(header::AUTHORIZATION)?.as_bytes();
    v.strip_prefix(b"Bearer ")
}

// --------------------------------------------------------------------------- state

struct Inner {
    ring: VecDeque<Arc<Frame>>,
    ids: HashSet<String>,
    next_seq: u64,
    log: File,
    log_path: PathBuf,
    log_lines: usize,
    buckets: HashMap<String, (f64, Instant)>,
}

struct App {
    tokens: Tokens,
    inner: Mutex<Inner>,
    tx: broadcast::Sender<Arc<Frame>>,
    conns: AtomicUsize,
    origin: HeaderValue,
}

impl App {
    fn lock(&self) -> MutexGuard<'_, Inner> {
        self.inner.lock().unwrap_or_else(|p| p.into_inner())
    }
}

/// Ring of frames, ids seen, next sequence number, lines in the file.
type Loaded = (VecDeque<Arc<Frame>>, HashSet<String>, u64, usize);

fn load_log(path: &Path) -> io::Result<Loaded> {
    let buf = match std::fs::read(path) {
        Ok(b) => Bytes::from(b),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Bytes::new(),
        Err(e) => return Err(e),
    };
    let mut ring = VecDeque::new();
    let mut ids = HashSet::new();
    let mut last = 0;
    let mut lines = 0;
    for line in buf.split(|&b| b == b'\n') {
        if line.is_empty() {
            continue;
        }
        lines += 1;
        let Ok(rec) = serde_json::from_slice::<Logged>(line) else { continue };
        last = last.max(rec.seq);
        ids.insert(rec.event.id.into_owned());
        ring.push_back(Arc::new(Frame::from_line(rec.seq, buf.slice_ref(line))));
        if ring.len() > RING {
            ring.pop_front();
        }
    }
    Ok((ring, ids, last + 1, lines))
}

fn write_frame(out: &mut impl Write, f: &Frame) -> io::Result<()> {
    for p in f.parts() {
        out.write_all(p)?;
    }
    out.write_all(b"\n")
}

impl Inner {
    fn append(&mut self, f: &Frame) -> io::Result<()> {
        write_frame(&mut self.log, f)?;
        self.log_lines += 1;
        if self.log_lines > 2 * RING {
            self.compact()?;
        }
        Ok(())
    }

    /// Rewrite the log to the frames still in memory (atomic rename).
    fn compact(&mut self) -> io::Result<()> {
        let tmp = self.log_path.with_extension("jsonl.tmp");
        let mut out = io::BufWriter::new(File::create(&tmp)?);
        for f in &self.ring {
            write_frame(&mut out, f)?;
        }
        out.into_inner()?.sync_all()?;
        std::fs::rename(&tmp, &self.log_path)?;
        self.log = OpenOptions::new().append(true).open(&self.log_path)?;
        self.log_lines = self.ring.len();
        Ok(())
    }

    fn allow(&mut self, who: &str) -> bool {
        let now = Instant::now();
        let (tokens, at) = self.buckets.entry(who.to_owned()).or_insert((BURST, now));
        *tokens = (*tokens + now.duration_since(*at).as_secs_f64() * RATE_PER_SEC).min(BURST);
        *at = now;
        if *tokens >= 1.0 {
            *tokens -= 1.0;
            true
        } else {
            false
        }
    }
}

// --------------------------------------------------------------------------- handlers

fn text(code: StatusCode, msg: &'static str) -> Response {
    (code, msg).into_response()
}

async fn post_event(State(app): State<Arc<App>>, headers: HeaderMap, body: Bytes) -> Response {
    if body.len() > MAX_BODY {
        return text(StatusCode::PAYLOAD_TOO_LARGE, "body too large\n");
    }
    let Some(who) = bearer(&headers).and_then(|t| app.tokens.principal(t)) else {
        eprintln!("recon-relay: 401 rejected POST");
        return text(StatusCode::UNAUTHORIZED, "unauthorized\n");
    };
    // SSE `data:` lines must not contain newlines; the emitter sends compact JSON.
    if body.iter().any(|&b| b == b'\n' || b == b'\r') {
        return text(StatusCode::BAD_REQUEST, "body must be one line of compact JSON\n");
    }
    let id = match serde_json::from_slice::<Incoming>(&body) {
        Ok(ev) if ev.id.len() <= 64 && !ev.id.is_empty() && valid_kind(&ev.kind) => ev.id.into_owned(),
        _ => return text(StatusCode::BAD_REQUEST, "expected {\"id\":..., \"kind\":[a-z_]+, ...}\n"),
    };
    let received_ms = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis()).unwrap_or(0);
    let mut inner = app.lock();
    if !inner.allow(who) {
        return text(StatusCode::TOO_MANY_REQUESTS, "rate limited\n");
    }
    if inner.ids.contains(&id) {
        return text(StatusCode::OK, "duplicate\n");
    }
    let seq = inner.next_seq;
    let frame = Arc::new(Frame::new(seq, who, received_ms, body));
    if let Err(e) = inner.append(&frame) {
        eprintln!("recon-relay: log write failed: {e}");
        return text(StatusCode::INTERNAL_SERVER_ERROR, "log write failed\n");
    }
    inner.next_seq += 1;
    inner.ids.insert(id);
    inner.ring.push_back(frame.clone());
    if inner.ring.len() > RING
        && let Some(old) = inner.ring.pop_front()
        && let Ok(rec) = serde_json::from_slice::<Logged>(&concat(&old))
    {
        inner.ids.remove(rec.event.id.as_ref());
    }
    drop(inner);
    let _ = app.tx.send(frame); // no subscribers is fine
    (StatusCode::ACCEPTED, format!("{seq}\n")).into_response()
}

/// Only used when an event leaves the ring (rare): rebuild its envelope to read its id.
fn concat(f: &Frame) -> Vec<u8> {
    f.parts().iter().flat_map(|p| p.iter().copied()).collect()
}

struct ConnGuard(Arc<App>);

impl Drop for ConnGuard {
    fn drop(&mut self) {
        self.0.conns.fetch_sub(1, Ordering::Relaxed);
    }
}

#[derive(Deserialize)]
struct StreamQuery {
    since: Option<u64>,
}

async fn stream_events(
    State(app): State<Arc<App>>,
    headers: HeaderMap,
    Query(q): Query<StreamQuery>,
) -> Response {
    if app.conns.fetch_add(1, Ordering::Relaxed) >= MAX_CONNS {
        app.conns.fetch_sub(1, Ordering::Relaxed);
        return text(StatusCode::SERVICE_UNAVAILABLE, "too many listeners\n");
    }
    let guard = ConnGuard(app.clone());
    let since = headers
        .get("last-event-id")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.parse::<u64>().ok())
        .or(q.since);
    // Subscribe while holding the lock so no event falls between replay and live.
    let (replay, mut rx) = {
        let inner = app.lock();
        let replay: Vec<Arc<Frame>> = match since {
            Some(s) => inner.ring.iter().filter(|f| f.seq > s).cloned().collect(),
            None => inner.ring.iter().rev().take(REPLAY_DEFAULT).rev().cloned().collect(),
        };
        (replay, app.tx.subscribe())
    };
    let (out, chunks) = mpsc::channel::<Bytes>(256);
    tokio::spawn(async move {
        let _guard = guard;
        let send = |b: Bytes| out.send(b);
        if send(Bytes::from_static(b"retry: 3000\n\n")).await.is_err() {
            return;
        }
        let mut last = 0;
        for f in replay {
            for c in f.sse_chunks() {
                if out.send(c).await.is_err() {
                    return;
                }
            }
            last = f.seq;
        }
        let mut ping = tokio::time::interval(PING);
        ping.tick().await;
        loop {
            tokio::select! {
                r = rx.recv() => match r {
                    Ok(f) => {
                        if f.seq <= last { continue; }
                        for c in f.sse_chunks() {
                            if out.send(c).await.is_err() { return; }
                        }
                        last = f.seq;
                    }
                    Err(broadcast::error::RecvError::Lagged(_)) => {
                        if out.send(Bytes::from_static(b"event: resync\ndata: {}\n\n")).await.is_err() { return; }
                    }
                    Err(broadcast::error::RecvError::Closed) => return,
                },
                _ = ping.tick() => {
                    if out.send(Bytes::from_static(b": ping\n\n")).await.is_err() { return; }
                }
                _ = out.closed() => return,
            }
        }
    });
    let body = Body::from_stream(stream::unfold(chunks, |mut rx| async move {
        rx.recv().await.map(|c| (Ok::<_, Infallible>(c), rx))
    }));
    Response::builder()
        .header(header::CONTENT_TYPE, "text/event-stream")
        .header(header::CACHE_CONTROL, "no-cache")
        .header("x-accel-buffering", "no")
        .header(header::ACCESS_CONTROL_ALLOW_ORIGIN, app.origin.clone())
        .body(body)
        .expect("static headers are valid")
}

#[derive(Deserialize)]
struct RecentQuery {
    limit: Option<usize>,
}

async fn recent(State(app): State<Arc<App>>, Query(q): Query<RecentQuery>) -> Response {
    let limit = q.limit.unwrap_or(REPLAY_DEFAULT).min(RING);
    let frames: Vec<Arc<Frame>> = {
        let inner = app.lock();
        inner.ring.iter().rev().take(limit).rev().cloned().collect()
    };
    let mut chunks = Vec::with_capacity(frames.len() * 4 + 2);
    chunks.push(Bytes::from_static(b"["));
    for (i, f) in frames.iter().enumerate() {
        if i > 0 {
            chunks.push(Bytes::from_static(b","));
        }
        chunks.extend(f.parts().into_iter().cloned());
    }
    chunks.push(Bytes::from_static(b"]"));
    Response::builder()
        .header(header::CONTENT_TYPE, "application/json")
        .header(header::CACHE_CONTROL, "no-cache")
        .header(header::ACCESS_CONTROL_ALLOW_ORIGIN, app.origin.clone())
        .body(Body::from_stream(stream::iter(chunks.into_iter().map(Ok::<_, Infallible>))))
        .expect("static headers are valid")
}

async fn health(State(app): State<Arc<App>>) -> String {
    let seq = app.lock().next_seq - 1;
    format!("ok seq={seq} listeners={}\n", app.conns.load(Ordering::Relaxed))
}

fn router(app: Arc<App>) -> Router {
    Router::new()
        .route("/events", post(post_event))
        .route("/stream", get(stream_events))
        .route("/recent", get(recent))
        .route("/health", get(health))
        .layer(DefaultBodyLimit::max(MAX_BODY))
        .with_state(app)
}

// --------------------------------------------------------------------------- main

fn env_path(var: &str, fallback: impl FnOnce() -> PathBuf) -> PathBuf {
    std::env::var_os(var).map(PathBuf::from).unwrap_or_else(fallback)
}

fn build_app(tokens: Tokens, log_path: PathBuf, origin: &str) -> io::Result<Arc<App>> {
    let (ring, ids, next_seq, log_lines) = load_log(&log_path)?;
    let log = OpenOptions::new().create(true).append(true).open(&log_path)?;
    let (tx, _) = broadcast::channel(1024);
    Ok(Arc::new(App {
        tokens,
        inner: Mutex::new(Inner { ring, ids, next_seq, log, log_path, log_lines, buckets: HashMap::new() }),
        tx,
        conns: AtomicUsize::new(0),
        origin: HeaderValue::from_str(origin).map_err(|_| io::Error::other("bad origin"))?,
    }))
}

#[tokio::main(flavor = "current_thread")]
async fn main() -> io::Result<()> {
    let state_dir = env_path("STATE_DIRECTORY", || PathBuf::from("/var/lib/recon-relay"));
    let tokens_path = env_path("RECON_RELAY_TOKENS", || {
        env_path("CREDENTIALS_DIRECTORY", || PathBuf::from("/etc/recon-relay")).join("tokens")
    });
    let bind = std::env::var("RECON_RELAY_BIND").unwrap_or_else(|_| "127.0.0.1:8090".into());
    let origin = std::env::var("RECON_RELAY_ORIGIN").unwrap_or_else(|_| "https://debe.github.io".into());

    let tokens = Tokens::parse(&std::fs::read_to_string(&tokens_path)?)?;
    let app = build_app(tokens, state_dir.join("events.jsonl"), &origin)?;
    let listener = tokio::net::TcpListener::bind(&bind).await?;
    eprintln!(
        "recon-relay: listening on {bind}, {} publishers, next seq {}",
        app.tokens.0.len(),
        app.lock().next_seq
    );
    axum::serve(listener, router(app))
        .with_graceful_shutdown(async {
            let mut term = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
                .expect("SIGTERM handler");
            tokio::select! { _ = term.recv() => {}, _ = tokio::signal::ctrl_c() => {} }
        })
        .await
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(t: &str) -> String {
        hex::encode(Sha256::digest(t.as_bytes()))
    }

    #[test]
    fn tokens_map_to_principals_and_reject_others() {
        let t = Tokens::parse(&format!("# c\ndebe {}\nci {}\n", hash("a"), hash("b"))).unwrap();
        assert_eq!(t.principal(b"a"), Some("debe"));
        assert_eq!(t.principal(b"b"), Some("ci"));
        assert_eq!(t.principal(b"c"), None);
        assert!(Tokens::parse("debe nothex\n").is_err());
    }

    #[test]
    fn envelope_is_valid_json_and_reads_back_from_the_log() {
        let body = Bytes::from_static(br#"{"id":"e1","kind":"leased","step":"found_001"}"#);
        let f = Frame::new(7, "debe", 123, body.clone());
        let line = concat(&f);
        let v: serde_json::Value = serde_json::from_slice(&line).unwrap();
        assert_eq!(v["seq"], 7);
        assert_eq!(v["principal"], "debe");
        assert_eq!(v["event"]["kind"], "leased");
        // the payload is shared, not copied
        assert_eq!(f.body.as_ptr(), body.as_ptr());

        let dir = std::env::temp_dir().join(format!("recon-relay-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("events.jsonl");
        let mut file = File::create(&p).unwrap();
        write_frame(&mut file, &f).unwrap();
        write_frame(&mut file, &Frame::new(8, "ci", 124, Bytes::from_static(br#"{"id":"e2","kind":"ci_verdict"}"#))).unwrap();
        let (ring, ids, next, lines) = load_log(&p).unwrap();
        assert_eq!((ring.len(), next, lines), (2, 9, 2));
        assert!(ids.contains("e1") && ids.contains("e2"));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn kinds_are_lowercase_words() {
        assert!(valid_kind("agent_start"));
        assert!(!valid_kind("Agent"));
        assert!(!valid_kind(""));
        assert!(!valid_kind("x<script>"));
    }
}
