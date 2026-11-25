# recon-relay

A small pub/sub relay for the live map. Publishers (`tools/live.py` in the desk, the gate, the
agent hooks and CI) POST events; browsers subscribe with Server-Sent Events. It is never
authoritative: the truth stays in git, and the page starts from a snapshot of `main`.

- **Zero-copy fan-out.** The body is kept as `Bytes`, wrapped once in an `Arc<Frame>`, and shared
  by every subscriber through `tokio::sync::broadcast`.
- **Replay.** The last events are kept in a ring persisted to `events.jsonl`. A new subscriber
  gets the recent history, and a reconnecting one resumes from `Last-Event-ID`. A subscriber
  that falls behind gets a `resync` event instead of blocking anyone.
- **Auth.** Each publisher has its own random bearer token. The relay stores only
  `<principal> <sha256(token)>` lines, compares in constant time, and takes the principal from
  the token, never from the request body.
- **Limits.** 16 KB bodies, a per-principal rate limit, a cap on open streams, and CORS for the
  page's origin only.

## Endpoints

| Endpoint | Does |
|---|---|
| `POST /events` | publish one event (bearer token) |
| `GET /stream` | Server-Sent Events, with replay and `Last-Event-ID` |
| `GET /recent` | the recent events as JSON |
| `GET /health` | `ok seq=<n> listeners=<n>` |

## Build and run

```sh
cargo build --release --target x86_64-unknown-linux-musl   # one static binary, about 1 MB
```

| Variable | Default | Meaning |
|---|---|---|
| `RECON_RELAY_BIND` | `127.0.0.1:8090` | listen address; put a TLS proxy in front |
| `RECON_RELAY_ORIGIN` | `https://debe.github.io` | the only origin allowed by CORS |
| `RECON_RELAY_TOKENS` | `$CREDENTIALS_DIRECTORY/tokens` | the token-hash file |
| `STATE_DIRECTORY` | `/var/lib/recon-relay` | where `events.jsonl` lives |

The token file has one `<principal> <sha256 hex of the token>` line per publisher:

```sh
token=$(openssl rand -hex 32)
printf '%s %s\n' "<handle>" "$(printf %s "$token" | sha256sum | cut -d' ' -f1)"
```

The publisher keeps the token in `~/.config/recon/live.token` (mode 0600), or, for CI, in the
repository secret `RECON_LIVE_TOKEN`.

A reverse proxy in front must not buffer `/stream` (for nginx: `proxy_buffering off` and long
read timeouts) and should rate-limit `POST /events`.

## Deployment

How and where the relay runs is the operator's business and stays out of this repository: keep
your service unit, proxy config, deploy scripts and rollback notes in `relay/local/`, which git
ignores.
