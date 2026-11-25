"use strict";
// Reconstruction Fleet: canvas map of the ledger (snapshot from main) + live overlay (relay SSE).
// The page is a view. Truth is the ledger on main, checked by CI.

const params = new URLSearchParams(location.search);
const RELAY = params.get("relay") || "https://recon.knownhosts.org";
const REPO = "debe/recon_conjecture";
const LOADED_AT = Date.now();
const STATUSES = ["proposed", "frozen", "reduced", "checked", "refuted", "withdrawn"];

const S = {
  programs: [], steps: new Map(), leases: new Map(), pending: new Map(), agents: new Map(), stopped: new Set(), fidelity: new Map(),
  seen: new Map(), ci: [], graveyard: [], ticker: [], fx: [], lastSeq: 0, snapshotAt: 0,
  live: false, ledgerEvents: [],
  snapLeases: null,   // leases on origin when the snapshot was built; null until it loads
};

// A lease event older than the snapshot, for a step the snapshot shows unleased, was released
// since (or never backed by a ref): the relay replays history, the snapshot read the refs.
function staleLease(sid, t) {
  return S.snapLeases !== null && t < S.snapshotAt && !(sid in S.snapLeases);
}

// A live status change shows until main catches up with it; an older event replayed for a
// step that main has since moved past is history, not news.
const RANK = { proposed: 0, frozen: 1, reduced: 2, checked: 3, refuted: 3, withdrawn: 3 };
function ahead(live, main) { return !!live && (RANK[live] ?? -1) > (RANK[main] ?? -1); }
let L = { nodes: new Map(), regions: [], w: 600, h: 400, graveY: 0 };
const view = { x: 24, y: 24, k: 1, fitted: false };
const canvas = document.getElementById("map");
const ctx = canvas.getContext("2d");
const $ = id => document.getElementById(id);
const cssVar = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const color = s => cssVar("--" + (STATUSES.includes(s) ? s : "proposed"));
const who = actor => (actor || "?").split("/")[0];

// ------------------------------------------------------------------ layout

const R = 15, DX = 156, DY = 104, PAD = 40, GAP = 36, HEAD = 46;
const ID_LINE = 22;   // characters per line of a step id under its node

// Step ids are long snake_case names: break them at underscores into lines of at most ID_LINE
// characters, so neighbouring labels never run into each other.
function wrapId(id) {
  const lines = [];
  let cur = "";
  for (const part of id.split("_")) {
    const next = cur ? cur + "_" + part : part;
    if (cur && next.length > ID_LINE) { lines.push(cur + "_"); cur = part; } else cur = next;
  }
  lines.push(cur);
  return lines.length > 2 ? [lines[0], clip(lines.slice(1).join(""), ID_LINE)] : lines;
}

function kids(id) {
  const s = S.steps.get(id);
  if (!s) return [];
  const set = new Set(s.children || []);
  (s.reductions || []).forEach(r => r.children.forEach(c => set.add(c)));
  return [...set].filter(c => S.steps.has(c)).sort();
}
function span(id) { const k = kids(id); return k.length ? k.reduce((a, c) => a + span(c), 0) : 1; }
function depth(id) { const k = kids(id); return 1 + (k.length ? Math.max(...k.map(depth)) : 0); }

function computeLayout() {
  const nodes = new Map(), regions = [];
  const progs = S.programs.length ? S.programs
    : [...new Set([...S.steps.values()].map(s => s.program))].map(id => ({ id, title: id }));
  let y = 0;
  const place = (id, x0, d, top) => {
    // +40: room for a lease chip above the first row without covering the program title
    nodes.set(id, { x: x0 + span(id) * DX / 2, y: top + HEAD + 52 + d * DY });
    let x = x0;
    for (const c of kids(id)) { place(c, x, d + 1, top); x += span(c) * DX; }
  };
  for (const p of progs) {
    const roots = [...S.steps.values()]
      .filter(s => s.program === p.id && (!s.parent || !S.steps.has(s.parent)))
      .map(s => s.id).sort();
    const w = roots.reduce((a, r) => a + span(r), 0);
    const d = roots.length ? Math.max(...roots.map(depth)) : 0;
    let x = PAD;
    for (const r of roots) { place(r, x, 0, y); x += span(r) * DX; }
    const h = HEAD + (d ? d * DY + 62 : 26);
    regions.push({ p, y, h, w: Math.max(3, w) * DX + 2 * PAD, n: roots.length });
    y += h + GAP;
  }
  const w = Math.max(640, ...regions.map(r => r.w));
  regions.forEach(r => (r.w = w));
  L = { nodes, regions, w, h: y + 120, graveY: y };
  if (!view.fitted) fit();
}

function fit() {
  const cw = canvas.clientWidth || 800;
  view.k = Math.min(1.2, Math.max(0.35, (cw - 48) / L.w));
  view.x = 24; view.y = ($("legend").offsetHeight || 36) + 22; view.fitted = true;   // below the legend
}

// ------------------------------------------------------------------ drawing

function roundRect(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath();
}
function clip(text, max) { return text.length > max ? text.slice(0, max - 1) + "…" : text; }

function draw() {
  const dpr = window.devicePixelRatio || 1;
  const cw = canvas.clientWidth, ch = canvas.clientHeight;
  if (canvas.width !== Math.round(cw * dpr) || canvas.height !== Math.round(ch * dpr)) {
    canvas.width = Math.round(cw * dpr); canvas.height = Math.round(ch * dpr);
  }
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.setTransform(dpr * view.k, 0, 0, dpr * view.k, dpr * view.x, dpr * view.y);
  const now = Date.now(), t = performance.now();
  const ink = cssVar("--ink"), muted = cssVar("--muted"), line = cssVar("--line");
  const font = cssVar("--font");

  for (const r of L.regions) {
    ctx.fillStyle = cssVar("--region"); ctx.strokeStyle = line; ctx.lineWidth = 1;
    roundRect(0, r.y, r.w, r.h, 14); ctx.fill(); ctx.stroke();
    const steps = [...S.steps.values()].filter(s => s.program === r.p.id);
    const closed = steps.filter(s => s.status === "checked" || s.status === "refuted").length;
    ctx.fillStyle = ink; ctx.font = `600 14px ${font}`;
    ctx.fillText(r.p.id, 16, r.y + 24);
    ctx.fillStyle = muted; ctx.font = `12px ${font}`;
    ctx.fillText(`${clip(r.p.title || "", 70)}  ·  ${closed}/${steps.length} closed`,
      16 + ctx.measureText(r.p.id).width * 1.2 + 10, r.y + 24);
    if (!r.n) { ctx.fillText("no steps yet", 16, r.y + 52); }
  }

  ctx.lineWidth = 1.5;
  for (const [id, a] of L.nodes) {
    const s = S.steps.get(id);
    for (const red of s.reductions || []) {
      for (const c of red.children) {
        const b = L.nodes.get(c);
        if (!b) continue;
        ctx.strokeStyle = red.status === "dead" ? line : color(s.status);
        ctx.setLineDash(red.status === "dead" ? [4, 4] : []);
        ctx.beginPath(); ctx.moveTo(a.x, a.y + R); ctx.lineTo(b.x, b.y - R); ctx.stroke();
      }
    }
  }
  ctx.setLineDash([]);

  for (const [id, p] of L.nodes) {
    const s = S.steps.get(id);
    const twinRefuted = s.status === "refuted";
    ctx.strokeStyle = twinRefuted ? color("refuted") : line;
    ctx.lineWidth = twinRefuted ? 3 : 1;
    ctx.beginPath(); ctx.arc(p.x, p.y, R + 5, 0, 2 * Math.PI); ctx.stroke();
    ctx.fillStyle = color(s.status);
    ctx.beginPath(); ctx.arc(p.x, p.y, R, 0, 2 * Math.PI); ctx.fill();
    const pend = S.pending.get(id);
    if (ahead(pend, s.status)) {
      ctx.strokeStyle = color(pend); ctx.lineWidth = 2.5; ctx.setLineDash([3, 3]);
      ctx.beginPath(); ctx.arc(p.x, p.y, R + 9, (t / 900) % (2 * Math.PI), (t / 900) % (2 * Math.PI) + 2 * Math.PI);
      ctx.stroke(); ctx.setLineDash([]);
    }
    ctx.fillStyle = ink; ctx.font = `600 11px ${font}`; ctx.textAlign = "center";
    const idLines = wrapId(id);
    idLines.forEach((ln, i) => ctx.fillText(ln, p.x, p.y + R + 18 + i * 13));
    ctx.fillStyle = muted; ctx.font = `11px ${font}`;
    ctx.fillText(clip(s.title || "", 24) + (ahead(pend, s.status) ? ` (${pend}, unmerged)` : ""),
      p.x, p.y + R + 32 + (idLines.length - 1) * 13);
    ctx.textAlign = "left";

    // the agents working on this step sit on an arc above it, one breathing dot per agent in
    // its role's colour (above, so they never cover the label underneath)
    const crew = agentsOn(id);
    const spread = Math.min(Math.PI * 0.9, crew.length * 0.42);
    crew.forEach((a, i) => {
      const ang = -Math.PI / 2 + (crew.length > 1 ? -spread / 2 + spread * i / (crew.length - 1) : 0);
      const ax = p.x + Math.cos(ang) * (R + 13), ay = p.y + Math.sin(ang) * (R + 13);
      const r = 4.5 + 0.8 * Math.sin(t / 420 + i * 1.7);
      ctx.fillStyle = roleColor(a.role); ctx.strokeStyle = cssVar("--surface"); ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(ax, ay, r, 0, 2 * Math.PI); ctx.fill(); ctx.stroke();
    });

    const lease = S.leases.get(id);
    if (lease && Date.parse(lease.expires) > now) {
      const since = now - (lease.beat || now - 1e9);
      if (since < 2500) {
        const k = since / 2500;
        ctx.strokeStyle = cssVar("--lease"); ctx.globalAlpha = 1 - k; ctx.lineWidth = 3;
        ctx.beginPath(); ctx.arc(p.x, p.y, R + 6 + k * 26, 0, 2 * Math.PI); ctx.stroke();
        ctx.globalAlpha = 1;
      }
      const label = clip(`${lease.holder}${lease.note ? " · " + lease.note : ""}`, 46);
      ctx.font = `600 11px ${font}`;
      const w = ctx.measureText(label).width + 16;
      const cx = Math.min(Math.max(p.x, w / 2 + 6), L.w - w / 2 - 6);   // keep inside the map
      ctx.fillStyle = cssVar("--lease");
      roundRect(cx - w / 2, p.y - R - 42, w, 20, 10); ctx.fill();   // clear of the agent orbit
      ctx.fillStyle = "#1d1f24"; ctx.textAlign = "center";
      ctx.fillText(label, cx, p.y - R - 28); ctx.textAlign = "left";
    }
  }

  S.fx = S.fx.filter(f => t - f.t0 < 1600);
  for (const f of S.fx) {
    const p = L.nodes.get(f.step);
    if (!p) continue;
    const k = (t - f.t0) / 1600;
    if (f.type === "burst") {
      ctx.strokeStyle = color("checked"); ctx.lineWidth = 4 * (1 - k); ctx.globalAlpha = 1 - k;
      for (let i = 0; i < 3; i++) {
        ctx.beginPath(); ctx.arc(p.x, p.y, R + 8 + k * (40 + i * 18), 0, 2 * Math.PI); ctx.stroke();
      }
    } else if (f.type === "bad") {
      ctx.globalAlpha = Math.abs(Math.sin(k * Math.PI * 5)) * (1 - k);
      ctx.fillStyle = color("refuted");
      ctx.beginPath(); ctx.arc(p.x, p.y, R + 3, 0, 2 * Math.PI); ctx.fill();
    } else {
      ctx.strokeStyle = color("frozen"); ctx.lineWidth = 2; ctx.globalAlpha = 1 - k;
      ctx.beginPath(); ctx.arc(p.x, p.y, R + 6 + k * 14, 0, 2 * Math.PI); ctx.stroke();
    }
    ctx.globalAlpha = 1;
  }

  // graveyard strip: releases and dead ends, newest first
  const gy = L.graveY;
  ctx.fillStyle = muted; ctx.font = `600 12px ${font}`;
  ctx.fillText("GRAVEYARD", 4, gy + 8);
  ctx.font = `11px ${font}`;
  S.graveyard.slice(0, 8).forEach((g, i) => {
    const x = 4 + (i % 4) * (L.w / 4), y = gy + 30 + Math.floor(i / 4) * 34;
    ctx.fillStyle = ink;
    ctx.fillText(clip(`${g.step || ""} · ${g.reason || "dead end"}`, 40), x, y);
    ctx.fillStyle = muted;
    ctx.fillText(clip(`${g.note || ""} (${g.actor || ""})`, 44), x, y + 14);
  });
  if (!S.graveyard.length) { ctx.fillStyle = muted; ctx.fillText("nothing has died yet", 4, gy + 30); }

  requestAnimationFrame(draw);
}

// ------------------------------------------------------------------ interaction

const pointers = new Map();
let drag = null, pinch = null, moved = false;
canvas.addEventListener("pointerdown", e => {
  canvas.setPointerCapture(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  moved = false;
  if (pointers.size === 1) drag = { x: e.clientX, y: e.clientY, vx: view.x, vy: view.y };
  if (pointers.size === 2) {
    const [a, b] = [...pointers.values()];
    pinch = { d: Math.hypot(a.x - b.x, a.y - b.y), k: view.k };
  }
  canvas.classList.add("dragging");
});
canvas.addEventListener("pointermove", e => {
  if (!pointers.has(e.pointerId)) return;
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pinch && pointers.size === 2) {
    const [a, b] = [...pointers.values()];
    zoomAt((a.x + b.x) / 2, (a.y + b.y) / 2, pinch.k * Math.hypot(a.x - b.x, a.y - b.y) / pinch.d / view.k);
    moved = true;
  } else if (drag) {
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    if (Math.abs(dx) + Math.abs(dy) > 3) moved = true;
    view.x = drag.vx + dx; view.y = drag.vy + dy; view.moved = true;
  }
});
const up = e => {
  pointers.delete(e.pointerId);
  if (pointers.size < 2) pinch = null;
  if (!pointers.size) {
    canvas.classList.remove("dragging");
    if (!moved) pick(e);
    drag = null;
  }
};
canvas.addEventListener("pointerup", up);
canvas.addEventListener("pointercancel", up);
canvas.addEventListener("wheel", e => {
  e.preventDefault();
  zoomAt(e.clientX, e.clientY, Math.exp(-e.deltaY * 0.0015));
}, { passive: false });

function zoomAt(cx, cy, factor) {
  const r = canvas.getBoundingClientRect();
  const k = Math.min(3, Math.max(0.2, view.k * factor));
  const x = cx - r.left, y = cy - r.top;
  view.x = x - (x - view.x) * (k / view.k);
  view.y = y - (y - view.y) * (k / view.k);
  view.k = k;
}

function pick(e) {
  const r = canvas.getBoundingClientRect();
  const wx = (e.clientX - r.left - view.x) / view.k, wy = (e.clientY - r.top - view.y) / view.k;
  for (const [id, p] of L.nodes) {
    if (Math.hypot(p.x - wx, p.y - wy) <= R + 8) { openDrawer(id); return; }
  }
}

function el(tag, attrs = {}, ...children) {
  const n = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") n.className = v; else if (k === "style") n.style.cssText = v; else n.setAttribute(k, v);
  }
  for (const c of children) if (c != null) n.append(c instanceof Node ? c : document.createTextNode(String(c)));
  return n;
}
const gh = path => `https://github.com/${REPO}/blob/main/${path}`;

function openDrawer(id) {
  const s = S.steps.get(id);
  const body = $("drawer-body");
  body.replaceChildren();
  const lease = S.leases.get(id);
  // a step seen only in live events (proposed on someone's machine) has no record on main yet
  const liveOnly = !s.statement_file;
  body.append(...[
    el("h3", {}, s.title || id),
    el("div", { class: "meta" },
      el("span", { class: "pill", style: `background:${color(s.status)}` }, s.status), "  ",
      id, s.parent ? ` · child of ${s.parent}` : " · root",
      s.approved_by ? ` · approved by ${s.approved_by}` : "",
      ` · fidelity passes ${Math.max(s.fidelity_passes ?? 0, (S.fidelity.get(id) || new Set()).size)}`),
    lease && Date.parse(lease.expires) > Date.now()
      ? el("p", {}, `Leased by ${lease.holder} until ${new Date(lease.expires).toLocaleTimeString()}`
        + (lease.note ? ` — ${lease.note}` : "")) : null,
    ahead(S.pending.get(id), s.status)
      ? el("p", {}, `Live: ${S.pending.get(id)} on someone's machine. It counts once a pull request with it passes CI and merges into main.`) : null,
    liveOnly ? el("p", { class: "empty" }, "Proposed on someone's machine. The statement shows here once its pull request merges into main.") : null,
    s.statement_en ? el("p", {}, s.statement_en) : null,
    s.statement_lean ? el("pre", {}, s.statement_lean) : null,
    liveOnly ? null : el("p", {}, el("a", { href: gh(s.statement_file), target: "_blank", rel: "noopener" }, s.status === "proposed" ? "statement" : "frozen statement"),
      s.checked ? " · " : "", s.checked ? el("a", { href: gh(s.checked.file), target: "_blank", rel: "noopener" }, "checked proof") : null,
      s.refuted ? " · " : "", s.refuted ? el("a", { href: gh(s.refuted.file), target: "_blank", rel: "noopener" }, "refutation") : null),
    (s.dead_ends || []).length ? el("p", {}, `Dead ends (${s.dead_ends.length}): `
      + s.dead_ends.slice(-3).map(d => `${d.reason}: ${d.approach}`).join(" · ")) : null,
    agentsOn(id).length ? el("p", {}, `Agents on it now: ${agentsOn(id).map(agentName).join(", ")}`) : null,
  ].filter(x => x != null));
  $("drawer").hidden = false;
}
$("drawer-close").addEventListener("click", () => ($("drawer").hidden = true));
document.addEventListener("keydown", e => { if (e.key === "Escape") $("drawer").hidden = true; });

// ------------------------------------------------------------------ panels

const hhmm = ms => {
  const d = new Date(ms);
  return Date.now() - ms > 864e5 ? d.toLocaleDateString([], { month: "short", day: "numeric" })
    : d.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
};

function describe(e) {
  const k = e.kind;
  if (k === "verdict") return `${e.verdict} ${e.target || ""}`;
  if (k === "precheck") return e.ok ? "precheck passed" : `precheck failed: ${e.reason || ""}`;
  if (k === "released") return `released (${e.reason})${e.note ? ": " + e.note : ""}`;
  if (k === "beat" || k === "leased") return `${k}${e.note ? ": " + e.note : ""}`;
  if (k === "ci_verdict") return `CI ${e.result} on PR #${e.pr ?? "?"}`;
  if (k === "agent_start" || k === "agent_stop") return `${k.replace("_", " ")} ${e.agent_type || ""}`;
  return k;
}
function kindClass(e) {
  if ((e.kind === "verdict" && e.verdict === "ACCEPTED") || e.kind === "checked" || (e.kind === "precheck" && e.ok)
    || (e.kind === "ci_verdict" && e.result === "success")) return "ok";
  if (e.kind === "verdict" || e.kind === "precheck" || e.kind === "refuted"
    || (e.kind === "ci_verdict" && e.result !== "success")) return "bad";
  if (e.kind === "leased" || e.kind === "beat") return "lease";
  return "";
}

let panelsDirty = true;
function renderPanels() {
  if (!panelsDirty) return;
  panelsDirty = false;
  const items = S.live ? S.ticker : S.ledgerEvents;
  $("ticker").replaceChildren(...(items.length ? items.slice(0, 150).map(x => el("li", { class: x.fresh ? "fresh" : "" },
    el("span", { class: "t" }, hhmm(x.t)),
    el("span", {}, el("span", { class: "k " + kindClass(x.e) }, x.e.step || ""), " ",
      describe(x.e), " ", el("span", { class: "t" }, x.e.actor || ""))))
    : [el("li", { class: "empty" }, "no events yet")]));
  const cutoff = Date.now() - 15 * 60e3;
  const people = new Map();
  for (const [h, v] of S.seen) if (v.t > cutoff) people.set(h, { ...v, leases: 0, agents: 0 });
  for (const l of S.leases.values()) {
    if (Date.parse(l.expires) < Date.now()) continue;
    const h = who(l.holder);
    if (!people.has(h)) people.set(h, { t: l.beat || 0, what: l.note || "", leases: 0, agents: 0 });
    people.get(h).leases++;
  }
  for (const a of liveAgents()) {
    const h = who(a.actor);
    if (!people.has(h)) people.set(h, { t: a.t, what: "", leases: 0, agents: 0 });
    people.get(h).agents++;
  }
  $("presence").replaceChildren(...(people.size ? [...people].map(([h, v]) => el("li", {},
    el("span", { class: "who" }, h),
    el("span", { class: "what" }, `${v.leases} lease${v.leases === 1 ? "" : "s"} · ${v.agents} agent${v.agents === 1 ? "" : "s"}${v.what ? " · " + v.what : ""}`)))
    : [el("li", { class: "empty" }, "nobody is working right now")]));
  $("ci").replaceChildren(...(S.ci.length ? S.ci.slice(0, 6).map(c => el("li", {},
    el("span", { class: "t" }, hhmm(c.t)),
    el("span", {}, el("span", { class: "k " + (c.result === "success" ? "ok" : "bad") }, c.result || "?"), " ",
      c.url ? el("a", { href: c.url, target: "_blank", rel: "noopener" }, `PR #${c.pr ?? "?"}`) : `PR #${c.pr ?? "?"}`,
      c.sha ? ` · ${String(c.sha).slice(0, 7)}` : ""))) : [el("li", { class: "empty" }, "no CI runs seen yet")]));
  renderFleet();
  const steps = [...S.steps.values()];
  const n = st => steps.filter(s => s.status === st).length;
  $("counts").textContent = `${n("checked")} checked · ${n("refuted")} refuted · ${n("frozen")} open · ${steps.length} steps`;
}
setInterval(() => { panelsDirty = true; renderPanels(); }, 15000);

function legend() {
  $("legend").replaceChildren(...STATUSES.map(s => el("span", {}, el("i", { style: `background:${color(s)}` }), s)),
    el("span", {}, el("i", { style: `background:${cssVar("--lease")}` }), "leased"),
    el("span", { class: "sep" }, "|"),
    ...ROLES.map(r => el("span", { class: "role" }, el("i", { style: `background:${roleColor(r)}` }), r)));
}

// ------------------------------------------------------------------ data

function fx(step, type) { S.fx.push({ step, type, t0: performance.now() }); }

// ------------------------------------------------------------------ agents
// The hook sends agent_start/agent_stop with the workflow label (`builder:<step>:b1`,
// `fid-testing:<step>`, or a free description). Desk and gate events carry the actor
// `<handle>/<label>`: matching that label and the step to a running agent shows what it is doing.

const AGENT_TTL = 4 * 3600e3;   // an agent with no stop event after this long is presumed gone
const ROLES = ["builder", "thinker", "red-team", "fidelity-reviewer", "librarian", "strategist"];
const roleColor = r => cssVar("--role-" + (ROLES.includes(r) ? r : "other"));
const segs = a => a.label.split(":").filter(x => x && x !== a.step);
const agentName = a => segs(a).join(" · ") || a.role;
const liveAgents = () => [...S.agents.values()].filter(a => Date.now() - a.t < AGENT_TTL);
const agentsOn = id => liveAgents().filter(a => a.step === id);

function attribute(e, t) {
  if (!e.actor || !e.step) return;
  const [h, lab] = e.actor.split("/");
  const mine = liveAgents().filter(a => a.step === e.step && who(a.actor) === h);
  const hit = mine.filter(a => segs(a).includes(lab));
  const a = hit.length ? hit[0] : mine.length === 1 ? mine[0] : null;
  if (a && t >= a.t) { a.act = describe(e); a.actT = t; }
}

const ago = ms => {
  const m = Math.max(0, Math.round((Date.now() - ms) / 60e3));
  return m < 60 ? `${m} min` : `${Math.floor(m / 60)} h ${m % 60} min`;
};

function renderFleet() {
  const agents = liveAgents().sort((a, b) => a.t - b.t);
  $("fleet-count").textContent = agents.length ? `· ${agents.length}` : "";
  $("fleet").replaceChildren(...(agents.length ? agents.map(a => el("li", { class: "agent" },
    el("i", { class: "role", style: `background:${roleColor(a.role)}` }),
    el("div", { class: "body" },
      el("div", { class: "top" },
        el("span", { class: "name", title: a.label }, agentName(a)),
        el("span", { class: "t" }, ago(a.t))),
      el("div", { class: "t" }, `${who(a.actor)} · ${a.role}${a.phase ? " · " + a.phase : ""}`),
      el("div", { class: "doing" },
        a.step ? el("span", { class: "k step", "data-step": a.step }, a.step) : null,
        a.step && a.act ? " · " : "",
        a.act || (a.step ? "" : "working"))))) : [el("li", { class: "empty" }, "no agents running")]));
}
document.addEventListener("click", ev => {
  const s = ev.target.closest && ev.target.closest("[data-step]");
  if (s && S.steps.has(s.dataset.step)) openDrawer(s.dataset.step);
});

function apply(env) {
  if (!env || !env.event || env.seq <= S.lastSeq) return;
  S.lastSeq = env.seq;
  const e = env.event, step = e.step;
  const t = Date.parse(e.ts) || env.received_ms;
  const fresh = env.received_ms > LOADED_AT - 1500;
  switch (e.kind) {
    case "leased": case "beat":
      if (step && !staleLease(step, t)) S.leases.set(step, {
        holder: e.actor, note: e.note || (S.leases.get(step) || {}).note, t,
        expires: e.expires || new Date(t + (e.minutes || 120) * 60e3).toISOString(), beat: fresh ? Date.now() : 0,
      });
      break;
    case "released":
      S.leases.delete(step);
      S.graveyard.unshift({ step, actor: e.actor, reason: e.reason, note: e.note, t });
      break;
    case "dead_end":
      S.graveyard.unshift({ step, actor: e.actor, reason: e.reason, note: e.approach, t });
      break;
    case "precheck":
      if (fresh) fx(step, e.ok ? "ok" : "bad");
      if (S.leases.has(step)) S.leases.get(step).note = e.ok ? "precheck passed" : "precheck: " + (e.reason || "failed");
      break;
    case "verdict":
      if (fresh) fx(step, e.verdict === "ACCEPTED" ? "burst" : "bad");
      break;
    case "proposed": case "frozen": case "checked": case "refuted": case "reduced":
      if (step) {
        if (!S.steps.has(step) && e.kind === "proposed") {
          S.steps.set(step, { id: step, program: step.split("_")[0], title: e.title || step, status: "proposed", children: [], reductions: [] });
          computeLayout();
        }
        S.pending.set(step, e.kind);
      }
      if (e.kind === "checked" || e.kind === "refuted") S.leases.delete(step);
      break;
    case "agent_start": {
      const id = e.agent_id || `${e.actor}#${t}`;
      if (S.stopped.has(id) || Date.now() - t > AGENT_TTL) break;
      S.agents.set(id, { id, actor: e.actor, role: e.agent_type || "agent", label: e.label || "",
        step: step || null, phase: e.phase || "", t, act: "", actT: 0 });
      break;
    }
    case "agent_stop": S.stopped.add(e.agent_id); S.agents.delete(e.agent_id); break;
    case "fidelity":   // distinct reviewers that passed it, until main's record catches up
      if (step && e.verdict === "pass") {
        if (!S.fidelity.has(step)) S.fidelity.set(step, new Set());
        S.fidelity.get(step).add(e.actor);
      }
      break;
    case "ci_verdict": S.ci.unshift({ pr: e.pr, result: e.result, sha: e.sha, url: e.url, t }); break;
    case "merged": setTimeout(loadSnapshot, 90e3); break;
  }
  if (!e.kind.startsWith("agent_")) attribute(e, t);
  if (e.actor && who(e.actor) !== "ci" && env.principal !== "ci") S.seen.set(who(e.actor), { t, what: `${describe(e)}${step ? " · " + step : ""}` });
  S.ticker.unshift({ e, t, fresh });
  if (S.ticker.length > 300) S.ticker.length = 300;
  panelsDirty = true;
}

async function loadSnapshot() {
  try {
    const r = await fetch(`state.json?t=${Date.now()}`, { cache: "no-store" });
    const d = await r.json();
    S.programs = d.programs || [];
    S.steps = new Map((d.steps || []).map(s => [s.id, s]));
    S.snapshotAt = Date.parse(d.generated_at) || 0;
    for (const [sid, st] of [...S.pending]) {
      const s = S.steps.get(sid);
      if (s && !ahead(st, s.status)) S.pending.delete(sid);
    }
    S.snapLeases = d.leases || {};
    for (const [sid, l] of [...S.leases]) if (staleLease(sid, l.t || 0)) S.leases.delete(sid);
    for (const [sid, l] of Object.entries(S.snapLeases)) {
      if (!S.leases.has(sid) && Date.parse(l.expires) > Date.now()) S.leases.set(sid, { ...l, t: S.snapshotAt, beat: 0 });
    }
    S.ledgerEvents = (d.events || []).slice(-150).reverse().map(e => ({ e, t: Date.parse(e.ts) || 0 }));
    if (!S.graveyard.length) {
      S.graveyard = (d.events || []).filter(e => e.kind === "released" || e.kind === "dead_end").reverse()
        .map(e => ({ step: e.step, actor: e.actor, reason: e.reason, note: e.note || e.approach, t: Date.parse(e.ts) }));
    }
    $("snapshot-info").textContent = `ledger snapshot ${new Date(S.snapshotAt).toLocaleString()}`
      + (d.commit ? ` (${d.commit.slice(0, 7)})` : "");
    computeLayout();
    panelsDirty = true;
    renderPanels();
  } catch (err) {
    $("snapshot-info").textContent = "snapshot unavailable";
  }
}

function setConn(on, label) {
  $("conn").className = "dot " + (on ? "on" : "off");
  $("conn-label").textContent = label || (on ? "live" : "relay offline · showing the ledger snapshot");
}

function connect() {
  if (!window.EventSource) { setConn(false, "no live updates in this browser"); return; }
  const es = new EventSource(`${RELAY}/stream`);
  es.onopen = () => { S.live = true; setConn(true); panelsDirty = true; };
  es.onmessage = m => { try { apply(JSON.parse(m.data)); } catch (_) { /* ignore malformed */ } };
  es.addEventListener("resync", async () => {
    try {
      const r = await fetch(`${RELAY}/recent?limit=1000`);
      (await r.json()).forEach(apply);
    } catch (_) { /* next reconnect replays */ }
  });
  es.onerror = () => { S.live = S.ticker.length > 0; setConn(false); };
}

legend();
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", legend);
loadSnapshot().then(connect);
setInterval(loadSnapshot, 5 * 60e3);
setInterval(renderPanels, 500);
window.addEventListener("resize", () => { if (!view.moved) view.fitted = false; computeLayout(); });
requestAnimationFrame(draw);
