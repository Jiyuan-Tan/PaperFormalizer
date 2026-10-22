/* PaperFormalizer local UI. Three views — toolkit (#/), library (#/library), paper (#/paper/<slug>) —
   kept current by server-sent events; every fetch carries an ETag, so an unchanged view costs a 304
   and no redraw. Decisions are collected on the page, shown as the exact CLI call, and run on OK. */
(() => {
"use strict";
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const esc = (s) => String(s ?? "").replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);
/* A text written in Unicode mathematics (a promotion entry, a docstring: no TeX) still writes an index
   it has no character for as `x_{i,j}`, `x^{2k}`, `n^(−1/2)`, `V_t`: set those as sub- and
   superscripts. Text in, HTML out; braces nest by repetition; a one-character index counts only on a
   word that is no name with underscores and when no word goes on after it (`S_T`, `Z_j²`; not
   `foo_bar`, not `foo_bar_x`); a link's address is left as written. */
function subsup(s) {
  return String(s ?? "").split(/(https?:\/\/\S+)/).map((part, k) => {
    let t = esc(part); if (k % 2) return t;
    for (let prev = ""; prev !== t;) { prev = t; t = t.replace(/([_^])\{([^{}]*)\}/g, (_, c, body) => (c === "_" ? `<sub>${body}</sub>` : `<sup>${body}</sup>`)); }
    return t.replace(/\^(\((?:[^()]|\([^()]*\))*\))/g, "<sup>$1</sup>")
      .replace(/(?<=[^\s_^])(?:(?<!_[\p{L}\p{N}.']*)(_)|\^)([\p{Ll}\p{Lu}\p{Lo}\p{Nd}])(?![\p{Ll}\p{Lu}\p{Lo}\p{Nd}_])/gu, (_, sub, x) => (sub ? `<sub>${x}</sub>` : `<sup>${x}</sup>`));
  }).join("");
}
const app = $("#app");

/* ── snapshot mode ────────────────────────────────────────────────────────
   The public site's page of a shared paper: this file loaded as `<script src=…/app.js
   data-snapshot="page/page.json">` (`snapshot.html`). There is no server: the paper's views are cut
   from the bundle's snapshot (`page_snapshot.ts`), nothing is posted, nothing of a run at work is
   drawn, and the bundle's files are linked by paths relative to the page. Anyone may share a bundle,
   so its snapshot is untrusted: every HTML string this page inserts passes DOMPurify first. */
const SNAP = (() => {
  const el = document.currentScript, src = el?.dataset.snapshot;
  return src ? { src, viewer: new URL(".", el.src).href, slug: null, share: null, leanDir: null, views: null } : null;
})();
if (SNAP) {
  const purify = window.DOMPurify;
  if (!purify?.sanitize) throw new Error("the page of a shared paper needs DOMPurify");
  const clean = (html) => purify.sanitize(String(html), { ADD_ATTR: ["target"], FORBID_TAGS: ["form", "style"] });
  let inside = false; // (DOMPurify itself may parse through innerHTML)
  // An SVG element's markup is cleaned as SVG (the proof map): read as HTML, DOMPurify drops every SVG element in it.
  const SVG = "http://www.w3.org/2000/svg";
  const cleanSvg = (v) => clean(`<svg xmlns="${SVG}">${v}</svg>`).replace(/^<svg[^>]*>/u, "").replace(/<\/svg>$/u, "");
  const cleaned = (set) => function (v) { if (inside) return set.call(this, v); inside = true; let html; try { html = this?.namespaceURI === SVG ? cleanSvg(v) : clean(v); } finally { inside = false; } return set.call(this, html); };
  for (const name of ["innerHTML", "outerHTML"]) {
    const d = Object.getOwnPropertyDescriptor(Element.prototype, name);
    Object.defineProperty(Element.prototype, name, { ...d, set: cleaned(d.set) });
  }
  const adjacent = Element.prototype.insertAdjacentHTML;
  Element.prototype.insertAdjacentHTML = function (where, html) { return cleaned(function (h) { return adjacent.call(this, where, h); }).call(this, html); };
  document.body.classList.add("snapshot");
  // The bundle's own HTML (the paper, its notes, contents and TeX) is cleaned once more, stricter, as
  // it is read: an id only in the renderer's schemes (`tex_html.ts`: none of the page's own ids
  // has these prefixes, so it cannot stand in for one), no `name`, no `data-copy` (the page's copy
  // button), and no style that lifts it out of the text (a position other than relative or static,
  // a z-index, an inset) — the browser parses the style, so no spelling of one slips through.
  let strictOn = false;
  const probe = document.createElement("span");
  purify.addHook("uponSanitizeAttribute", (_node, data) => {
    if (!strictOn) return;
    if (data.attrName === "name" || data.attrName === "data-copy" || (data.attrName === "id" && !/^(?:env|alg|bib|lbl|sec|res|fig|tab)-/.test(data.attrValue))) { data.keepAttr = false; return; }
    if (data.attrName !== "style") return;
    probe.style.cssText = data.attrValue;
    const lifts = !["", "relative", "static"].includes(probe.style.position) || probe.style.zIndex !== "" || probe.style.inset !== "";
    if (!lifts) return;
    if (!["", "relative", "static"].includes(probe.style.position)) probe.style.removeProperty("position");
    probe.style.removeProperty("z-index");
    probe.style.removeProperty("inset");
    data.attrValue = probe.style.cssText;
  });
  SNAP.strict = (html) => { strictOn = true; try { return purify.sanitize(String(html ?? ""), { ADD_ATTR: ["target"], FORBID_TAGS: ["form", "style"] }); } finally { strictOn = false; } };
}
/** What only a result's drawer shows (`DRAWER_KEYS` of run_model.ts): the snapshot holds it on the result. */
const SNAP_DRAWER = ["review", "paperError", "axioms", "conditions", "rows", "leanView", "linksStale", "linksUnanswered", "leanMissing", "segments", "uncovered", "citedSource"];
/** The snapshot's views as the server answers a finished run's: its page, its drawers, its paper. */
async function snapLoad() {
  const r = await fetch(SNAP.src, { credentials: "same-origin" });
  if (!r.ok) throw new Error(`${SNAP.src}: ${r.status} ${r.statusText}`);
  const s = await r.json();
  if (s?.schema !== 1 || typeof s.slug !== "string" || !Array.isArray(s.results)) throw new Error("its snapshot is of a layout this page does not read");
  SNAP.leanDir = typeof s.leanDir === "string" ? s.leanDir : null;
  if (s.paper && typeof s.paper === "object") {
    s.paper.html = SNAP.strict(s.paper.html);
    for (const c of Array.isArray(s.paper.comments) ? s.paper.comments : []) if (c && typeof c === "object") { c.html = SNAP.strict(c.html); if (c.label != null) c.label = SNAP.strict(c.label); }
    for (const t of Array.isArray(s.paper.toc) ? s.paper.toc : []) if (t && typeof t === "object") t.html = SNAP.strict(t.html);
  }
  s.texHtml = Object.fromEntries(Object.entries(s.texHtml && typeof s.texHtml === "object" ? s.texHtml : {}).map(([k, v]) => [k, SNAP.strict(v)]));
  SNAP.share = await fetch("share.json", { credentials: "same-origin" }).then((x) => (x.ok ? x.json() : null)).catch(() => null);
  const pick = (r, keep) => Object.fromEntries(Object.entries(r).filter(([k]) => SNAP_DRAWER.includes(k) === keep));
  const summary = {
    slug: s.slug, title: String(s.title ?? ""), authors: String(s.authors ?? ""), stage: "", stageIndex: 0, phase: "", live: false, status: "done", headline: "",
    lastEvent: null, pending: { weakening: 0, rewind: false, cap: false, promotion: null, checkpoint: false }, redoing: false,
    verdict: s.verdict ?? null, buckets: s.buckets ?? null, updatedAt: 0, supersededBy: null, orch: null, requests: [], unread: 0, reviews: [], tokens: s.tokens ?? null,
  };
  const texHtml = s.texHtml ?? {};
  return {
    page: { summary, stages: [], halt: null, pending: null, source: { input: null, main: s.main ?? null }, promotion: null, repairs: [], objections: [], messages: [], share: null, texHtml,
      results: s.results.map((r) => ({ ...pick(r, false), review: r.review ? { correctness: r.review.correctness } : null })) },
    drawers: { results: Object.fromEntries(s.results.map((r) => [r.id, pick(r, true)])), leanDefs: s.leanDefs ?? {}, places: s.places ?? {}, texHtml },
    paper: s.paper ? { ...s.paper, from: "corrected_paper", health: null } : null,
  };
}
async function snapApi(url) {
  const v = await SNAP.views;
  const m = /^\/api\/runs\/[^/]+(?:\/(drawers|paper))?$/.exec(url);
  if (!m) throw Object.assign(new Error("this page shows one shared paper"), { answered: true });
  return { data: v[m[1] ?? "page"], changed: false };
}

/* ── data ─────────────────────────────────────────────────────────────── */
const etags = new Map();
const asked = { n: 0 };
async function api(url) {
  if (SNAP) return snapApi(url);
  const hit = etags.get(url), n = ++asked.n;
  const r = await fetch(url, { headers: hit ? { "If-None-Match": hit.etag } : {}, credentials: "same-origin" });
  if (r.status !== 304 && !r.ok) throw Object.assign(new Error((await r.json().catch(() => ({}))).error || `${r.status} ${r.statusText}`), { answered: true });
  const data = r.status === 304 ? null : await r.json();
  // answered after a request made later was: that one holds the newer state, this answer is dropped
  const now = etags.get(url);
  if (now && now.n > n) return { data: now.data, changed: false };
  if (r.status === 304 && now) { now.n = n; return { data: now.data, changed: false }; }
  if (r.status === 304) throw new Error("304 for a view not held");
  etags.set(url, { etag: r.headers.get("ETag") || "", data, n });
  return { data, changed: true };
}
async function post(url, body) {
  if (SNAP) throw new Error("This page of a shared paper is read-only.");
  const r = await fetch(url, { method: "POST", headers: { "Content-Type": "application/json", "X-TC": "1" }, body: JSON.stringify(body), credentials: "same-origin" });
  const data = await r.json().catch(() => ({}));
  if (!r.ok) throw Object.assign(new Error(data.error || `${r.status} ${r.statusText}`), { status: r.status });
  return data;
}
let toastT;
function toast(msg, err = false) {
  let t = $(".toast");
  if (!t) { t = document.createElement("div"); t.className = "toast"; t.setAttribute("role", "status"); document.body.append(t); }
  t.textContent = msg; t.classList.toggle("err", err); t.hidden = false;
  clearTimeout(toastT); toastT = setTimeout(() => { t.hidden = true; }, err ? 7000 : 3500);
}
function copy(text) {
  (navigator.clipboard?.writeText(text) ?? Promise.reject()).then(() => toast("Copied"), () => toast("Copy is blocked here — select the text instead"));
}
document.addEventListener("click", (e) => { const c = e.target.closest("[data-copy]"); if (c) { e.preventDefault(); copy(c.dataset.copy); } });
document.addEventListener("click", (e) => { if (SNAP && e.target.closest("[data-report]")) openReport(); });
/** A token count in a few characters: 940, 12k, 4.0M, 1.2B. */
const tokens = (n) => n >= 1e9 ? `${(n / 1e9).toFixed(1)}B` : n >= 1e6 ? `${(n / 1e6).toFixed(n >= 1e8 ? 0 : 1)}M` : n >= 1e3 ? `${Math.round(n / 1e3)}k` : String(n);
const tokenLine = (t) => t ? `${tokens(t.input)} in (${tokens(t.cached)} cached) · ${tokens(t.output)} out · ${t.calls} calls${t.uncounted ? `, ${t.uncounted} not counted` : ""}` : "";
const ago = (ms) => {
  if (!ms) return "";
  const s = Math.max(0, (Date.now() - ms) / 1000);
  return s < 60 ? "just now" : s < 3600 ? `${Math.round(s / 60)} min ago` : s < 86400 ? `${Math.round(s / 3600)} h ago` : `${Math.round(s / 86400)} d ago`;
};

/* TeX fragments from run records (review detail, readings, conditions, segments): math by KaTeX. */
function tex(s, macros) {
  if (!s) return "";
  // rendered by the server under the paper's macros (KaTeX, else MathJax); this is the fallback
  const done = P.detail?.texHtml?.[s]; if (done !== undefined) return done;
  return typeset(s, macros, texText);
}
/* A text that may write its mathematics either way (Unicode by contract, the owner's own words):
   what stands between `$…$`, `\(…\)`, `\[…\]` is typeset as TeX, the rest goes through `subsup`;
   what stands between backticks is code, shown as written. */
const mixed = (s, macros) => String(s ?? "").split(/`([^`]+)`/).map((part, k) => (k % 2 ? `<code>${esc(part)}</code>` : typeset(part, macros, subsup))).join("");
/** `s` as HTML: its formulas by KaTeX under `macros`, the text between them by `plain`. */
function typeset(s, macros, plain) {
  const out = [];
  const re = /\$\$([\s\S]+?)\$\$|\\\[([\s\S]+?)\\\]|\\\(([\s\S]+?)\\\)|\$((?:\\\$|[^$])+?)\$|\\begin\{(align\*?|equation\*?|gather\*?)\}([\s\S]*?)\\end\{\5\}/g;
  let last = 0, m;
  while ((m = re.exec(s))) {
    out.push(plain(s.slice(last, m.index)));
    const display = m[1] !== undefined || m[2] !== undefined || m[5] !== undefined;
    let body = m[1] ?? m[2] ?? m[3] ?? m[4] ?? `\\begin{aligned}${m[6]}\\end{aligned}`;
    body = body.replace(/\\label\{[^}]*\}/g, "").replace(/\\begin\s*\{array\}\s*\{((?:[^{}]|\{[^{}]*\})*)\}/g, (_, spec) => `\\begin{array}{${spec.replace(/[@!<>]\s*\{[^{}]*\}/g, "")}}`); // KaTeX: no @{…} in an array preamble
    try { out.push(window.katex.renderToString(body, { displayMode: display, throwOnError: false, strict: "ignore", macros: { ...KATEX_GAPS, ...(macros || {}) } })); }
    catch { out.push(`<code>${esc(body)}</code>`); }
    last = re.lastIndex;
  }
  out.push(plain(s.slice(last)));
  return out.join("");
}
// LaTeX commands KaTeX lacks (as in the server's renderer)
const KATEX_GAPS = { "\\xspace": "", "\\Vec": "\\vec{#1}", "\\mbox": "\\text{#1}", "\\hbox": "\\text{#1}", "\\makebox": "\\text{#1}", "\\normalfont": "", "\\offinterlineskip": "", "\\strut": "", "\\mathstrut": "\\vphantom{(}", "\\textsc": "\\text{#1}", "\\protect": "", "\\hfill": "\\quad", "\\mathbbm": "\\mathbb{#1}", "\\mathds": "\\mathbb{#1}" };
/** The number the paper prints for a label (the paper's own numbering), or null when it has none. */
function refNumber(label) {
  const key = label.replace(/&amp;/g, "&");
  return P.paper?.labels?.[key] ?? null;
}
function texText(t) {
  // an index outside a formula is no TeX: Unicode mathematics (`subsup`) — a label is a name, left as written
  return t.split(/(\\(?:eqref|ref|cref|Cref|autoref|cite[pt]?)\{[^{}]*\})/).map((part, k) => (k % 2 ? esc(part) : subsup(part))).join("")
    .replace(/\\(?:emph|textit)\{([^{}]*)\}/g, "<em>$1</em>").replace(/\\textbf\{([^{}]*)\}/g, "<strong>$1</strong>")
    .replace(/\\(eqref|ref|cref|Cref|autoref)\{([^{}]*)\}/g, (_, cmd, label) => { const n = refNumber(label); const named = ["cref", "Cref", "autoref"].includes(cmd) ? P.paper?.envs?.find((e) => e.label === label)?.heading : null; return n === null ? `<span class="cite">${label}</span>` : cmd === "eqref" ? `(${esc(n)})` : esc(named ?? n); })
    .replace(/\\cite[pt]?\{([^{}]*)\}/g, "[$1]").replace(/``/g, "“").replace(/''/g, "”").replace(/~/g, "&nbsp;").replace(/\\\\/g, "<br>");
}

/* ── router + live updates ────────────────────────────────────────────── */
const S = { view: "", slug: null, toolkit: null };
function parseRoute() {
  if (SNAP) return { view: "paper", slug: SNAP.slug };
  const h =location.hash.replace(/^#/, "") || "/";
  const m = /^\/paper\/([^/?#]+)/.exec(h);
  if (m) return { view: "paper", slug: decodeURIComponent(m[1]) };
  if (h.startsWith("/library")) return { view: "library", slug: null };
  return { view: "toolkit", slug: null };
}
async function route() {
  const r = parseRoute();
  const switching = r.view !== S.view || r.slug !== S.slug;
  S.view = r.view; S.slug = r.slug;
  $$(".nav a").forEach((a) => a.removeAttribute("aria-current"));
  const cur = $(`.nav a[data-nav="${r.view}"]`); if (cur) cur.setAttribute("aria-current", "page");
  if (switching) { closeDrawer(); keepBody(); window.scrollTo(0, 0); app.innerHTML = `<p class="loading">Loading…</p>`; P.built = null; }
  try {
    if (r.view === "toolkit") await showToolkit(switching);
    else if (r.view === "library") await showLibrary(switching);
    else await showPaper(r.slug, switching);
  } catch (err) { app.innerHTML = `<div class="page"><p class="empty-note">Could not load this view: ${esc(err.message)}</p></div>`; }
}
window.addEventListener("hashchange", route);

let pending = new Set(), flushT = null;
function onChange(scope) {
  pending.add(scope);
  clearTimeout(flushT);
  flushT = setTimeout(async () => {
    const scopes = pending; pending = new Set();
    try {
      if (scopes.has("demo")) await refreshTour();
      if ([...scopes].some((s) => s === "toolkit" || s.startsWith("run:"))) await refreshInbox();
      if (S.view === "toolkit" && [...scopes].some((s) => s === "toolkit" || s.startsWith("run:"))) await showToolkit(false);
      if (S.view === "library" && scopes.has("library")) await showLibrary(false);
      if (S.view === "paper" && scopes.has(`run:${S.slug}`)) await showPaper(S.slug, false);
      C.failed = false; drawConn();
    } catch (err) {
      console.warn(err);
      if (err.answered) return;
      // the server did not answer: what the page shows is no longer known to be current, and what
      // was asked is asked again with the next round (`wake`)
      C.failed = true; drawConn();
      for (const s of scopes) pending.add(s);
    }
  }, 250);
}
/** Ask again for everything on screen: what was pushed while this tab could not hear is lost. */
function refetch() { onChange("toolkit"); onChange("library"); if (S.slug) onChange(`run:${S.slug}`); }

/* The connection to the server: `open` once its hello came, `failed` when a fetch did not get through,
   `outdated` when the page's files on disk are no longer the ones this tab runs. While it is known
   not to stand, the page says that what it shows is the last state received — not the run's. */
const C = { es: null, open: null, failed: false, outdated: false, boot: null, assets: null, quietT: null };
const connState = (c) => (c.open === false || c.failed ? "lost" : c.outdated ? "outdated" : "live");
function drawConn() {
  const state = connState(C), c = $("#conn");
  document.body.classList.toggle("stale", state === "lost");
  c.classList.toggle("off", state !== "live");
  c.textContent = state === "live" ? "● live" : state === "lost" ? "○ connection lost — this is the last state received" : "↻ this page was updated — click to reload";
  c.onclick = state === "outdated" ? () => location.reload() : null;
}
const PING_MS = 10_000;
function connect() {
  if (!window.EventSource) { $("#conn").textContent = "○ no live updates"; return; }
  C.es?.close();
  const es = C.es = new EventSource("/api/events");
  // the server pings: three missed, and the connection is one that died without saying so (a laptop
  // that slept, a tunnel that dropped) — the browser would wait on it for ever
  const heard = () => { clearTimeout(C.quietT); C.quietT = setTimeout(() => { C.open = false; drawConn(); connect(); }, 3 * PING_MS + 5000); };
  const files = (now) => { if (!now) return; if (C.assets !== null && now !== C.assets) C.outdated = true; else C.assets = now; };
  es.addEventListener("hello", (e) => {
    let d = {}; try { d = JSON.parse(e.data); } catch { /* an older server */ }
    // reconnected to a UI started anew: its page code may be newer than this tab's — load it
    if (C.boot !== null && d.boot != null && d.boot !== C.boot) { location.reload(); return; }
    C.boot = d.boot ?? null;
    files(d.assets);
    if (d.assets) heard(); // (a server that sends no pings is not held to them)
    // after a reconnect (sleep, server restart) changes made meanwhile were never pushed: refetch
    if (C.open !== null) refetch();
    C.open = true; drawConn();
  });
  es.addEventListener("ping", (e) => { heard(); try { files(JSON.parse(e.data).assets); } catch { /* ignore */ } drawConn(); });
  es.addEventListener("change", (e) => { try { onChange(JSON.parse(e.data).scope); } catch { /* ignore */ } });
  es.onerror = () => { C.open = false; drawConn(); };
}
/** The tab is looked at again (it may have slept, its timers and its connection with it): ask anew. */
function wake() {
  if (document.hidden) return;
  if (C.es && C.es.readyState === 2) connect(); // closed for good (the server refused it): try again
  refetch();
  if (TOUR.on) refreshTour();
}

/* ── inbox ────────────────────────────────────────────────────────────── */
async function refreshInbox() {
  const { data } = await api("/api/toolkit");
  S.toolkit = data;
  const items = data.runs.filter((r) => r.status === "needs-you" || r.requests?.length);
  const c = $("#inbox-count"); c.textContent = items.length; c.classList.toggle("zero", !items.length);
  // the tab says how many papers wait; what is new since the last look is notified, when asked for —
  // never what stood there when the page loaded
  document.title = `${items.length ? `(${items.length}) ` : ""}PaperFormalizer`;
  // (a message of the agent's waits for no decision: announced as a message, counted nowhere here)
  const now = new Map([...items.flatMap((r) => needsOf(r).map(([k, what]) => [`${r.slug}|${k}`, { r, title: r.title, what }])), ...data.runs.filter((r) => r.unread).map((r) => [`${r.slug}|message ${r.unread}`, { r, title: "PaperFormalizer", what: `The agent replied on ${r.title}` }])]);
  if (NOTE.seen && notifyOn()) {
    for (const [k, { r, title, what }] of now) {
      if (NOTE.seen.has(k)) continue;
      try { const n = new window.Notification(title, { body: what, tag: k }); n.onclick = () => { window.focus(); location.hash = `#/paper/${encodeURIComponent(r.slug)}`; n.close(); }; } catch { /* the browser refuses: the tab's count stands */ }
    }
  }
  NOTE.seen = new Set(now.keys());
  $("#inbox-list").innerHTML = items.length
    ? items.map((r) => `<a class="inbox-item" href="#/paper/${encodeURIComponent(r.slug)}">${esc(r.title)}<small>${esc(r.slug)} · ${tex(r.headline)}</small></a>`).join("")
    : `<div class="inbox-empty">Nothing is waiting for you.</div>`;
}
/* Desktop notifications: one per new thing that waits for the owner. On unless turned off with the
   header's button (remembered in this browser); the browser is asked for its permission when the
   page opens, and again at the first click when it answers only to one. */
const NOTE = { seen: null };
/** What a paper of the inbox waits for, each by a key that changes when it is another one. */
function needsOf(r) {
  const out = [];
  if (r.pending?.weakening) out.push(["repair", "A revision that would weaken a result waits for your decision."]);
  if (r.pending?.promotion && r.status === "needs-you") out.push([`promotion ${r.pending.promotion}`, "Results proposed for your toolkit wait for your decision."]);
  for (const q of r.requests ?? []) out.push([`request ${q.id}`, "The agent asks you something."]);
  if (!out.length) out.push(["needs", r.headline]);
  return out;
}
const threadHidden = () => { try { return window.localStorage.getItem("tc-thread") === "hidden"; } catch { return false; } };
const setThreadHidden = (on) => { try { window.localStorage.setItem("tc-thread", on ? "hidden" : "shown"); } catch { /* shown, then */ } };
const notifyWanted = () => { try { return window.localStorage.getItem("tc-notify") !== "0"; } catch { return true; } };
const notifyOn = () => { try { return notifyWanted() && window.Notification.permission === "granted"; } catch { return false; } };
if (!SNAP && window.Notification && window.isSecureContext) {
  const b = $("#notify-btn"), draw = () => { b.textContent = notifyOn() ? "Notifying — turn off" : "Notify me"; b.setAttribute("aria-pressed", String(notifyOn())); };
  b.hidden = false; draw();
  const ask = async () => { if (notifyWanted() && window.Notification.permission === "default") { try { await window.Notification.requestPermission(); } catch { /* asked again at a click */ } draw(); } };
  ask();
  document.addEventListener("click", (e) => { if (!e.target.closest("#notify-btn")) ask(); }, { once: true });
  b.addEventListener("click", async () => {
    const on = !notifyOn();
    if (on && (await window.Notification.requestPermission()) !== "granted") { toast("The browser blocks notifications for this page.", true); return; }
    try { window.localStorage.setItem("tc-notify", on ? "1" : "0"); } catch { toast("This browser keeps no settings for the page.", true); }
    draw();
  });
}
const showInbox = (on) => { $("#inbox-pop").hidden = !on; $("#inbox-btn").setAttribute("aria-expanded", String(on)); };
$("#inbox-btn").addEventListener("click", () => showInbox($("#inbox-pop").hidden));
document.addEventListener("click", (e) => { if (!e.target.closest(".inbox-wrap")) showInbox(false); });

/* ── modal confirm ────────────────────────────────────────────────────── */
function confirmRun(title, html, okLabel = "Continue") {
  return new Promise((resolve) => {
    const m = $("#modal");
    $("#modal-title").textContent = title; $("#modal-body").innerHTML = html; $("#modal-ok").textContent = okLabel;
    m.hidden = false; $("#modal-ok").focus();
    const done = (v) => { m.hidden = true; $("#modal-ok").onclick = null; $("#modal-cancel").onclick = null; resolve(v); };
    $("#modal-ok").onclick = () => done(true);
    $("#modal-cancel").onclick = () => done(false);
    m.onkeydown = (e) => { if (e.key === "Escape") { e.stopPropagation(); done(false); } }; // the dialog only: not the drawer under it
  });
}
const cmdBox = (c) => `<div class="cmd"><code>${esc(c)}</code><button type="button" data-copy="${esc(c)}">copy</button></div>`;

/* ═════════════ TOOLKIT VIEW ═════════════ */
const T = { q: "", f: "all", page: 0, size: 8 };
const STATUS_WORD = { "needs-you": "needs you", running: "running", agent: "with the agent", done: "done", idle: "idle", superseded: "superseded" };
async function showToolkit(first) {
  const { data, changed } = await api("/api/toolkit");
  S.toolkit = data;
  if (S.view !== "toolkit") return; // the reader moved on while this was fetched
  if (!first && !changed && $("#tk-page")) return;
  const scroll = window.scrollY;
  const focusId = document.activeElement?.id;
  const runs = data.runs;
  const count = (s) => runs.filter((r) => r.status === s).length;
  if (!$("#tk-page")) {
    app.innerHTML = `<div class="page" id="tk-page">
      <div class="head"><div><div class="kicker">Papers</div><h1 id="tk-name"></h1><div class="meta" id="tk-meta"></div></div><div class="stats" id="tk-stats"></div></div>
      <section class="sec"><h2>Waiting for you <span class="sub" id="wait-sub"></span></h2><div class="waiting" id="waiting"></div></section>
      <section class="sec"><h2>Papers <span class="sub">one verify run per paper · live</span></h2>
        <div class="tools"><label class="sr" for="runs-q">Search papers</label><input id="runs-q" type="search" placeholder="Search title, author or run name" autocomplete="off"><span class="seg" id="runs-filter" role="group" aria-label="Filter"></span></div>
        <div class="tbl-wrap"><table class="runs"><colgroup><col class="c-paper"><col class="c-prog"><col class="c-st"><col class="c-up"><col class="c-sh"></colgroup><thead><tr><th>Paper</th><th>Progress</th><th>Status</th><th>Updated</th><th>Share</th></tr></thead><tbody id="runs-body"></tbody></table></div>
        <div class="pager" id="runs-pager"></div></section>
      <section class="sec"><h2>Verify a paper <span class="sub">an agent session runs it; this page follows it</span></h2><div id="start-how"></div></section>
    </div>`;
    $("#runs-q").value = T.q;
    const search = (e) => { T.q = e.target.value.trim(); T.page = 0; drawRuns(); };
    $("#runs-q").addEventListener("input", search);
    $("#runs-q").addEventListener("search", search);
    $("#runs-filter").addEventListener("click", (e) => { const b = e.target.closest("[data-f]"); if (b) { T.f = b.dataset.f; T.page = 0; drawRuns(); } });
    $("#runs-pager").addEventListener("click", (e) => { const b = e.target.closest("[data-pg]"); if (b && !b.disabled) { T.page = +b.dataset.pg; drawRuns(); } });
    $("#runs-body").addEventListener("click", (e) => {
      // the share cell acts on its own: its button shares that row's paper, its links open elsewhere
      const sb = e.target.closest("[data-share]"); if (sb) { if (!sb.disabled) shareRun(sb.dataset.share); return; }
      if (e.target.closest(".sh a")) return;
      const tr = e.target.closest("tr[data-slug]"); if (tr) location.hash = `#/paper/${encodeURIComponent(tr.dataset.slug)}`;
    });
    $("#runs-body").addEventListener("keydown", (e) => { const tr = e.target.closest("tr[data-slug]"); if (tr && e.key === "Enter" && !e.target.closest(".sh")) location.hash = `#/paper/${encodeURIComponent(tr.dataset.slug)}`; });
  }
  $("#tk-name").textContent = `Papers in ${data.toolkit.name}`;
  $("#start-how").innerHTML = `<p class="meta">Open a terminal in <code>${esc(data.toolkit.repo)}</code>, start <code>claude</code> or <code>codex</code>, and ask it, for example:</p>${cmdBox(`Use PaperFormalizer to verify the paper at <path to the .tex, folder or arXiv id> (toolkit ${data.toolkit.root}).`)}<p class="meta">The agent starts the run, attaches itself to it and acts at every halt; the run appears here and updates live. Decisions that are yours wait for you on the paper's page.</p>`;
  $("#tk-meta").innerHTML = `<span>Owner ${esc(data.toolkit.owner)}</span><span>Lean <code>${esc(data.toolkit.lean.replace(/^.*:/, ""))}</code></span><span>Base: ${esc(data.toolkit.base.join(", ") || "Mathlib")}</span><span><code>${esc(data.toolkit.root)}</code></span>`;
  $("#tk-stats").innerHTML = [["papers", runs.length], ["need you", count("needs-you")], ["running", count("running")], ["done", count("done")]].map(([k, v]) => `<div class="stat"><b>${v}</b><span>${k}</span></div>`).join("");
  const waiting = runs.filter((r) => r.status === "needs-you");
  $("#wait-sub").textContent = waiting.length ? `${waiting.length} open` : "nothing open";
  $("#waiting").innerHTML = waiting.length
    ? waiting.map((r) => `<div class="wcard"><span class="kicker">${esc(r.slug)}</span><h3>${tex(r.headline)}</h3><p>${esc(r.title)}</p><div><a class="btn btn-primary" href="#/paper/${encodeURIComponent(r.slug)}" style="border:none">Open the paper</a></div></div>`).join("")
    : `<div class="wcard ok"><h3>Nothing is waiting for you</h3><p>${count("running") ? `${count("running")} run(s) in progress; a halt will appear here.` : "Ask an agent session to verify a paper (below), or open a finished one."}</p></div>`;
  drawRuns();
  window.scrollTo(0, scroll);
  if (focusId && $(`#${focusId}`)) $(`#${focusId}`).focus();
}
function drawRuns() {
  const runs = S.toolkit?.runs ?? [];
  const cats = { all: "All", "needs-you": "Needs you", running: "Running", agent: "With the agent", done: "Done", idle: "Idle" };
  const n = (c) => runs.filter((r) => c === "all" || r.status === c).length;
  $("#runs-filter").innerHTML = Object.entries(cats).map(([k, v]) => `<button type="button" data-f="${k}" aria-pressed="${T.f === k}">${v} ${n(k)}</button>`).join("");
  const q = T.q.toLowerCase();
  const rows = runs.filter((r) => (T.f === "all" || r.status === T.f) && (!q || `${r.title} ${r.slug} ${r.authors}`.toLowerCase().includes(q)));
  const pages = Math.max(1, Math.ceil(rows.length / T.size));
  T.page = Math.min(T.page, pages - 1);
  const shown = rows.slice(T.page * T.size, T.page * T.size + T.size);
  const STAGES = 11;
  $("#runs-body").innerHTML = shown.length ? shown.map((r) => {
    const dots = Array.from({ length: STAGES }, (_, i) => `<span class="stg ${i <= r.stageIndex ? "done" : i === r.stageIndex + 1 ? (r.live || r.status === "running" ? "current" : r.status === "needs-you" || r.status === "agent" ? "halt" : "") : ""}"></span>`).join("");
    const pill = r.live || r.status === "running" ? `<span class="pill b-running"><span class="dot-live"></span>running</span>` : `<span class="pill b-${r.status}">${STATUS_WORD[r.status]}</span>`;
    return `<tr class="row" data-slug="${esc(r.slug)}" tabindex="0"><td class="t">${esc(r.title)}${r.unread ? ` <span class="msg-new" title="The agent wrote on this paper's page">● ${r.unread} new message${r.unread > 1 ? "s" : ""}</span>` : ""}<small>${esc(r.slug)}${r.authors ? ` · ${esc(r.authors)}` : ""}</small></td>
      <td><div class="stages" title="${esc(r.stage)}">${dots}</div></td><td class="st">${pill}<small title="${esc(r.headline)}">${tex(r.headline)}</small></td><td class="mono" style="white-space:nowrap;color:var(--ink-faint)">${ago(r.updatedAt)}${r.tokens ? `<small title="${esc(tokenLine(r.tokens))}">${esc(tokens(r.tokens.input))} in · ${esc(tokens(r.tokens.output))} out</small>` : ""}</td><td class="sh">${shareCellHTML(r)}</td></tr>`;
  }).join("") : `<tr><td colspan="5" class="none" style="text-align:center;padding:1.2rem">No paper matches.</td></tr>`;
  const from = rows.length ? T.page * T.size + 1 : 0;
  $("#runs-pager").innerHTML = `<span class="info">${from}–${T.page * T.size + shown.length} of ${rows.length}</span><button type="button" data-pg="${T.page - 1}" ${T.page === 0 ? "disabled" : ""} aria-label="Previous page">‹</button>${Array.from({ length: pages }, (_, i) => `<button type="button" data-pg="${i}" ${i === T.page ? 'aria-current="page"' : ""}>${i + 1}</button>`).join("")}<button type="button" data-pg="${T.page + 1}" ${T.page >= pages - 1 ? "disabled" : ""} aria-label="Next page">›</button>`;
}

/* ═════════════ LIBRARY VIEW ═════════════ */
const LS = { q: "", div: "all", paper: "", mod: null };
let LIB = null, BYLEAF = new Map();
async function showLibrary(first) {
  const { data, changed } = await api("/api/library");
  if (S.view !== "library") return;
  if (!first && !changed) return;
  LIB = data;
  BYLEAF = new Map(data.modules.flatMap((m) => m.decls.map((d) => [d.leaf, { ...d, mod: m }])));
  if (!$("#lib-page")) {
    app.innerHTML = `<div class="page" id="lib-page">
      <div class="head"><div><div class="kicker">Library</div><h1>Toolkit library</h1><p class="meta" style="max-width:62ch">The proved Lean results your papers build on, read from the Lean sources (always current). Each declaration shows its docstring first, then the statement line by line; hover a phrase or a row to see its partner.</p></div><div class="stats" id="lib-stats"></div></div>
      <div class="tools" style="margin-top:1.2rem"><label class="sr" for="lib-q">Search</label><input id="lib-q" type="search" placeholder="Search names and docstrings" autocomplete="off">
        <span class="seg" id="lib-div" role="group" aria-label="Division"></span><label class="sr" for="lib-paper">Used in paper</label><select id="lib-paper"></select></div>
      <div class="lib-grid"><nav class="lib-nav" id="lib-nav" aria-label="Modules"></nav><div class="lib-main" id="lib-main"></div></div></div>`;
    $("#lib-q").addEventListener("input", (e) => { LS.q = e.target.value.trim(); drawLib(); });
    $("#lib-div").addEventListener("click", (e) => { const b = e.target.closest("[data-div]"); if (b) { LS.div = b.dataset.div; drawLib(); } });
    $("#lib-paper").addEventListener("change", (e) => { LS.paper = e.target.value; drawLib(); });
    $("#lib-page").addEventListener("click", (e) => {
      const m = e.target.closest("[data-lmod]"); if (m) { LS.mod = m.dataset.lmod || null; LS.q = ""; $("#lib-q").value = ""; drawLib(); window.scrollTo(0, 0); return; }
      const d = e.target.closest("[data-ldecl]"); if (d && BYLEAF.has(d.dataset.ldecl)) { LS.mod = BYLEAF.get(d.dataset.ldecl).mod.path; LS.q = ""; $("#lib-q").value = ""; drawLib(); const el = document.getElementById(`d-${d.dataset.ldecl}`); if (el) { el.scrollIntoView({ block: "start", behavior: "smooth" }); el.classList.add("flash"); setTimeout(() => el.classList.remove("flash"), 1300); } }
    });
  }
  const divs = ["all", ...new Set(data.modules.map((m) => m.path.split("/")[0]))];
  $("#lib-div").innerHTML = divs.map((d) => `<button type="button" data-div="${esc(d)}" aria-pressed="${LS.div === d}">${d === "all" ? "All" : esc(d)}</button>`).join("");
  $("#lib-paper").innerHTML = `<option value="">Used in any paper or none</option>` + data.papers.map((p) => `<option value="${esc(p)}" ${LS.paper === p ? "selected" : ""}>Used in ${esc(p)}</option>`).join("");
  drawLib();
}
const passes = (d, mod) => (LS.div === "all" || mod.path.startsWith(LS.div)) && (!LS.paper || d.papers.includes(LS.paper));
function drawLib() {
  const all = LIB.modules.flatMap((m) => m.decls.map((d) => ({ d, m })));
  $$("#lib-div button").forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.div === LS.div)));
  const papersUsing = new Set(all.flatMap(({ d }) => d.papers)).size;
  $("#lib-stats").innerHTML = [["declarations", all.length], ["modules", LIB.modules.length], ["linked docstrings", LIB.linked], [`of ${LIB.papers.length} papers use it`, papersUsing]].map(([k, v]) => `<div class="stat"><b>${v}</b><span>${k}</span></div>`).join("");
  // nav
  const groups = {};
  for (const m of LIB.modules) { const s = m.path.split("/"); ((groups[s[0]] ??= {})[s.length > 2 ? s[1] : ""] ??= []).push(m); }
  let h = `<button type="button" data-lmod="" aria-current="${!LS.mod && !LS.q}">Overview<span class="c">${all.filter(({ d, m }) => passes(d, m)).length}</span></button>`;
  for (const [div, areas] of Object.entries(groups)) {
    h += `<div class="grp">${esc(div)}</div>`;
    for (const [area, ms] of Object.entries(areas)) {
      if (area) h += `<div class="area">${esc(area)}</div>`;
      h += ms.map((m) => { const n = m.decls.filter((d) => passes(d, m)).length; return `<button type="button" data-lmod="${esc(m.path)}" aria-current="${LS.mod === m.path}" class="${n ? "" : "dim"}" title="${esc(m.title)}">${esc(m.path.split("/").pop())}<span class="c">${n}</span></button>`; }).join("");
    }
  }
  $("#lib-nav").innerHTML = h;
  const main = $("#lib-main");
  const q = LS.q.toLowerCase();
  if (q) {
    const hits = all.filter(({ d, m }) => passes(d, m) && `${d.leaf} ${d.doc}`.toLowerCase().includes(q));
    main.innerHTML = `<h2>${hits.length} declaration(s) match “${esc(LS.q)}”</h2>` + (hits.length ? hits.map(({ d, m }) => declCard(d, m, true)).join("") : `<p class="empty-note">Nothing matches. Try a word from a docstring.</p>`);
  } else if (LS.mod) {
    const m = LIB.modules.find((x) => x.path === LS.mod);
    if (!m) { LS.mod = null; return drawLib(); }
    const ds = m.decls.filter((d) => passes(d, m));
    main.innerHTML = `<div class="crumbs"><button type="button" data-lmod="">Library</button>${m.path.split("/").map((s) => `<span>/</span><span>${esc(s)}</span>`).join("")}</div>
      <h1 class="mod-title">${mixed(m.title || m.path.split("/").pop())}</h1>${m.summary ? `<p class="mod-sum">${mixed(m.summary)}</p>` : ""}<div class="mod-path">${esc(m.module)} · ${m.decls.length} declarations</div>
      ${ds.length ? ds.map((d) => declCard(d, m, false)).join("") : `<p class="empty-note">No declaration here passes the filter.</p>`}`;
  } else {
    const mods = LIB.modules.filter((m) => m.decls.some((d) => passes(d, m)));
    main.innerHTML = `<h2>Modules</h2><table class="mtable"><thead><tr><th>Module</th><th class="n">Decls</th><th class="n">Papers</th></tr></thead><tbody>${mods.map((m) => `<tr data-lmod="${esc(m.path)}"><td>${mixed(m.title || m.path)}<small>${esc(m.module)}</small></td><td class="n">${m.decls.length}</td><td class="n">${new Set(m.decls.flatMap((d) => d.papers)).size}</td></tr>`).join("")}</tbody></table>`;
  }
}
/* A docstring: its mathematics and its code as `mixed` has them, each linked phrase a span naming its rows. */
function nlHTML(doc) {
  const out = []; let last = 0;
  for (const m of doc.matchAll(/\[([^\]]+)\]\((hyp:([^)]*)|goal|step:(\d+))\)/g)) {
    const [, t, all, hs, n] = m;
    out.push(mixed(doc.slice(last, m.index)), `<span class="xl" data-xl="${esc(all === "goal" ? "⊢" : n ? `⊢${n}` : hs.split(",").map((x) => x.trim()).join(" "))}">${mixed(t)}</span>`);
    last = m.index + m[0].length;
  }
  return out.join("") + mixed(doc.slice(last));
}
function phrasesFor(doc, names) {
  const want = names.split(/\s+/).filter(Boolean); const out = [];
  for (const m of doc.matchAll(/\[([^\]]+)\]\((hyp:([^)]*)|goal)\)/g)) { const hs = m[2] === "goal" ? ["⊢"] : m[3].split(",").map((x) => x.trim()); if (hs.some((h) => want.includes(h))) out.push(m[1]); }
  return [...new Set(out)];
}
function parseSig(sig) {
  const open = { "(": ")", "{": "}", "[": "]", "⦃": "⦄" }; const rows = []; let i = 0;
  const skip = () => { while (sig[i] === " ") i++; };
  skip();
  while (i < sig.length && open[sig[i]]) {
    const o = sig[i], c = open[o]; let d = 0, j = i;
    for (; j < sig.length; j++) { if (sig[j] === o) d++; else if (sig[j] === c && --d === 0) break; }
    if (j >= sig.length) return null;
    const inner = sig.slice(i + 1, j); let depth = 0, cut = -1;
    for (let k = 0; k < inner.length; k++) { const ch = inner[k]; if ("([{⦃".includes(ch)) depth++; else if (")]}⦄".includes(ch)) depth--; else if (ch === ":" && depth === 0 && inner[k + 1] !== "=") { cut = k; break; } }
    rows.push({ names: cut >= 0 && o !== "[" ? inner.slice(0, cut).trim() : "", type: cut >= 0 && o !== "[" ? inner.slice(cut + 1).trim() : inner.trim(), side: o !== "(", raw: sig.slice(i, j + 1) });
    i = j + 1; skip();
  }
  if (sig[i] !== ":") return rows.length ? { rows, concl: "" } : null;
  return { rows, concl: sig.slice(i + 1).trim() };
}
function stmtHTML(d) {
  const p = parseSig(d.sig);
  if (!p) return `<pre class="st" style="margin:0.4rem 0">${esc(d.sig)}</pre>`;
  const thm = d.kind === "theorem";
  const isHyp = (r) => /^h/.test(r.names) || /[≤<=≠→∀∃]|Tendsto|PosDef|PosSemidef/.test(r.type);
  const row = (r) => { const ph = r.names ? phrasesFor(d.doc, r.names) : []; return `<div class="srow ${r.side ? "side" : isHyp(r) ? "hyp" : ""}" data-binder="${esc(r.names)}"><div class="sl">${r.names ? `<span class="sn">${esc(r.names)}</span><span class="sc">:</span><span class="st">${esc(r.type)}</span>` : `<span class="st">${esc(r.raw)}</span>`}</div>${ph.length ? `<div class="sdoc">${ph.map((x) => mixed(x)).join(" · ")}</div>` : ""}</div>`; };
  const gph = phrasesFor(d.doc, "⊢");
  return `<div class="stmt">${p.rows.length ? `<div class="stmt-lbl">${thm ? "hypotheses" : "parameters"}</div>${p.rows.map(row).join("")}` : ""}${p.concl ? `<div class="stmt-lbl">${thm ? "conclusion" : "type"}</div><div class="srow concl" data-binder="⊢"><div class="sl"><span class="st">${esc(p.concl)}</span></div>${gph.length ? `<div class="sdoc">${gph.map((x) => mixed(x)).join(" · ")}</div>` : ""}</div>` : ""}</div>${thm && !/\]\((hyp:|goal)/.test(d.doc) ? `<p class="stmt-note">This docstring does not link its phrases to the hypotheses yet.</p>` : ""}`;
}
function declCard(d, m, showMod) {
  const refs = (xs) => xs.length ? xs.map((x) => `<button type="button" class="ref-chip" data-ldecl="${esc(x)}">${esc(x)}</button>`).join("") : `<span class="none">none</span>`;
  const generic = /^(Given|Under|For) \[the (stated|supplied)/.test(d.doc);
  return `<div class="dcard xlscope" id="d-${esc(d.leaf)}"><div class="dhead2"><span class="dkind ${esc(d.kind)}">${esc(d.kind)}</span><span class="dname">${esc(d.leaf)}</span>${generic ? `<span class="generic">generic docstring</span>` : ""}</div>
    ${showMod ? `<div class="dmodline">${esc(m.module)}</div>` : ""}<div class="ddoc">${d.doc ? nlHTML(d.doc) : `<span class="none">No docstring.</span>`}</div>${stmtHTML(d)}
    <dl class="dmeta"><dt>uses</dt><dd>${refs(d.uses)}</dd><dt>used by</dt><dd>${refs(d.usedBy)}</dd><dt>papers</dt><dd>${d.papers.length ? d.papers.map((p) => `<span class="pp">${esc(p)}</span>`).join("") : `<span class="none">none yet</span>`}</dd></dl></div>`;
}
// phrase ↔ row hover, in the card / drawer it belongs to
function xlNames(el) { return (el.dataset.xl ?? el.dataset.binder ?? "").split(/\s+/).filter(Boolean); }
let xlLast = null, xlPinned = null;

/* ── Lean ↔ the paper's own text ──────────────────────────────────────────
   The phrases of the open result (`segments`, cut from its statement) are found in its statement
   on the page by their text, and painted with the CSS highlight API: nothing in the paper's DOM is
   changed, so a phrase may run across formulas and list items. The phrases a row states light up
   on hover; nothing marks them at rest.
   `whole`: the parts of a displayed formula that are not found by themselves (a row of an aligned
   display is not one run of text) and light their formula whole. */
const XLP = { ranges: new Map(), whole: new Set(), root: null };
const xlCanPaint = () => typeof Highlight === "function" && Boolean(CSS.highlights);
/** The visible characters of `root` without white space, each with its text node and offset. */
function xlChars(root) {
  const chars = []; let str = "";
  const walk = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, { acceptNode: (n) => (n.parentElement?.closest(".rv-tag, .env, .eqn, .katex-mathml, .cmark, .rv.del, .fbadge, .rv-proofonly") ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT) });
  for (let n = walk.nextNode(); n; n = walk.nextNode()) {
    const t = n.nodeValue;
    for (let i = 0; i < t.length; i++) if (!/\s/.test(t[i])) { chars.push([n, i]); str += t[i]; }
  }
  return { chars, str };
}
/** The visible characters of the TeX `text` as the page renders it, without white space. */
function xlWant(text) {
  const probe = document.createElement("div");
  probe.innerHTML = tex(text, P.paper?.macros);
  // an equation's number is the page's own count, not the phrase's
  probe.querySelectorAll(".katex-mathml, .eqn").forEach((x) => x.remove());
  return probe.textContent.replace(/\s+/g, "");
}
/** Where `want` stands in the first of `scopes` that has it (each: its characters `str`, and `from`,
    where its last hit ended) — from there on, else anywhere: [scope, index], or null. A phrase of
    fewer than two characters stands in too many places to be found. */
function xlAt(scopes, want) {
  if (want.length < 2) return null;
  for (const s of scopes) {
    let at = s.str.indexOf(want, s.from);
    if (at < 0) at = s.str.indexOf(want);
    if (at >= 0) { s.from = at + want.length; return [s, at]; }
  }
  return null;
}
/** The range of the TeX `text` in the first of `scopes` (`xlChars`, with `from`) that has it, or null. */
function xlFind(scopes, text) {
  const want = xlWant(text), hit = xlAt(scopes, want);
  if (!hit) return null;
  const [n0, o0] = hit[0].chars[hit[1]], [n1, o1] = hit[0].chars[hit[1] + want.length - 1];
  const range = document.createRange(); range.setStart(n0, o0); range.setEnd(n1, o1 + 1);
  return range;
}
/** Find the phrases `segments` in the block `root` of the page and underline them; returns how many were found. */
function xlLocate(root, segments) {
  if (!root?.matches(".formal") || !xlCanPaint() || !segments?.length) return 0;
  // a repaired statement is read in its corrected text first, then in the whole block: a phrase the
  // repair left alone stands outside the corrected text (struck-out text is never searched)
  const scopes = [...[...root.querySelectorAll(":scope .rv.ins")].filter((b) => !b.classList.contains("pending")), root].map((el) => ({ ...xlChars(el), from: 0 }));
  // a part of a displayed formula is looked for as the formula it is by itself (`alone`)
  for (const seg of segments) { const range = xlFind(scopes, seg.alone?.text ?? seg.text); if (range) XLP.ranges.set(seg.id, range); }
  // … and one not found so lights the formula whole
  for (const first of segments) {
    const parts = first.whole ? segments.filter((s) => s.display === first.id && !XLP.ranges.has(s.id)) : [];
    const range = parts.length ? xlFind(scopes.map((s) => ({ ...s, from: 0 })), first.whole.text) : null;
    if (range) for (const p of parts) { XLP.ranges.set(p.id, range); XLP.whole.add(p.id); }
  }
  // a folded definition of the setting that holds a phrase is opened: a phrase lights only where it is drawn
  for (const f of root.querySelectorAll("details.rv-fold:not([open])")) if ([...XLP.ranges.values()].some((x) => x.intersectsNode(f))) f.open = true;
  XLP.root = root; root.classList.add("xl-on");
  for (const f of root.querySelectorAll(".katex, mjx-container")) if ([...XLP.ranges.values()].some((x) => x.intersectsNode(f))) f.classList.add("xl-has");
  return XLP.ranges.size;
}
/** The part of formula `f` the phrase `r` covers when it starts or ends inside it; null when it takes the formula whole. */
function xlInside(r, f) {
  const { chars } = xlChars(f); if (!chars.length) return null;
  const whole = document.createRange(); whole.setStart(...chars[0]); whole.setEnd(chars.at(-1)[0], chars.at(-1)[1] + 1);
  const startsIn = r.compareBoundaryPoints(Range.START_TO_START, whole) > 0, endsIn = r.compareBoundaryPoints(Range.END_TO_END, whole) < 0;
  if (!startsIn && !endsIn) return null;
  const part = r.cloneRange();
  if (!startsIn) part.setStart(whole.startContainer, whole.startOffset);
  if (!endsIn) part.setEnd(whole.endContainer, whole.endOffset);
  return part;
}
/** Paint the phrases `ids` in the paper (none: clear). */
function xlPaint(ids) {
  if (!xlCanPaint()) return;
  const rs = [...ids].map((i) => XLP.ranges.get(i)).filter(Boolean);
  if (rs.length) CSS.highlights.set("xl-paper", new Highlight(...rs)); else CSS.highlights.delete("xl-paper");
  // A formula is a stack of positioned glyph boxes, which a text highlight paints unevenly or not
  // at all: a formula a lit phrase takes whole is washed as one box, and the part of a formula a
  // phrase covers (one condition of a display that holds several) is boxed where it stands.
  $$(".xl-math").forEach((x) => x.classList.remove("xl-math"));
  $$(".xl-box").forEach((x) => x.remove());
  if (!rs.length || !XLP.root) return;
  const at = XLP.root.getBoundingClientRect();
  for (const f of XLP.root.querySelectorAll(".katex, mjx-container")) for (const r of rs) {
    if (!r.intersectsNode(f)) continue;
    const part = xlInside(r, f);
    if (!part) { f.classList.add("xl-math"); continue; }
    const b = part.getBoundingClientRect(), box = document.createElement("div");
    box.className = "xl-box";
    box.style.cssText = `left:${b.left - at.left - 2}px;top:${b.top - at.top - 2}px;width:${b.width + 4}px;height:${b.height + 4}px`;
    XLP.root.append(box);
  }
}
/** The phrase of the open result under a point of the page, or null. */
function xlPhraseAt(x, y) {
  if (!XLP.ranges.size) return null;
  const c = document.caretPositionFromPoint ? document.caretPositionFromPoint(x, y) : null;
  const r = c ? null : document.caretRangeFromPoint?.(x, y);
  const node = c ? c.offsetNode : r?.startContainer, offset = c ? c.offset : r?.startOffset;
  if (node) for (const [id, range] of XLP.ranges) { try { if (range.comparePoint(node, offset) === 0) return id; } catch { /* another document */ } }
  // over a formula the caret may land outside every phrase (its glyphs are positioned boxes): the
  // phrase the formula under the pointer belongs to
  const f = document.elementFromPoint(x, y)?.closest(".katex, mjx-container");
  if (f) for (const [id, range] of XLP.ranges) if (range.intersectsNode(f)) return id;
  return null;
}

/* ── Lean ↔ the condition's own passage ───────────────────────────────────
   A declaration tagged with a core node (`leanDefs[key].node`) has a place on the page
   (`detail.places`): the passage of the paper stating it, or — a reading the paper does not print —
   its note in the paper and its entry among the open result's added conditions. */
function plNames(el) { return (el.dataset.places ?? el.dataset.place ?? "").split(/\s+/).filter(Boolean); }
/** The place of core node `node` as the page now shows it (`el` in the paper, `cond` in the drawer), or null. */
function plOf(node) {
  const p = node ? P.detail?.places?.[node] : null; if (!p) return null;
  if (p.anchor) {
    const at = document.getElementById(p.anchor); if (!at) return null;
    return { el: at.closest(".formal, .p") ?? at, says: p.says, label: (P.paper?.envs ?? []).find((e) => e.anchor === p.anchor)?.heading ?? "the text" };
  }
  const card = P.paper?.readings?.[node], el = card ? markOf(card) : null;
  const cond = resultById(P.drawer)?.conditions?.some((c) => c.id === node) ?? false;
  return el || cond ? { el, cond, label: el ? "clarification" : "condition added" } : null;
}
/** The words of a place inside its block, when the paper's text there reads as the core has it. */
const plRange = (p) => (p.says && xlCanPaint() ? xlFind([{ ...xlChars(p.el), from: 0 }], p.says) : null);
/** Light the places of `nodes` (none: clear): a passage's own words, else its whole block; a reading's note and entry. */
function plPaint(nodes) {
  $$(".pl-hot, .pl-math").forEach((x) => x.classList.remove("pl-hot", "pl-math"));
  const ranges = [];
  for (const node of nodes) {
    const p = plOf(node); if (!p) continue;
    const range = p.el ? plRange(p) : null;
    if (range) { ranges.push(range); for (const f of p.el.querySelectorAll(".katex, mjx-container")) if (range.intersectsNode(f)) f.classList.add("pl-math"); }
    else p.el?.classList.add("pl-hot");
    if (p.cond) $(`#d-body [data-cond="${CSS.escape(node)}"]`)?.classList.add("pl-hot");
  }
  if (!xlCanPaint()) return;
  if (ranges.length) CSS.highlights.set("xl-place", new Highlight(...ranges)); else CSS.highlights.delete("xl-place");
}
/** Bring the place of `node` into view: in the paper, else in the drawer. */
function plGo(node) {
  const p = plOf(node); if (!p) return;
  if (p.el) reveal(plRange(p)?.startContainer.parentElement ?? p.el, "center");
  else $(`#d-body [data-cond="${CSS.escape(node)}"]`)?.scrollIntoView({ block: "center", behavior: "smooth" });
}

/** The drawer row stating phrase `id` first, or null. */
const xlRowOf = (id) => $$("#drawer .xlscope .srow").find((o) => xlNames(o).includes(id)) ?? null;

const xlLight = (t) => {
  $$(".xl-hot, .xl-also").forEach((x) => x.classList.remove("xl-hot", "xl-also"));
  if (!t) xlPaint([]);
  // the passages its declarations formalize light with a row of the drawer, whatever its phrases
  const places = t?.closest("#drawer") ? plNames(t) : [];
  plPaint(places); if (places.length) t.classList.add("xl-hot");
  const scope = t?.closest(".xlscope"); if (!t || !scope) return;
  const names = new Set(xlNames(t));
  // In the paper's drawer a row lights itself and its phrases in the paper (none: none stay lit); the
  // other rows stating one of those phrases are marked too, quieter (claims of one theorem share
  // their hypotheses' wording).
  if (scope.closest("#drawer")) {
    if (names.size) { t.classList.add("xl-hot"); scope.querySelectorAll(".srow").forEach((o) => { if (o !== t && xlNames(o).some((n) => names.has(n))) o.classList.add("xl-also"); }); }
    xlPaint(names); return;
  }
  if (!names.size) return;
  const goal = [...names].some((n) => n.startsWith("⊢"));
  scope.querySelectorAll(".xl, .srow").forEach((o) => { const on = xlNames(o); if (on.some((n) => names.has(n) || (n === "⊢" && goal) || (n.startsWith("⊢") && names.has("⊢")))) o.classList.add("xl-hot"); });
};
// the paper's statement → its row: point at a phrase to light it and its rows, click to bring the row up
let xlPaperLast = null, xlPaperTick = 0;
document.addEventListener("mousemove", (e) => {
  if (!XLP.root || xlPinned || !$("#drawer").classList.contains("on")) return;
  if (!XLP.root.contains(e.target)) { if (xlPaperLast) { xlPaperLast = null; xlLight(null); } return; }
  const now = performance.now(); if (now - xlPaperTick < 60) return; xlPaperTick = now;
  const id = xlPhraseAt(e.clientX, e.clientY);
  if (id === xlPaperLast) return; xlPaperLast = id;
  XLP.root.style.cursor = id ? "pointer" : "";
  $$(".xl-hot, .xl-also").forEach((x) => x.classList.remove("xl-hot", "xl-also"));
  if (!id) { xlPaint([]); return; }
  xlPaint([id]);
  $$("#drawer .xlscope .srow").forEach((o) => { if (xlNames(o).includes(id)) o.classList.add("xl-hot"); });
});
document.addEventListener("mouseover", (e) => {
  if (xlPinned && document.contains(xlPinned)) return; // a clicked row keeps its phrases lit
  const t = e.target.closest(".xl, .srow, .ds-place"); if (t === xlLast) return; xlLast = t;
  xlLight(t);
});
// click a row or a phrase to keep its link lit; click it again, or elsewhere, to let go
document.addEventListener("click", (e) => {
  // a phrase of the open result in the paper: its row, brought into view in the drawer and kept lit
  if (XLP.root?.contains(e.target) && $("#drawer").classList.contains("on") && !e.target.closest("a")) {
    const id = xlPhraseAt(e.clientX, e.clientY), row = id ? xlRowOf(id) : null;
    if (row) {
      $$(".xl-pin").forEach((x) => x.classList.remove("xl-pin"));
      for (let f = row.closest("details:not([open])"); f; f = f.closest("details:not([open])")) f.open = true; // a row in a closed fold is shown
      xlPinned = row; row.classList.add("xl-pin"); xlLight(row); xlPaint([id]);
      row.scrollIntoView({ block: "center", behavior: "smooth" });
      return;
    }
  }
  // a declaration's place: kept lit and brought into view (its fold stays as it is)
  const chip = e.target.closest("#drawer .ds-place");
  if (chip) {
    e.preventDefault();
    $$(".xl-pin").forEach((x) => x.classList.remove("xl-pin"));
    xlPinned = chip; chip.classList.add("xl-pin"); xlPaint([]); xlLight(chip); plGo(chip.dataset.place);
    return;
  }
  const t = e.target.closest(".xlscope .xl, .xlscope .srow");
  $$(".xl-pin").forEach((x) => x.classList.remove("xl-pin"));
  if (!t || t === xlPinned) { xlPinned = null; xlLast = null; if (!t) $$(".xl-hot, .xl-also").forEach((x) => x.classList.remove("xl-hot", "xl-also")); return; }
  xlPinned = t; t.classList.add("xl-pin"); xlLight(t);
  // a row of the drawer: the place the paper says it, brought into view
  if (t.closest("#drawer")) {
    const first = xlNames(t).map((i) => XLP.ranges.get(i)).find(Boolean);
    (first?.startContainer.parentElement)?.scrollIntoView({ block: "center", behavior: "smooth" });
  }
});

/* ═════════════ PAPER VIEW ═════════════ */
/* `open`: the margin card being read; `drawer`: the result whose drawer is open (`folds`: its opened
   declarations); `sel`: the proof-map node; `off`: the hidden kinds of note; `drawn`: what each part of
   the page was last drawn from. What the owner has entered and not yet sent: `promo` (promotion
   decisions), `repair` (rulings on repairs, by node), `edit` (a reading being reworded); `sent`: the
   rulings on repairs that went out and the run has not taken up yet (`sentState`).
   The run's detail comes in two parts: `page` — what the page draws before a drawer opens, small, since
   a run at work changes it every few seconds — and `drawers`, what only the results' drawers show;
   `detail` is the two as one (`withDrawers`), which every part reads. `cards`: the HTML each margin
   card was last drawn from. */
const blankMsg = () => ({ re: null, text: "", files: [], error: "", sending: false });
const paperState = () => ({ open: null, drawer: null, folds: new Set(), foldsOf: null, sel: null, drawn: {}, promo: {}, repair: {}, edit: null, flag: null, msg: blankMsg(), fresh: new Set(), threadN: -1, clearAsk: null, sent: null, page: null, drawers: null, cards: null });
const P = { built: null, detail: null, paper: null, off: new Set(), ...paperState() };
/** The run's detail as the page's parts read it: the page's part with, once it has come, the drawers'
    (`w`) — each result's, the declarations they open, the TeX the server rendered for them. What the
    page's part says of a result stands (the drawers' may be a moment older). */
function withDrawers(page, w) {
  if (!w) return { leanDefs: {}, places: {}, ...page };
  const whole = (r, d) => (d ? { ...d, ...r, review: r.review && { ...d.review, ...r.review } } : r);
  return { ...page, leanDefs: w.leanDefs, places: w.places, texHtml: { ...w.texHtml, ...page.texHtml }, results: page.results.map((r) => whole(r, w.results[r.id])) };
}
/* The paper's body is the heavy part of the page (megabytes of formulas to parse): the one drawn is
   kept when the reader leaves the paper, and put back as it stands when they return to it unchanged. */
let KEPT = null; // { paper: the payload it was drawn from, el }
function keepBody() { const el = $("#paper-body"); if (el && P.paper && P.drawn.body === P.paper) KEPT = { paper: P.paper, el }; }
/** A verdict or bucket key as the page words it: the data says `repaired`, the page says revised. Pure. */
const bucketWord = (k) => (({ repaired: "revised" })[k] ?? k).replace(/_/g, " ");
const KIND_TAG = { note: ["PaperFormalizer", "t-note"], reading: ["Clarification", ""], "reading-owner": ["Author's reading", ""], "reading-symbol": ["Symbol", ""], condition: ["Bookkeeping condition", "t-cond"], detail: ["Proof detail", "t-detail"], rewind: ["Proposed correction", "t-note"], cap: ["Revision not settled", "t-note"] };
const CHIP = { note: "Findings", reading: "Clarifications", "reading-owner": "Clarifications", "reading-symbol": "Clarifications", condition: "Bookkeeping", detail: "Proof details", rewind: "Findings", cap: "Findings" };

async function showPaper(slug, first) {
  const at = `/api/runs/${encodeURIComponent(slug)}`, here = () => S.view === "paper" && S.slug === slug;
  // asked for at once; the page is drawn from the first two, and the drawers' part joins when it comes
  const dP = api(at), pP = api(`${at}/paper`), wP = api(`${at}/drawers`);
  pP.catch(() => {}); wP.catch(() => {}); // each is awaited further down
  const fresh = P.built !== slug;
  if (fresh) {
    // a paper opened: the page stands, with the run's state, as soon as its detail is here — the
    // paper's text (megabytes) follows
    const d0 = await dP;
    if (!here() || P.built === slug) return;
    const navP = $("#nav-paper"); navP.hidden = false; navP.textContent = `Paper · ${slug}`; navP.href = `#/paper/${encodeURIComponent(slug)}`;
    Object.assign(P, { built: slug, paper: null }, paperState()); // a paper opened afresh: nothing of the last one's page
    app.innerHTML = `<div class="pv m-all" id="pv">
      <aside class="pv-left" aria-label="Paper navigation"><div class="side-h">Run</div><ol class="vstages" id="vstages"></ol>
        <div class="side-h">Contents</div><ul class="toc" id="toc"></ul>
        <div class="side-h">Proof map</div><svg class="pm-svg" id="pm-svg" role="group" aria-label="Dependency map"><defs><marker id="pm-a" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="5" markerHeight="5" orient="auto-start-reverse"><path class="pm-arr" d="M0,0.6 L7.4,4 L0,7.4 Z"></path></marker></defs><g id="pm-marks"></g></svg>
        <div class="pm-legend"><span class="pm-key"><i class="pm-sw err"></i>error</span><span class="pm-key"><i class="pm-sw minor"></i>clarification</span><span class="pm-key"><i class="pm-sw top"></i>key result</span><span class="pm-key"><i class="pm-dotk"></i>needs you</span><span class="pm-key"><i class="pm-dotk lean"></i>Lean proved</span></div>
        <p class="pm-note">An arrow reads “used by”: main results sit on top. Click a result for its links; double-click to jump to it.</p><div class="pm-card" id="pm-card" hidden></div></aside>
      <article class="paper" id="article"><div class="byline" id="byline"></div><h1 class="ptitle" id="ptitle"></h1><div class="authors" id="pauthors"></div><div id="status"></div>
        <div class="rtool" role="toolbar" aria-label="Review"><span class="lbl">Markup</span><span class="seg" id="markup" role="group"><button type="button" data-m="all" aria-pressed="true" title="Red: the printed text that is wrong. Blue: the correction.">All markup</button><button type="button" data-m="simple" aria-pressed="false" title="The corrected text; a bar in the margin marks each change.">Corrected</button><button type="button" data-m="original" aria-pressed="false">Original</button></span><span class="chips" id="chips"></span><span class="nav-changes"><button type="button" id="prev-c" aria-label="Previous">↑</button><span id="c-pos">—</span><button type="button" id="next-c" aria-label="Next">↓</button></span></div>
        <div class="render-check" id="render-check"></div><div id="paper-body"><p class="loading">Loading…</p></div><div id="promo"></div></article>
      <aside class="pv-rail" aria-label="PaperFormalizer comments"><div class="rail-head">PaperFormalizer <span id="rail-count"></span></div><p class="rail-off">Comments are hidden in this view.</p><div class="rail-cards" id="rail-cards"></div></aside></div>`;
    wirePaper();
    P.page = d0.data; P.detail = withDrawers(P.page, P.drawers);
    drawHeader(); drawStages(); drawStatus();
  }
  wP.then((w) => {
    if (!here() || P.built !== slug || P.drawers === w.data) return;
    P.drawers = w.data; P.detail = withDrawers(P.page, P.drawers);
    // the open drawer follows its result
    if (P.drawer && P.drawn.drawer !== JSON.stringify(resultById(P.drawer))) refreshDrawer();
  }, (err) => console.warn(err));
  const [d, p] = await Promise.all([dP, pP]);
  if (!here() || P.built !== slug) return;
  first ||= fresh;
  const detailChanged = d.changed || first;
  const paperChanged = p.changed || first;
  P.page = d.data; P.paper = p.data;
  const D = P.detail = withDrawers(P.page, P.drawers);
  const sent = P.sent ? (P.sent.seen++, sentState(P.sent, D.repairs, D.summary.live)) : null;
  if (sent === "taken" || sent === "dropped") P.sent = null;
  if (sent === "dropped") toast("The run did not take up your decisions — its log says why. They are kept here to send again.", true);
  const scroll = window.scrollY;
  if (paperChanged) drawPaperBody();
  if (detailChanged || paperChanged || sent === "dropped") {
    // a live run changes its detail every few seconds (stage, headline): only the parts whose own
    // inputs changed are redrawn — the margin cards and the map are heavy on a long paper. A part's
    // inputs are everything it reads from the run's detail; all of them read the paper.
    const stale = (part, ...inputs) => { const k = inputs.join("\n"); const was = P.drawn[part]; P.drawn[part] = k; return paperChanged || was !== k; };
    const results = JSON.stringify(P.page.results);
    drawHeader(); drawStages(); drawStatus();
    if (stale("marks", results, D.summary.live)) { drawBadges(); drawProofOnlyNotes(); }
    if (stale("map", results)) drawMap();
    // (the cards that said "sent" were drawn outside this bookkeeping: drawn again when that is over)
    const cards = stale("cards", results, JSON.stringify(D.repairs), JSON.stringify(D.objections), Boolean(P.sent), atRest(D.summary)) || sent === "dropped";
    if (cards) drawCards();
    if (stale("promo", JSON.stringify(D.promotion))) drawPromo();
    if (cards) requestAnimationFrame(layout);
    // the open drawer follows its result, and the paper's text when that was drawn anew
    if (P.drawer && stale("drawer", JSON.stringify(resultById(P.drawer)))) refreshDrawer();
  }
  window.scrollTo(0, scroll);
}

function resultById(id) { return P.detail?.results.find((r) => r.id === id) ?? null; }
function resultByLabel(label) { return P.detail.results.find((r) => r.label === label) ?? null; }
/** The run is at rest: nothing is at work on it, so the owner's change (a reading reworded) can resume it. */
const atRest = (s) => !s.live && s.status !== "running" && s.status !== "superseded";
/* The element a result stands at on the page: its environment; the block of a corollary a repair
   split off; else — a result stated in prose — the anchor at its first line. */
function resEl(id) {
  const r = resultById(id);
  const env = r?.label ? envEl(r.label) : null;
  if (env) return env;
  const at = P.paper?.anchors?.[id] ? document.getElementById(P.paper.anchors[id]) : null;
  return at?.closest(".rv.cor, .prose-res") ?? at;
}
function envOf(id) {
  const r = resultById(id);
  const env = r && r.label ? (P.paper?.envs ?? []).find((e) => e.label === r.label) : null;
  if (env) return env;
  const a = P.paper?.anchors?.[id];
  return a ? { anchor: a, label: null, envName: r?.kind ?? "result", heading: r?.splitFrom ? splitHeading(r) : r?.citedIn ? citedHeading(r) : P.paper?.anchorHeadings?.[id] ?? proseHeading(r ?? { id, kind: "result" }) } : null;
}
/* A published result a proof invokes by citation: named by the citation and the result whose proof uses it. */
/* The label a result gets where the paper only anchors it. A citation invoked inside a proof is a label
   and nothing more: it has no statement, Lean or proof of its own to open (its place in the Lean is a
   premise of the result that uses it), so it is no button. */
function resBadge(r) {
  const text = `${esc(envOf(r.id)?.heading ?? proseHeading(r))} ${badge(r)}`;
  // the label of a citation invoked inside a proof stands on a line of its own
  return `<button type="button" class="res-badge${r.citedIn ? " cited-site" : ""}" data-res="${esc(r.id)}">${text}</button>`;
}
/** The Lean statement of a result the paper cites without proving: the proposition the proofs that use
    it assume (`[key, declaration]`), or null — the result has Lean of its own, or none is on file. */
function citedDef(r) { return !r.citedLean ? null : Object.entries(P.detail?.leanDefs ?? {}).find(([, d]) => d.node === r.id || d.name.split(".").pop() === r.citedLean) ?? null; }
/** The proof that invoked the citation no longer uses it: a repair replaced that step. */
function citedDropped(r) { const host = r.citedIn ? resultById(r.citedIn) : null; return Boolean(host) && !host.deps.includes(r.id); }
function citedHeading(r) {
  const host = envOf(r.citedIn)?.heading ?? "a result";
  if (citedDropped(r)) return `[${r.cites}] · no longer used in ${host}`;
  return `[${r.cites}] · ${r.citedLean ? "assumed · " : r.lean ? "proved in Lean · " : ""}used in ${host}`;
}
/* A block a repair split off a result is named after that result: the paper gives it no number. It is
   a corollary of the result, or (`splitKind`) a proposition the printed statement bundled in. */
function splitHeading(r) {
  const of = envOf(r.splitFrom)?.heading ?? "";
  const word = r.splitKind === "proposition" ? "Proposition" : "Corollary";
  // numbered under its result — "Corollary 5.2.1", "Proposition 5.2.2", one running number across both
  // kinds — so it is told from the paper's own numbers and from its siblings
  const num = /\s((?:[A-Z]\.?)?\d[\w.]*)$/.exec(of)?.[1];
  const k = P.detail.results.filter((x) => x.splitFrom === r.splitFrom).findIndex((x) => x.id === r.id) + 1;
  return num ? `${word} ${num}.${k}` : `${word} ${k} of ${of || "the result above"}`;
}
function proseHeading(r) { const k = r.kind.charAt(0).toUpperCase() + r.kind.slice(1); const tail = r.id.split(":").pop().replace(/-/g, " "); return `${k} (${tail})`; }
const shortHeading = (h) => h.replace(/^Theorem/, "Thm").replace(/^Proposition/, "Prop").replace(/^Corollary/, "Cor").replace(/^Lemma/, "Lem").replace(/^Definition/, "Def").replace(/^Assumption/, "Ass");

function drawHeader() {
  const s = P.detail.summary;
  $("#byline").innerHTML = `PaperFormalizer · <b>${esc(s.slug)}</b>${P.detail.source.main ? ` — <code>${esc(P.detail.source.main)}</code>` : ""} · shown from <code>${esc(P.paper?.from ?? "—")}/</code>${P.paper?.pdf ? ` · <a href="${esc(P.paper.pdf)}" target="_blank" rel="noopener">PDF</a>` : ""}${s.tokens ? `<br><span class="tokens" title="Model tokens this run has used so far (runs/${esc(s.slug)}/token_usage.jsonl)">Tokens: ${esc(tokenLine(s.tokens))}</span>` : ""}`;
  const h = P.paper?.health;
  const rc = $("#render-check");
  if (rc && h) {
    const unknown = Object.entries(h.unknownCommands).sort((a, b) => b[1] - a[1]);
    const bits = [h.unresolvedRefs.length ? `${h.unresolvedRefs.length} reference(s) unresolved` : "all references resolved", `${h.figures} figure(s)${h.missingFigures.length ? `, ${h.missingFigures.length} file(s) missing` : ""}`, `${h.tables} table(s)`, h.mathErrors ? `${h.mathErrors} formula(s) shown as source (left to the agent)` : "", h.mathFallbacks ? `${h.mathFallbacks} formula(s) drawn by MathJax` : "", h.omitted ? `${h.omitted} drawing(s) only in the PDF` : "", unknown.length ? `${unknown.length} command(s) shown as plain text` : ""].filter(Boolean);
    const ok = !h.unresolvedRefs.length && !h.mathErrors && !h.missingFigures.length;
    rc.innerHTML = `<details><summary><span class="${ok ? "ok" : "warn"}">●</span> Render check: ${esc(bits.join(" · "))}</summary><div>${h.unresolvedRefs.length ? `<p>Unresolved: <code>${h.unresolvedRefs.map(esc).join(", ")}</code></p>` : ""}${h.missingFigures.length ? `<p>Missing figure files: <code>${h.missingFigures.map(esc).join(", ")}</code></p>` : ""}${unknown.length ? `<p>Commands shown as plain text: <code>${unknown.slice(0, 30).map(([k, n]) => `\\${esc(k)}${n > 1 ? `×${n}` : ""}`).join(" ")}</code></p>` : ""}${P.paper.pdf ? `<p>For anything that looks wrong here, the <a href="${esc(P.paper.pdf)}" target="_blank" rel="noopener">typeset PDF</a> is exact.</p>` : ""}</div></details>`;
  }
  $("#ptitle").innerHTML = P.paper?.title ? P.paper.title : esc(s.title);
  $("#pauthors").innerHTML = P.paper?.authors || esc(s.authors);
}
function drawStages() {
  $("#vstages").innerHTML = P.detail.stages.map((st) => `<li class="${st.state}"><span class="ic"></span><code>${esc(st.id.replace(/^(\d)/, "F$1"))}</code><span>${esc(st.label.replace(/^F[\d.]+ /, ""))}</span></li>`).join("");
}
/* The page of a shared paper: what the check concluded, who shared it, and the bundle's files — in
   place of a run's status, its conversation and its decisions. */
function drawSnapStatus() {
  const s = P.detail.summary, sh = SNAP.share;
  const b = s.buckets ? Object.entries(s.buckets).map(([k, v]) => `${v} ${bucketWord(k)}`).join(" · ") : "";
  const login = /^[A-Za-z0-9-]{1,39}$/.test(sh?.shared_by ?? "") ? sh.shared_by : null;
  const on = /^\d{4}-\d{2}-\d{2}/.test(sh?.shared_at ?? "") ? sh.shared_at.slice(0, 10) : null;
  const by = login ? `<p>Shared by <a href="https://github.com/${esc(login)}" target="_blank" rel="noopener">@${esc(login)}</a>${on ? ` on ${esc(on)}` : ""}.</p>` : "";
  const files = [...(P.paper?.pdf ? [[P.paper.pdf, "Revised paper (PDF)"]] : []), ...(SNAP.leanDir ? [["lean/", "Lean code"]] : [])];
  $("#status").innerHTML = `<div class="status"><div class="line"><span class="pill b-done">${esc(bucketWord(String(s.verdict ?? "report")))}</span><h2>Formalized with PaperFormalizer</h2></div>${b ? `<p>${esc(b)}</p>` : ""}${by}<div class="actions"><button class="btn" type="button" data-report>Full report</button>${files.map(([f, label]) => `<a class="btn" href="${esc(f)}" target="_blank" rel="noopener">${esc(label)}</a>`).join("")}</div></div>`;
}
/* The bundle's REPORT.md, typeset in the drawer (a shared paper's page): its headings, paragraphs and
   lists, **bold** and `code`, and its formulas by KaTeX under the paper's macros. A plain reader of
   the few forms the report writes, not Markdown at large; what it inserts passes DOMPurify. */
function reportHTML(md) {
  const m = P.paper?.macros;
  const inline = (t) => t.replace(/\\label\{[^{}]*\}\s*/g, "").split(/`([^`]+)`/).map((part, k) => (k % 2 ? `<code>${esc(part)}</code>` : typeset(part, m, (x) => esc(x).replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")))).join("");
  const out = [];
  let para = [], list = null;
  const flush = () => {
    if (para.length) out.push(`<p>${inline(para.join(" "))}</p>`);
    if (list) out.push(`<ul>${list.map((i) => `<li>${inline(i)}</li>`).join("")}</ul>`);
    para = []; list = null;
  };
  for (const line of String(md).split(/\r?\n/)) {
    const h = /^(#{1,4})\s+(.*)$/.exec(line), li = /^\s{0,3}[-*]\s+(.*)$/.exec(line);
    if (!line.trim()) flush();
    else if (h) { flush(); out.push(`<h${Math.min(6, h[1].length + 2)} class="rh">${inline(h[2])}</h${Math.min(6, h[1].length + 2)}>`); }
    else if (li) { if (para.length) { const keep = list; list = null; flush(); list = keep; } (list ??= []).push(li[1]); }
    else if (list && /^\s+\S/.test(line)) list[list.length - 1] += ` ${line.trim()}`;
    else { if (list) flush(); para.push(line.trim()); }
  }
  flush();
  return out.join("");
}
async function openReport() {
  closeDrawer();
  $("#d-kind").textContent = "report"; $("#d-title").textContent = "Full report";
  $("#d-sub").innerHTML = `<a href="REPORT.md" target="_blank" rel="noopener">REPORT.md</a>`;
  $("#d-body").innerHTML = `<p class="none">Loading…</p>`;
  $("#drawer").classList.add("on"); $("#drawer").setAttribute("aria-hidden", "false");
  document.body.classList.add("drawer-on");
  try {
    const r = await fetch("REPORT.md", { credentials: "same-origin" });
    if (!r.ok) throw new Error(`${r.status} ${r.statusText}`);
    $("#d-body").innerHTML = `<div class="report">${reportHTML(await r.text())}</div>`;
  } catch (err) { $("#d-body").innerHTML = `<p class="none">The report could not be read: ${esc(err.message)}</p>`; }
  $("#d-body").scrollTop = 0;
}
function drawStatus() {
  if (SNAP) { drawSnapStatus(); return; }
  const host = $("#status");
  // a live run redraws this every few seconds: an open rejection keeps what the owner typed, and the caret
  const drafts = new Map($$(".review", host).filter((b) => !b.querySelector(".ask").hidden).map((b) => [b.dataset.rid, b.querySelector("textarea").value]));
  const typing = document.activeElement?.matches?.("#status .review textarea") ? document.activeElement : null;
  const caret = typing && { rid: typing.closest(".review").dataset.rid, from: typing.selectionStart, to: typing.selectionEnd };
  const writing = document.activeElement?.matches?.("#status [data-msg-text]") ? { from: document.activeElement.selectionStart, to: document.activeElement.selectionEnd } : null;
  const listTop = $(".thread-list", host)?.scrollTop ?? 0;
  const askTop = new Map($$(".ask-list", host).map((l) => [l.dataset.ask, [l.scrollTop, l.childElementCount]]));
  markRead();
  drawStatusBox();
  const s = P.detail.summary;
  // the conversation with the agent: what was said on a request the agent still asks is shown on
  // it, the rest under the status; the owner writes from either (`P.msg`)
  const said = P.detail.messages ?? [], asked = new Set((s.requests ?? []).map((q) => q.id)), byId = new Map(said.map((m) => [m.id, m]));
  const askOf = (m) => { for (let k = 0; m?.re && k < 50; m = byId.get(m.re), k++) if (asked.has(m.re)) return m.re; return null; };
  const asks = (s.requests ?? []).map((q) => {
    const on = said.filter((m) => askOf(m) === q.id);
    const foot = P.msg.re === q.id ? composeHTML() : `<div class="row"><button class="btn btn-primary" type="button" data-msg="open" data-re="${esc(q.id)}">Reply</button><button class="btn" type="button" data-dismiss="${esc(q.id)}" title="It is answered: take it off the page">Dismiss</button>${s.orch ? "" : `<span class="hint">No agent session is attached: reply here (it is delivered once one is), or answer in a session.</span>`}</div>`;
    return `<div class="ask-banner"><div class="ask-list" data-ask="${esc(q.id)}"><div><b>The agent asks you:</b> ${tex(q.text, P.paper?.macros)}</div>${on.map(messageHTML).join("")}</div>${foot}</div>`;
  }).join("");
  // The thread ends with the box to write on in — unless the owner is replying on a request above
  // (a reply to a request cleared meanwhile is written on here: its words are kept). It scrolls
  // within its own height, the newest entry last.
  const loose = P.msg.re === null || !asked.has(P.msg.re);
  const rest = said.filter((m) => !askOf(m)), news = said.filter((m) => m.unseen || P.fresh.has(m.id)).length;
  const clearing = P.clearAsk ? `<p class="compose-err" role="alert">${esc(P.clearAsk)} <button class="linkbtn" type="button" data-msg="clear-anyway">Clear anyway</button> <button class="linkbtn" type="button" data-msg="clear-keep">Keep it</button></p>` : "";
  // (hidden at the owner's wish, remembered in this browser: its heading stays, with what is new)
  const hide = `<button class="linkbtn" type="button" data-msg="${threadHidden() ? "show" : "hide"}" title="${threadHidden() ? "Show the conversation again" : "Fold the conversation away; its heading stays"}">${threadHidden() ? "Show" : "Hide"}</button>`;
  const thread = threadHidden()
    ? `<section class="thread thread-hidden"><h3>Ask the agent${news ? ` <span class="msg-new">${news} new</span>` : ""}<span class="thread-tools">${hide}</span></h3></section>`
    : `<section class="thread"><h3>Ask the agent${news ? ` <span class="msg-new">${news} new</span>` : ""}<span class="thread-tools">${said.length ? `<button class="linkbtn" type="button" data-msg="clear" title="Archive this conversation in the run's folder and start afresh">Clear conversation</button>` : ""}${hide}</span></h3>${clearing}${rest.length ? `<div class="thread-list">${rest.map(messageHTML).join("")}</div>` : ""}${loose ? composeHTML() : `<div class="row"><button class="btn" type="button" data-msg="open">Write to the agent here</button><span class="hint">You are replying to its request above.</span></div>`}</section>`;
  const who = (s.orch ? `<span class="orch on">● ${esc(s.orch.agent)} attached — it acts at each halt</span>` : `<span class="orch">○ No agent attached <button class="linkbtn" type="button" id="orch-how">start one</button></span>`) +
    (s.fullAuto ? `<span class="orch on" title="Started with --full-auto: the revisions that would weaken a main result and the promotion rounds take the agent's recommendations; each appears under “Review the agent's decisions”. You may still decide an item first.">full auto — your decisions take the agent's recommendations, for your review after</span>` : "");
  // rulings the agent made at halts, for the owner's review: approve, or reject with guidance (the agent acts on it)
  const reviews = (s.reviews ?? []).map((r) => `<div class="review" data-rid="${esc(r.id)}"><div><b>The agent decided</b> on ${esc(envOf(r.node)?.heading ?? r.node)} <span class="meta">${esc(ago(Date.parse(r.at)))}</span></div><div class="review-b">${tex(r.text, P.paper?.macros)}</div><div class="actions"><button class="btn btn-primary" type="button" data-review="approve">Approve</button><button class="btn" type="button" data-review="reject">Reject</button></div><div class="ask" hidden><label class="mono" style="font-size:var(--fs-2xs);color:var(--ink-faint)">What should the agent do instead?</label><textarea></textarea><div class="row" style="justify-content:flex-end"><button class="btn btn-ghost" type="button" data-review="cancel">Cancel</button><button class="btn btn-primary" type="button" data-review="send">Send to the agent</button></div></div></div>`).join("");
  host.insertAdjacentHTML("afterbegin", asks + (reviews ? `<section class="reviews"><h3>Review the agent's decisions</h3>${reviews}</section>` : ""));
  // beside Stop, and whenever there is a run: a word to the agent
  const box = host.querySelector(".status");
  if (box && !box.querySelector(".actions")) box.insertAdjacentHTML("beforeend", `<div class="actions"></div>`);
  box?.querySelector(".actions").insertAdjacentHTML("beforeend", `<button class="btn" type="button" data-msg="open">Message the agent</button>`);
  box?.insertAdjacentHTML("beforeend", `<div class="orch-line">${who}</div>`);
  host.insertAdjacentHTML("beforeend", thread);
  // the newest entry in view on open and when one arrives; else where the owner had scrolled to
  const list = $(".thread-list", host);
  if (list) list.scrollTop = P.threadN === rest.length ? listTop : list.scrollHeight;
  P.threadN = rest.length;
  // a request's exchange the same way: where the owner had scrolled to, the newest entry when one arrives
  for (const l of $$(".ask-list", host)) { const [top, n] = askTop.get(l.dataset.ask) ?? [0, -1]; l.scrollTop = n === l.childElementCount ? top : l.scrollHeight; }
  if (writing) { const ta = $("[data-msg-text]", host); if (ta) { ta.focus({ preventScroll: true }); ta.setSelectionRange(writing.from, writing.to); } }
  for (const [rid, text] of drafts) {
    const box = $(`.review[data-rid="${CSS.escape(rid)}"]`, host); if (!box) continue;
    const ta = box.querySelector("textarea");
    box.querySelector(".ask").hidden = false; ta.value = text;
    if (caret?.rid === rid) { ta.focus({ preventScroll: true }); ta.setSelectionRange(caret.from, caret.to); }
  }
}
/* The agent's messages are read once the paper's page shows them: marked so on the server (no click
   asked), and highlighted for as long as this page stays open (`P.fresh`). */
function markRead() {
  const unseen = (P.detail.messages ?? []).filter((m) => m.unseen);
  if (!unseen.length || document.hidden || P.reading) return;
  for (const m of unseen) P.fresh.add(m.id);
  P.reading = true;
  post(`/api/runs/${encodeURIComponent(S.slug)}/message-seen`, {}).catch(() => {}).then(() => { P.reading = false; });
}
/* Clear the conversation (archived in the run's folder). What the agent has not acted on is not
   cleared away unless the owner says so again. */
async function clearConversation(force) {
  try { await post(`/api/runs/${encodeURIComponent(S.slug)}/message-clear`, force ? { force: true } : {}); P.clearAsk = null; P.fresh.clear(); toast("Conversation cleared"); onChange(`run:${S.slug}`); }
  catch (err) { if (err.status === 409) { P.clearAsk = err.message; drawStatus(); } else toast(err.message, true); }
}
const bytesText = (n) => n >= 1048576 ? `${(n / 1048576).toFixed(1)} MB` : n >= 1024 ? `${Math.round(n / 1024)} kB` : `${n} B`;
/** One message of the conversation. The agent's is TeX; the owner's own words are text with their
 *  line breaks — never markup; a formula they write is typeset (`mixed`). Attached files are named, not linked. */
function messageHTML(m) {
  const agent = m.from === "agent";
  const fresh = m.unseen || P.fresh.has(m.id);
  const state = agent ? (fresh ? `<span class="msg-new">new</span>` : "") : m.waiting ? `<span class="hint">${P.detail.summary.orch ? (P.detail.summary.orch.watching ? "delivered to the attached agent — waiting for the agent" : "waiting for the agent — it will read it when it next checks") : "not delivered — waiting for the agent: nobody sees it until an agent session is attached"}</span>` : "";
  const files = (m.files ?? []).map((f) => `<li>${esc(f.name)} · ${bytesText(f.bytes)}</li>`).join("");
  return `<div class="msg${agent ? " agent" : ""}${fresh ? " unseen" : ""}"><div class="msg-by"><b>${agent ? "The agent" : "You"}</b> <span>${esc(ago(Date.parse(m.at)))}</span>${state}</div><div class="msg-b">${agent ? tex(m.text, P.paper?.macros) : mixed(m.words, P.paper?.macros).replace(/\n/g, "<br>")}</div>${files ? `<ul class="msg-files">${files}</ul>` : ""}</div>`;
}
/* What a message may carry (enforced by the server: `MESSAGE_LIMITS`, `UPLOAD_EXT` of server.ts). */
const MSG_LIMITS = { chars: 4000, files: 5, fileBytes: 40 * 1048576, bytes: 100 * 1048576, ext: [".pdf", ".txt", ".tex", ".bib", ".md", ".png", ".jpg", ".jpeg", ".zip", ".tar", ".gz", ".tgz"] };
/** The box the owner writes to the agent in (`P.msg`: its text, the files chosen, what was refused). */
function composeHTML() {
  const c = P.msg, reply = c.re !== null;
  const files = c.files.map((f, i) => `<li>${esc(f.name)} · ${bytesText(f.size)} <button class="linkbtn" type="button" data-msg="unfile" data-i="${i}" aria-label="Remove ${esc(f.name)}">×</button></li>`).join("");
  const hint = P.detail.summary.orch ? "The agent reads this and acts in its session; it changes nothing by itself." : "No agent session is attached: nobody sees this until one is. It is kept, and delivered when a session next watches the run; it changes nothing by itself.";
  return `<div class="compose" data-compose><textarea data-msg-text rows="3" maxlength="${MSG_LIMITS.chars}" aria-label="${reply ? "Your reply" : "Your message to the agent"}" placeholder="${reply ? "Your reply" : "What the agent should know"} (or drop a file here)">${esc(c.text)}</textarea>
    ${files ? `<ul class="msg-files">${files}</ul>` : ""}${c.error ? `<p class="compose-err" role="alert">${esc(c.error)}</p>` : ""}<p class="hint">${hint}</p>
    <div class="row"><button class="btn" type="button" data-msg="attach">Attach file</button>${reply ? `<button class="btn btn-ghost" type="button" data-msg="cancel">Cancel</button>` : ""}<button class="btn btn-primary" type="button" data-msg="send"${c.sending ? " disabled" : ""}>${c.sending ? "Sending…" : "Send to the agent"}</button></div></div>`;
}
/** Files chosen for the message being written, refused here as the server would refuse them. */
function attachFiles(list) {
  const c = P.msg; if (!c) return;
  c.error = "";
  for (const f of list) {
    const total = c.files.reduce((n, x) => n + x.size, 0);
    if (!MSG_LIMITS.ext.some((x) => f.name.toLowerCase().endsWith(x))) c.error = `${f.name}: not a kind of file a message carries (${MSG_LIMITS.ext.join(" ")})`;
    else if (c.files.length >= MSG_LIMITS.files) c.error = `A message carries at most ${MSG_LIMITS.files} files.`;
    else if (f.size > MSG_LIMITS.fileBytes) c.error = `${f.name}: a file is at most ${bytesText(MSG_LIMITS.fileBytes)}.`;
    else if (total + f.size > MSG_LIMITS.bytes) c.error = `The files of a message are at most ${bytesText(MSG_LIMITS.bytes)} together.`;
    else c.files.push(f);
  }
  drawStatus();
}
/* Send the message: each file as a request of its own (its bytes), then the message that carries
   them. It is stored for the agent, whose watcher wakes on it — nothing in the run changes. */
async function sendMessage() {
  const c = P.msg, base = `/api/runs/${encodeURIComponent(S.slug)}`;
  if (!c || c.sending) return;
  if (!c.text.trim() && !c.files.length) { c.error = "Write the message, or attach a file."; drawStatus(); return; }
  c.sending = true; c.error = ""; drawStatus();
  try {
    const draft = c.files.length ? [...crypto.getRandomValues(new Uint8Array(12))].map((b) => b.toString(16).padStart(2, "0")).join("") : undefined;
    for (const f of c.files) {
      const r = await fetch(`${base}/upload?draft=${draft}&name=${encodeURIComponent(f.name)}`, { method: "POST", headers: { "Content-Type": "application/octet-stream", "X-TC": "1" }, body: f, credentials: "same-origin" });
      if (!r.ok) throw new Error((await r.json().catch(() => ({}))).error || `${f.name} was not received (${r.status})`);
    }
    await post(`${base}/message`, { text: c.text, ...(c.re ? { re: c.re } : {}), ...(draft ? { draft } : {}) });
    if (P.msg === c) P.msg = blankMsg();
    toast(P.detail.summary.orch ? "Sent to the agent" : "Kept — delivered once an agent session is attached");
    onChange(`run:${S.slug}`);
  } catch (err) { c.sending = false; c.error = err.message; drawStatus(); }
}
function drawStatusBox() {
  const d = P.detail, s = d.summary, host = $("#status");
  // a proposal the owner sent back is still in the paper until its replacement is written
  $("#pv")?.classList.toggle("redoing", Boolean(s.redoing));
  // … and one the run is still checking is not yet the owner's to rule on
  $("#pv")?.classList.toggle("checking", Boolean(s.live && !s.redoing));
  if (s.live || s.status === "running") {
    // a promotion round being applied is at work too, though no runner is live: nothing to stop from here
    host.innerHTML = `<div class="status"><div class="line"><span class="pill b-running"><span class="dot-live"></span>running</span><h2>${tex(s.headline, P.paper?.macros)}</h2></div><p>This page updates as ${s.live ? "the run" : "it"} goes.</p>${s.live ? `<div class="actions"><button class="btn" type="button" id="stop-run">Stop the run</button></div>` : ""}</div>`;
    return;
  }
  if (s.status === "done") {
    const b = s.buckets ? Object.entries(s.buckets).map(([k, v]) => `${v} ${bucketWord(k)}`).join(" · ") : "";
    // a finished paper can be shared on the public site; its last share is shown with where it stands
    const sh = d.share, shared = sh ? shareLineHTML(sh) : "";
    if (sh && !SHARE_FINAL.has(sh.status)) sharePoll(S.slug);
    // offered only for a bundle that can be shared; else a line says why (`shareable`)
    const ready = s.shareable?.ok !== false;
    const share = ready ? `<button class="btn" type="button" id="share-run"${SHARING.has(S.slug) ? " disabled" : ""}>${SHARING.has(S.slug) ? "Sharing…" : sh ? "Share again" : "Share"}</button>` : "";
    host.innerHTML = `<div class="status"><div class="line"><span class="pill b-done">report</span><h2>${tex(s.headline, P.paper?.macros)}</h2></div>${b ? `<p>${esc(b)}</p>` : ""}${shared || (ready ? `<p class="share-invite">Share your checked work to help other people: they can read what the check found in this paper and build on its Lean proofs.</p>` : "")}${ready ? "" : `<p class="share-invite">Not ready to share: ${esc(s.shareable.reason ?? "its bundle cannot be shared")}.</p>`}<div class="actions">${d.promotion && d.promotion.waiting ? `<button class="btn btn-primary" type="button" data-jump="promo-sec">Review results proposed for your toolkit</button>` : ""}${share}</div></div>`;
    return;
  }
  if (s.status === "needs-you") {
    let body = "";
    if (d.promotion?.waiting) body += `<p>Promotion round ${d.promotion.round}: ${d.promotion.proposals.length} result(s) are proposed for your toolkit. Each has its own Accept / Defer / Decline buttons, at the end of the paper.</p><div class="actions"><button class="btn btn-primary" type="button" data-jump="promo-sec">Decide them</button></div>`;
    if (d.repairs?.length) body += P.sent ? `<p>Your decisions on the revisions were sent — the run is taking them up.</p>` : repairsPointerHTML(d);
    if (s.toResume) body += `<div class="actions"><button class="btn" type="button" id="resume-plain">Resume the run</button></div>`;
    if (!s.orch && (d.halt || d.pending || s.toResume)) body += noOrchHTML(s.slug);
    host.innerHTML = `<div class="status needs"><div class="line"><span class="pill b-needs-you">needs you</span><h2>${tex(s.headline, P.paper?.macros)}</h2></div>${body}</div>`;
    return;
  }
  if (s.status === "superseded") {
    host.innerHTML = `<div class="status"><div class="line"><span class="pill b-superseded">superseded</span><h2>${tex(s.headline, P.paper?.macros)}</h2></div><p>This run is kept as history; nothing here waits on anyone.</p><div class="actions"><a class="btn btn-primary" href="#/paper/${encodeURIComponent(s.supersededBy)}" style="border:none">Open ${esc(s.supersededBy)}</a></div></div>`;
    return;
  }
  if (s.status === "agent") {
    const msg = d.halt ? `<details><summary class="linkbtn">The halt</summary><pre>${esc(d.halt.message)}</pre></details>` : "";
    host.innerHTML = `<div class="status"><div class="line"><span class="pill b-agent">with the agent</span><h2>${tex(s.headline, P.paper?.macros)}</h2></div><p>The attached agent decides this halt and resumes the run; each ruling it makes for you appears here for your review.</p>${msg}</div>`;
    return;
  }
  host.innerHTML = `<div class="status"><div class="line"><span class="pill b-idle">idle</span><h2>${tex(s.headline, P.paper?.macros)}</h2></div><div class="actions"><button class="btn" type="button" id="resume-plain">Resume the run</button></div></div>`;
}
function drawPaperBody() {
  const body = $("#paper-body");
  if (!P.paper) { body.innerHTML = `<p class="empty-note">The paper's source is not in this run yet.</p>`; $("#toc").innerHTML = ""; return; }
  MARKS = ENVS = null; P.drawn.body = P.paper;
  if (KEPT?.paper === P.paper) { body.replaceWith(KEPT.el); $$(".linked", KEPT.el).forEach((x) => x.classList.remove("linked")); linkedId = null; }
  else { body.innerHTML = P.paper.html; setupPdfFigures(body); }
  // (a heading's own links — a \ref in it — are unwrapped: an <a> inside the entry's would split it in two)
  $("#toc").innerHTML = P.paper.toc.map((t) => `<li class="l${t.level}"><a href="#${esc(t.id)}" data-sec="${esc(t.id)}">${t.html?.replace(/<\/?a\b[^>]*>/g, "") ?? esc(t.text)}</a></li>`).join("");
}
/* Each result's verdict in the paper: a badge on its environment or on its corollary block; a result
   stated in prose gets a button at its first line, clickable like an environment. Drawn over the
   paper body, again whenever the results change. */
function drawBadges() {
  const body = $("#paper-body");
  $$(".fbadge", body).forEach((b) => b.remove());
  const put = (el, r) => { const b = document.createElement("span"); b.className = "fbadge"; b.innerHTML = badge(r); el.prepend(b); };
  for (const f of $$(".formal[data-label]", body)) { const r = resultByLabel(f.dataset.label); if (r) put(f, r); }
  for (const f of $$(".rv.cor[data-res], .prose-res[data-res]", body)) { const r = resultById(f.dataset.res); if (r) put(f, r); }
  const inEnv = new Set((P.paper?.envs ?? []).map((e) => e.label).filter(Boolean));
  for (const a of $$(".res-anchor[data-node]", body)) {
    const r = resultById(a.dataset.node);
    // a corollary block is headed already, and a result an environment holds is shown there
    a.innerHTML = !r || a.closest(".rv.cor, .prose-res") || (r.label && inEnv.has(r.label)) ? "" : resBadge(r);
  }
}
/* PDF figures: pdf.js draws page 1 when the figure scrolls into view (loaded once, lazily). */
let pdfjsP = null;
function setupPdfFigures(root) {
  const canvases = $$("canvas[data-pdf]", root);
  if (!canvases.length) return;
  const fail = (c) => c.replaceWith(Object.assign(document.createElement("span"), { className: "omitted", textContent: "This PDF figure could not be drawn — use “open”." }));
  if (!window.IntersectionObserver) { canvases.forEach((c) => drawPdf(c).catch(() => fail(c))); return; }
  const io = new IntersectionObserver((ents) => {
    for (const en of ents) {
      if (!en.isIntersecting) continue;
      io.unobserve(en.target);
      drawPdf(en.target).catch(() => fail(en.target));
    }
  }, { rootMargin: "400px" });
  canvases.forEach((c) => io.observe(c));
}
async function drawPdf(canvas) {
  const pdfjsDir = SNAP ? `${SNAP.viewer}pdfjs/` : "/pdfjs/build/";
  pdfjsP ??= import(`${pdfjsDir}pdf.min.mjs`).then((m) => { m.GlobalWorkerOptions.workerSrc = `${pdfjsDir}pdf.worker.min.mjs`; return m; });
  const pdfjs = await pdfjsP;
  const doc = await pdfjs.getDocument({ url: canvas.dataset.pdf, isEvalSupported: false }).promise;
  const page = await doc.getPage(Number(canvas.dataset.page) || 1);
  const box = canvas.parentElement.getBoundingClientRect();
  const v1 = page.getViewport({ scale: 1 });
  const cssW = Math.min(box.width || 600, v1.width * 1.6);
  const scale = (cssW / v1.width) * (window.devicePixelRatio || 1);
  const vp = page.getViewport({ scale });
  canvas.width = vp.width; canvas.height = vp.height;
  canvas.style.width = `${cssW}px`;
  await page.render({ canvasContext: canvas.getContext("2d"), viewport: vp }).promise;
}
/** What to say under an error's statement that shows no corrected text — the repair is in its proof,
 *  or there is none on file (yet) — or null: a result with no error, or one whose statement shows its
 *  correction (`corrected`). Pure. */
function proofOnlyNote(r, live, corrected) {
  if (corrected || (r.repair !== "proof" && r.repair !== "none")) return null;
  if (r.repair === "proof") return { text: "The statement stands as printed. The revision is in its proof — the revised steps are marked where the proof is printed.", unrepaired: false };
  return { text: live ? "The statement does not hold as printed. Its revision is being written." : "The statement does not hold as printed, and no revision of it is on file.", unrepaired: true };
}
function drawProofOnlyNotes() {
  $$("#paper-body .rv-proofonly").forEach((n) => n.remove());
  for (const r of P.detail?.results ?? []) {
    const el = r.label ? resEl(r.id) : null;
    const note = el?.matches(".formal") ? proofOnlyNote(r, P.detail.summary.live, Boolean(el.querySelector(".rv.ins"))) : null;
    if (note) el.insertAdjacentHTML("beforeend", `<div class="rv-proofonly${note.unrepaired ? " unrepaired" : ""}">${note.text}</div>`);
  }
}
function badge(r) {
  if (r.needs) return `<span class="pill b-error">needs you</span>`;
  if (r.bucket) return `<span class="pill ${({ verified: "b-verified", verified_with_bookkeeping: "b-vwb", conditional: "b-conditional", repaired: "b-repaired", refuted: "b-refuted" })[r.bucket] ?? "b-neutral"}">${esc(bucketWord(r.bucket))}</span>`;
  if (r.state === "error") return r.paperError?.kind === "undetermined" ? `<span class="pill b-pending">not determined</span>` : `<span class="pill b-error">error</span>`;
  if (r.state === "minor") return `<span class="pill b-pending">clarification</span>`;
  if (r.review?.correctness) return `<span class="pill b-vwb">${esc(r.review.correctness)}</span>`;
  return "";
}

/* margin comments */
function drawCards() {
  const host = $("#rail-cards");
  const comments = P.paper?.comments ?? [];
  // a reading on record is revised only while the run is at rest (the change resumes it)
  const rest = atRest(P.detail.summary);
  // a decision waiting on the owner is a card too, first, beside the statement it is about
  const now = [...P.detail.repairs.map((r) => [`repair:${r.node}`, repairCardHTML(r, P.detail)]), ...comments.map((c) => [c.id, commentCardHTML(c, rest)])];
  const had = P.cards, els = $$(".card", host);
  P.cards = new Map(now);
  if (had && now.length && P.cards.size === now.length && els.length === now.length && now.every(([id], i) => els[i].dataset.card === id)) {
    // the same cards as stand there: only those that read otherwise now are drawn again (a push
    // that touches one — an issue reported on it, a ruling — leaves the other few hundred formulas be)
    now.forEach(([id, html], i) => { if (had.get(id) !== html) swapCard(els[i], html); });
    linkedId = null; link(P.open);
  } else {
    // a long open card scrolls in place: where the reader was in it survives the redraw (a choice
    // clicked near its end must not send it back to its top)
    const was = els.map((c) => [c.dataset.card, $(".cbody", c)?.scrollTop ?? 0]).filter(([, t]) => t > 0);
    host.innerHTML = now.map(([, html]) => html).join("");
    linkedId = null; link(P.open); // the cards are new elements: the open one is marked again
    for (const [id, top] of was) {
      const c = $$(".card", host).find((x) => x.dataset.card === id); const body = c && $(".cbody", c);
      if (!body) continue;
      if (id === P.open) c.classList.add("active"); // its body scrolls only once open (`layout` keeps the class)
      body.scrollTop = top;
    }
  }
  $("#rail-count").textContent = `${comments.length} note(s)`;
  const chips = {};
  for (const c of comments) chips[CHIP[c.kind] ?? "Findings"] = (chips[CHIP[c.kind] ?? "Findings"] ?? 0) + 1;
  // most to least consequential; a symbol's reading is a clarification, a condition added to a statement its own group
  $("#chips").innerHTML = ["Findings", "Bookkeeping", "Clarifications", "Proof details"].filter((k) => chips[k]).map((k) => [k, chips[k]]).map(([k, n]) => `<button class="chip" type="button" data-chip="${k}" aria-pressed="${!P.off.has(k)}" title="${P.off.has(k) ? "Hidden — click to show" : "Click to hide"}">${k} ${n}</button>`).join("");
  filterCards();
}
/* A comment's card as the page state has it now (its reading being edited, its issue being written). */
const commentCardHTML = (c, rest) => cardHTML(c, c.env ? resultByLabel(c.env) : null, { own: P.paper.ownerReadings?.[c.id] ?? [], atRest: rest, draft: P.edit?.card === c.id ? P.edit.text : null, issue: issueOf(c), flag: P.flag?.card === c.id ? P.flag.text : null });
/* Redraw the card `id` alone — a click in one card changes that card (every decision card for a
   decision: each shows how many are decided). Drawing all of them again, a few hundred formulas,
   was the second a click took. The card keeps its place, its open state and where it was scrolled. */
function redrawCard(id) {
  const rest = atRest(P.detail.summary);
  for (const x of id.startsWith("repair:") ? P.detail.repairs.map((r) => `repair:${r.node}`) : [id]) {
    const el = cardEl(x), r = x.startsWith("repair:") ? P.detail.repairs.find((y) => `repair:${y.node}` === x) : null, c = r ? null : P.paper.comments.find((y) => y.id === x);
    if (!el || !(r || c)) { drawCards(); return; }
    const html = r ? repairCardHTML(r, P.detail) : commentCardHTML(c, rest);
    swapCard(el, html); P.cards?.set(x, html);
  }
  linkedId = null; link(P.open);
}
/* The card `el` drawn again from `html`: it keeps its place, its open state and where it was scrolled. */
function swapCard(el, html) {
  const id = el.dataset.card, top = $(".cbody", el)?.scrollTop ?? 0, cls = el.className, style = el.getAttribute("style");
  el.outerHTML = html;
  const now = cardEl(id); now.className = cls; if (style) now.setAttribute("style", style);
  const body = $(".cbody", now); if (body) body.scrollTop = top;
}
function cardHTML(c, r, o = { own: [], atRest: false, draft: null }) {
  const [tag, cls] = KIND_TAG[c.kind] ?? ["Note", ""];
  const editing = o.draft !== null && o.own.length > 0;
  return `<div class="card" data-card="${esc(c.id)}" data-kind="${esc(c.kind)}" data-chip="${CHIP[c.kind] ?? "Findings"}" ${r ? `data-node="${esc(r.id)}"` : ""} ${c.env ? `data-env="${esc(c.env)}"` : ""} tabindex="0">
    <div class="cbyline"><span class="av">PF</span><span class="cname">${c.kind === "note" ? "PaperFormalizer" : c.label}</span>${r ? `<span class="cwhen">${esc(envOf(r.id)?.heading ?? r.id)}</span>` : ""}<span class="ctag ${cls}">${esc(tag)}</span></div>
    ${editing ? "" : `<div class="cbody">${c.html}</div>`}${c.kind === "reading-owner" ? ownerReadingHTML(o) : ""}${editing || c.kind === "rewind" || c.kind === "cap" ? "" : issueHTML(o)}</div>`;
}
/* The foot of a comment that asks no decision: the owner may report an issue with it (optional — a
   note awaiting a ruling is decided instead). `issue`: the one reported on it; `flag`: the open text. */
function issueHTML({ issue = null, flag = null }) {
  if (SNAP) return ""; // (a shared paper's page reports nothing)
  if (flag !== null) return `<div class="cflag"><textarea data-flag-text rows="3" aria-label="Describe the issue" placeholder="Describe the issue">${esc(flag)}</textarea>
    <div class="cacts"><button class="btn btn-primary" type="button" data-flag="send">Send</button><button class="btn" type="button" data-flag="cancel">Cancel</button></div></div>`;
  const open = `<button class="linkbtn" type="button" data-flag="open">Report an issue</button>`;
  if (!issue) return `<div class="cflag quiet"><div class="cacts">${open}</div></div>`;
  if (issue.handled) return `<div class="cflag"><p class="cfine">Issue reported — addressed</p><div class="cacts">${open}</div></div>`;
  return `<div class="cflag"><p class="cfine">Issue reported: ${tex(issue.text, P.paper?.macros)}</p><div class="cacts"><button class="linkbtn" type="button" data-flag="edit">Edit</button><button class="linkbtn" type="button" data-flag="withdraw">Withdraw</button></div></div>`;
}
/* A reading entered for the paper's owner (often by the agent, on the owner's behalf): what it is,
   and — when the run's record holds it and the run is at rest — its Edit / Remove, or the open editor. */
function ownerReadingHTML({ own, atRest, draft }) {
  if (SNAP) return `<div class="cown"><p class="cfine">A binding reading entered for the paper's author: the formalization follows it.</p></div>`;
  const several = own.length > 1 ? ` It is pinned on ${own.length} results; a change here applies to each.` : "";
  if (draft !== null && own.length) return `<div class="cown"><textarea data-reading-text rows="5" aria-label="The reading, as TeX">${esc(draft)}</textarea>
    <p class="cfine">Written as TeX: math in <code>$…$</code>, the paper's macros.${several}</p>
    <div class="cacts"><button class="btn btn-primary" type="button" data-reading="save">Save</button><button class="btn" type="button" data-reading="cancel">Cancel</button></div></div>`;
  return `<div class="cown"><p class="cfine">A binding reading entered for the paper's author: the formalization follows it.${own.length ? ` ${atRest ? "You can edit or remove it here." : "It can be edited or removed here once the run is at rest."}${several}` : ""}</p>
    ${own.length && atRest ? `<div class="cacts"><button class="linkbtn" type="button" data-reading="edit">Edit</button><button class="linkbtn" type="button" data-reading="remove">Remove</button></div>` : ""}</div>`;
}
/* Edit / Save / Cancel / Remove on an owner's reading: a change goes out as the resume that carries it. */
function readingClick(e) {
  const b = e.target.closest("[data-reading]"); if (!b) return false;
  const card = b.closest(".card").dataset.card, own = P.paper.ownerReadings?.[card] ?? [], act = b.dataset.reading;
  const redraw = () => { redrawCard(card); activate(card, false); };
  const redo = "<p>The run then resumes: the referee re-grades the result the reading is pinned on and what depends on it, and the Lean stages redo what changed.</p>";
  const sent = (started) => { if (started) { P.edit = null; drawCards(); } };
  if (act === "edit") { P.edit = { card, text: own[0].text }; redraw(); }
  else if (act === "cancel") { P.edit = null; redraw(); }
  else if (act === "save") {
    const text = (P.edit?.text ?? "").trim();
    if (!text) toast("The reading has no text — remove it instead.", true);
    else if (own.every((r) => r.text.trim() === text)) { P.edit = null; redraw(); }
    else runAction({ kind: "edit-reading", readings: own.map((r) => ({ id: r.id, text })) }, "Change the author's reading", `<p>The reading is changed in the run's record (<code>discovery/patches.json</code>); it stays pinned where it is, and what it settled stays settled.</p>${redo}`).then(sent);
  } else if (act === "remove") {
    const reopens = own.some((r) => r.withdraws > 0) ? " A finding it had set aside is open again, for the referee to grade the statement as printed." : "";
    runAction({ kind: "remove-reading", ids: own.map((r) => r.id) }, "Remove the author's reading", `<p>The reading is removed from the run's record (<code>discovery/patches.json</code>) and no longer binds the formalization.${reopens}</p>${redo}`).then(sent);
  }
  return true;
}
/** The issue the owner reported on the comment `c`: the open one, else the last the agent acted on. */
function issueOf(c) { const on = (P.detail.objections ?? []).filter((o) => o.comment === c.key); return on.find((o) => !o.handled) ?? on.at(-1) ?? null; }
/* Report an issue / Send / Cancel / Edit / Withdraw at a comment's foot: stored for the agent, whose watcher wakes on it.
   The text box takes the focus without scrolling: the redrawn card is still easing to its place, and a
   scroll to where it stands meanwhile went to the top of the page. */
function flagClick(e) {
  const b = e.target.closest("[data-flag]"); if (!b) return false;
  const card = b.closest(".card").dataset.card, act = b.dataset.flag;
  const c = P.paper.comments.find((x) => x.id === card), issue = c && issueOf(c), open = issue && !issue.handled ? issue : null;
  const redraw = () => { redrawCard(card); activate(card, false); };
  const send = (body, said) => post(`/api/runs/${encodeURIComponent(S.slug)}/objection`, body).then(() => { P.flag = null; toast(said); onChange(`run:${S.slug}`); }, (err) => toast(err.message, true));
  if (!c) return true;
  if (act === "open" || act === "edit") { P.flag = { card, text: act === "edit" ? open?.text ?? "" : "" }; redraw(); $("[data-flag-text]", cardEl(card))?.focus({ preventScroll: true }); }
  else if (act === "cancel") { P.flag = null; redraw(); }
  else if (act === "withdraw") { if (open) send({ id: open.id, withdraw: true }, "Withdrawn"); }
  else if (!(P.flag?.text ?? "").trim()) toast("Describe the issue.", true);
  else send(open ? { id: open.id, text: P.flag.text } : { comment: c.key, text: P.flag.text }, P.detail.summary.orch ? "Sent — the agent acts on it" : "Recorded — an agent acts on it once one is attached");
  return true;
}
function filterCards() { $$("#rail-cards .card").forEach((c) => c.classList.toggle("hidden-by-filter", P.off.has(c.dataset.chip))); layout(); }

function wirePaper() {
  $("#markup").addEventListener("click", (e) => {
    const b = e.target.closest("[data-m]"); if (!b) return;
    $$("#markup button").forEach((x) => x.setAttribute("aria-pressed", String(x === b)));
    const pv = $("#pv"); pv.classList.remove("m-all", "m-simple", "m-original"); pv.classList.add(`m-${b.dataset.m}`);
    layout();
  });
  $("#chips").addEventListener("click", (e) => { const c = e.target.closest("[data-chip]"); if (!c) return; P.off.has(c.dataset.chip) ? P.off.delete(c.dataset.chip) : P.off.add(c.dataset.chip); c.setAttribute("aria-pressed", String(!P.off.has(c.dataset.chip))); filterCards(); });
  $("#prev-c").addEventListener("click", () => step(-1));
  $("#next-c").addEventListener("click", () => step(1));
  $("#paper-body").addEventListener("click", (e) => {
    const mk = e.target.closest(".cmark"); if (mk) { e.stopPropagation(); activate(mk.dataset.c, false); return; }
    if (P.open && !e.target.closest("a, button, summary")) { P.open = null; link(null); layout(); }
    if (e.target.closest("a, .rv-fold > summary")) return; // a link goes where it points and a fold opens, not into the drawer
    // a result's block opens its drawer: a prose result's button or a corollary's block (`data-res`), an environment
    const rb = e.target.closest("[data-res]"); if (rb) { openDrawer(rb.dataset.res); return; }
    const f = e.target.closest(".formal[data-label]"), r = f && resultByLabel(f.dataset.label); if (r) openDrawer(r.id); else if (f) openBlockDrawer(f);
  });
  $("#rail-cards").addEventListener("input", (e) => {
    const t = e.target.closest("[data-rtext]"); const entry = t?.closest("[data-repair]"); if (entry && P.repair[entry.dataset.repair]) P.repair[entry.dataset.repair].text = t.value;
    const rt = e.target.closest("[data-reading-text]"); if (rt && P.edit) P.edit.text = rt.value;
    const ft = e.target.closest("[data-flag-text]"); if (ft && P.flag) P.flag.text = ft.value;
  });
  $("#rail-cards").addEventListener("click", (e) => {
    if (repairClick(e) || readingClick(e) || flagClick(e)) return;
    // the reading pane's own controls: the comment before or after (the paper goes to its passage), or close
    const pn = e.target.closest("[data-pane]"); if (pn) { if (pn.dataset.pane === "close") fold(); else step(pn.dataset.pane === "next" ? 1 : -1); return; }
    if (e.target.closest("summary, button, a, textarea")) { setTimeout(layout, 30); return; }
    // beside the paper a card's click goes to its passage; listed under it (a narrow window) the first
    // click opens the card where it is, to be read, and the next goes to the passage
    const card = e.target.closest(".card"); if (!card) return;
    // the open card closes on a click of its heading (its text is read and selected, not a switch)
    if (P.open === card.dataset.card) { if (e.target.closest(".cbyline, .cpane")) fold(); return; }
    activate(card.dataset.card, wide());
  });
  $("#rail-cards").addEventListener("mouseover", (e) => { const c = e.target.closest(".card"); link(c ? c.dataset.card : P.open); });
  $("#toc").addEventListener("click", (e) => { const a = e.target.closest("a[data-sec]"); if (!a) return; e.preventDefault(); const t = document.getElementById(a.dataset.sec); if (t) reveal(t); });
  $("#article").addEventListener("click", async (e) => {
    if (e.target.id === "stop-run") {
      if (!(await confirmRun("Stop the run", `<p>The runner stops its workers and the run can be resumed later.</p>`, "Stop"))) return;
      try { await post(`/api/runs/${encodeURIComponent(S.slug)}/action`, { action: { kind: "stop" } }); toast("Stopping…"); } catch (err) { toast(err.message, true); }
    }
    // within the page: the address hash is the route, so a plain `#id` link would leave the paper
    const jump = e.target.closest("[data-jump]");
    if (jump) {
      const to = document.getElementById(jump.dataset.jump);
      if (to) reveal(to, "start");
      else (document.scrollingElement ?? document.documentElement).scrollTo({ top: 1e9, behavior: "smooth" });
      return;
    }
    const go = e.target.closest("[data-goto]");
    if (go) { jumpTo(go.dataset.goto); activate(`repair:${go.dataset.goto}`, false); return; }
    if (e.target.id === "repair-recs") { acceptRepairRecs(); return; }
    if (e.target.id === "resume-plain") runAction({ kind: "resume" }, "Resume the run");
    if (e.target.id === "share-run") { shareRun(); return; }
    if (e.target.id === "orch-how") { await confirmRun("Attach an agent session", noOrchHTML(S.slug), "OK"); return; }
    const mg = e.target.closest("[data-msg]");
    if (mg) {
      const act = mg.dataset.msg;
      // (what is being written is kept: the box moves — to a request, back under the thread — its words and files with it)
      if (act === "hide" || act === "show") { setThreadHidden(act === "hide"); drawStatus(); }
      else if (act === "open") { setThreadHidden(false); P.msg.re = mg.dataset.re ?? null; drawStatus(); const ta = $("#status [data-msg-text]"); ta?.focus(); ta?.scrollIntoView({ block: "nearest" }); }
      else if (act === "cancel") { P.msg = blankMsg(); drawStatus(); }
      else if (act === "unfile") { P.msg.files.splice(Number(mg.dataset.i), 1); drawStatus(); }
      else if (act === "clear" || act === "clear-anyway") clearConversation(act === "clear-anyway");
      else if (act === "clear-keep") { P.clearAsk = null; drawStatus(); }
      else if (act === "send") sendMessage();
      // (a chooser of its own: the box is drawn again while a run is live, and would take the answer with it)
      else if (act === "attach") { const i = Object.assign(document.createElement("input"), { type: "file", multiple: true, accept: MSG_LIMITS.ext.join(",") }); i.onchange = () => attachFiles([...i.files]); i.click(); }
      return;
    }
    const dm = e.target.closest("[data-dismiss]");
    if (dm) {
      try { await post(`/api/runs/${encodeURIComponent(S.slug)}/dismiss`, { id: dm.dataset.dismiss }); onChange(`run:${S.slug}`); } catch (err) { toast(err.message, true); }
      return;
    }
    const rv = e.target.closest("[data-review]");
    if (rv) {
      const box = rv.closest(".review"), ask = box.querySelector(".ask"), act = rv.dataset.review;
      if (act === "reject") { ask.hidden = false; ask.querySelector("textarea").focus(); return; }
      if (act === "cancel") { ask.hidden = true; return; }
      const guidance = ask.querySelector("textarea").value.trim();
      if (act === "send" && !guidance) { toast("Say what the agent should do instead.", true); return; }
      try {
        await post(`/api/runs/${encodeURIComponent(S.slug)}/review`, { id: box.dataset.rid, verdict: act === "send" ? "reject" : "approve", guidance });
        toast(act === "send" ? (P.detail.summary.orch ? "Sent — the agent acts on it" : "Recorded — an agent acts on it once one is attached") : "Approved");
        onChange(`run:${S.slug}`);
      } catch (err) { toast(err.message, true); }
    }
  });
  // the message being written: its words, and the files chosen or dropped on its box
  $("#status").addEventListener("input", (e) => { if (e.target.matches("[data-msg-text]")) P.msg.text = e.target.value; });
  $("#status").addEventListener("dragover", (e) => { if (e.target.closest("[data-compose]")) e.preventDefault(); });
  $("#status").addEventListener("drop", (e) => { if (e.target.closest("[data-compose]")) { e.preventDefault(); attachFiles([...e.dataTransfer.files]); } });
  $("#pm-marks").addEventListener("click", (e) => { const g = e.target.closest("[data-pm]"); if (g && e.detail < 2) selectNode(P.sel === g.dataset.pm ? null : g.dataset.pm); });
  $("#pm-marks").addEventListener("keydown", (e) => { const g = e.target.closest("[data-pm]"); if (g && e.key === "Enter") { selectNode(g.dataset.pm); jumpTo(g.dataset.pm); } });
  $("#pm-marks").addEventListener("dblclick", (e) => { const g = e.target.closest("[data-pm]"); if (g) { selectNode(g.dataset.pm); jumpTo(g.dataset.pm); } });
  $("#pm-card").addEventListener("click", (e) => {
    if (e.target.closest("[data-x]")) return selectNode(null);
    const go = e.target.closest("[data-pmgo]"); if (go) return selectNode(go.dataset.pmgo);
    const to = e.target.closest("[data-pmto]"); if (to) return jumpTo(to.dataset.pmto);
    const det = e.target.closest("[data-pmdet]"); if (det) openDrawer(det.dataset.pmdet);
  });
  $("#promo").addEventListener("click", promoClick);
  $("#promo").addEventListener("input", (e) => { const i = e.target.closest("[data-edit]"); if (i) { const id = i.dataset.edit; const cur = P.promo[id] ?? P.detail.promotion.decisions[id] ?? {}; P.promo[id] = { ...cur, kind: "accept_with_edits", edits: { ...cur.edits, target_module: i.value } }; } });
}

/* margin layout: each card beside its anchor, pushed past the one above */
const wide = () => window.matchMedia("(min-width: 1261px)").matches;
let MARKS = null; // the paper's comment marks by id, rebuilt with the paper body
let ENVS = null; // … and its labelled environments by label (the first of a label): looked up per card at every layout
/** The environment labelled `label`: the paper's, else — none there — one anywhere on the page. */
function envEl(label) {
  if (!ENVS) { ENVS = new Map(); for (const f of $$("#paper-body .formal[data-label]")) if (!ENVS.has(f.dataset.label)) ENVS.set(f.dataset.label, f); }
  return ENVS.get(label) ?? document.querySelector(`.formal[data-label="${CSS.escape(label)}"]`);
}
const markOf = (id) => (MARKS ??= new Map($$("#paper-body .cmark").map((m) => [m.dataset.c, m]))).get(id) ?? null;
const cardEl = (id) => (id ? $(`#rail-cards [data-card="${CSS.escape(id)}"]`) : null);
/* What a card is about: a note's mark in the text; a decision's statement. */
function anchorOf(card) { return card.dataset.anchor ? document.getElementById(card.dataset.anchor) : markOf(card.dataset.card); }
/* The environment a card's note stands at: its result's, or — a note on a definition or an
   assumption, which is no result — the labelled environment itself. */
function envElOf(card) {
  if (card.dataset.node) return resEl(card.dataset.node);
  return card.dataset.env ? envEl(card.dataset.env) : null;
}
/** How far below the end of its environment a note's mark may stand and still be read with it (px):
 *  its proof and its other notes come between. */
const NOTE_REACH = 2600;
/** Does a note sit at its environment? Its mark is `inside` it, or `below` its end by less than the reach. Pure. */
const sitsAtEnv = (inside, below) => inside || (below > -2 && below < NOTE_REACH);
/* Where a card sits, and what a click on it brings into view (`el`): a note on a result is written
   under the statement and its corrected text, and is read against the statement — so the notes of
   one environment gather at its top (`env`); a note on running text sits where its paragraph begins. */
function placeOf(card, rect = (el) => el.getBoundingClientRect()) {
  const a = anchorOf(card), env = a && envElOf(card);
  if (!a) return { el: null, env: null };
  if (env && sitsAtEnv(env.contains(a), rect(a).top - rect(env).bottom)) return { el: env, env };
  return { el: a.closest(".p") ?? a, env: null };
}
/** The tops of cards down a rail, from where each wants to be (`want`: px, null: anywhere) and its
 *  height `h`, `gap` apart: the open card `k` (-1: none) sits exactly at its place and the others give
 *  way after it and before it; with no room above, all keep their order from the top. Pure. */
function cardTops(cards, k, gap) {
  const tops = cards.map(() => 0);
  const down = (from, y) => { for (let i = from; i < cards.length; i++) { tops[i] = Math.max(cards[i].want ?? y, y); y = tops[i] + cards[i].h + gap; } };
  if (k < 0) { down(0, 0); return tops; }
  tops[k] = cards[k].want; down(k + 1, tops[k] + cards[k].h + gap);
  for (let i = k - 1, y = tops[k] - gap; i >= 0; i--) { tops[i] = Math.min(cards[i].want ?? y, y - cards[i].h); y = tops[i] - gap; }
  if (k > 0 && tops[0] < 0) down(0, 0);
  return tops;
}
/* Margin layout, as in a word processor's comment rail: the open card sits exactly beside its mark
   and the others give way above and below it. Cards not open show their first lines only; two or
   more on one paragraph fold into a stack (the most important on top) that opens with any of them. */
const KIND_RANK = { note: 1, rewind: 2, cap: 2, "reading-owner": 3, reading: 4, condition: 4, "reading-symbol": 5, detail: 6 };
function layout() {
  const host = $("#rail-cards"); if (!host) return;
  const cards = $$(".card", host);
  // a narrow window lists the cards under the paper: no places, no stacks — the open one still opens
  if (!wide()) { cards.forEach((c) => { c.style.transform = ""; c.classList.remove("stack", "stacked"); c.classList.toggle("active", c.dataset.card === P.open); }); host.style.height = ""; return; }
  // a pane just closed is measured and placed as the card it is again
  for (const c of cards) if (c.classList.contains("pinned") && c.dataset.card !== P.open) { c.classList.remove("pinned"); c.style.maxHeight = ""; }
  const base = host.getBoundingClientRect().top;
  // 1. which cards show: group the ones that sit at one environment or paragraph (reads only, no layout
  // change yet: an element many cards sit at is measured once)
  const rects = new Map(), rect = (el) => rects.get(el) ?? rects.set(el, el.getBoundingClientRect()).get(el);
  const items = cards.filter((c) => !c.classList.contains("hidden-by-filter")).map((c) => {
    const { el, env } = placeOf(c, rect);
    return { c, block: env ?? (el ? el.closest("#paper-body > *") ?? el : null), t: el ? rect(el).top - base : 1e9 };
  }).sort((x, y) => x.t - y.t);
  const groups = [];
  for (const it of items) {
    const g = groups.at(-1);
    if (g && it.block && g[0].block === it.block) g.push(it); else groups.push([it]);
  }
  // 2. classes (the one write before measuring)
  const shown = [];
  for (const g of groups) {
    const open = g.length < 2 || g.some((it) => it.c.dataset.card === P.open);
    const head = open ? null : [...g].sort((x, y) => (KIND_RANK[x.c.dataset.kind] ?? 9) - (KIND_RANK[y.c.dataset.kind] ?? 9))[0];
    for (const it of g) {
      // the open card is the reading pane (`pinOpen`): its strip says which comment it is, of all and
      // of those on its passage, and steps to the next
      const at = it.c.dataset.card === P.open ? g.indexOf(it) : -1, sw = it.c.querySelector(":scope > .cpane");
      const html = at < 0 ? "" : `<button type="button" data-pane="prev" aria-label="Previous comment" title="Previous comment">‹</button><span>${items.indexOf(it) + 1} of ${items.length}${g.length > 1 ? ` · ${at + 1} of ${g.length} on this passage` : ""}</span><button type="button" data-pane="next" aria-label="Next comment" title="Next comment">›</button><button type="button" data-pane="close" aria-label="Close" title="Close (Esc)">✕</button>`;
      if (at < 0) sw?.remove(); else if (sw) { if (sw.innerHTML !== html) sw.innerHTML = html; } else it.c.insertAdjacentHTML("afterbegin", `<div class="cpane">${html}</div>`);
      it.c.classList.toggle("active", it.c.dataset.card === P.open);
      it.c.classList.toggle("stack", it === head);
      it.c.classList.toggle("stacked", Boolean(head) && it !== head);
      if (it === head) it.c.dataset.more = String(g.length - 1);
      if (open || it === head) shown.push({ ...it, t: g[0].t });
    }
  }
  // 3. measure
  for (const it of shown) {
    it.h = it.c.offsetHeight + (it.c.classList.contains("stack") ? 8 : 0);
    const body = it.c.querySelector(".cbody"); it.clip = Boolean(body) && body.scrollHeight > body.clientHeight + 1;
    it.want = it.t === 1e9 ? null : Math.max(0, it.t - 6);
  }
  // 4. place
  const tops = cardTops(shown, shown.findIndex((it) => it.c.dataset.card === P.open && it.want !== null), 10);
  let end = 0;
  shown.forEach((it, i) => { it.c.style.transform = `translateY(${tops[i]}px)`; it.c.classList.toggle("clip", it.clip); end = Math.max(end, tops[i] + it.h); });
  host.style.height = `${end}px`;
  pinOpen();
}
/* The open card is a reading pane: it fills the margin column of the window, from under the bars that
   stay at the top to near the bottom, and stays there while the paper scrolls beside it — a long comment
   scrolls inside it. The other cards are out of sight meanwhile (their marks in the text stay, and open
   them); closing it brings them back beside their passages. */
function pinOpen() {
  const host = $("#rail-cards"); if (!host) return;
  const card = wide() ? cardEl(P.open) : null, on = Boolean(card) && !card.classList.contains("hidden-by-filter");
  for (const c of $$(".card.pinned", host)) if (!on || c !== card) { c.classList.remove("pinned"); c.style.maxHeight = ""; }
  host.classList.toggle("reading", on);
  if (!on) return;
  const bars = ($(".topbar")?.offsetHeight ?? 0) + ($(".rtool")?.offsetHeight ?? 0) + 12;
  card.classList.add("pinned");
  card.style.maxHeight = `${Math.max(240, window.innerHeight - bars - 16)}px`;
  const top = host.getBoundingClientRect().top, floor = ($("#paper-body")?.getBoundingClientRect().bottom ?? top + host.offsetHeight) - top - card.offsetHeight;
  card.style.transform = `translateY(${Math.max(0, Math.min(bars - top, floor))}px)`;
}
let pinFrame = 0;
window.addEventListener("scroll", () => { if (P?.open && !pinFrame) pinFrame = requestAnimationFrame(() => { pinFrame = 0; pinOpen(); }); }, { passive: true });
/* Close the open card: it and the others go back beside their passages. */
function fold() { P.open = null; link(null); layout(); $("#c-pos").textContent = "—"; }
let rz; const relayout = () => { clearTimeout(rz); rz = setTimeout(layout, 120); };
window.addEventListener("resize", relayout);
// off-screen parts of the paper render on demand (content-visibility) and settle their height then
if (window.ResizeObserver) new ResizeObserver(relayout).observe(app);
let linkedId = null;
function link(id) {
  if (id === linkedId) return;
  linkedId = id;
  $$(".linked").forEach((x) => x.classList.remove("linked"));
  if (!id) return;
  const card = cardEl(id);
  card?.classList.add("linked");
  (card && anchorOf(card))?.classList.add("linked");
}
/* Open a card. From the card itself (or the ↑ ↓ buttons) the paper goes to what the card is read
   against; from its mark in the paper the paper stays, and the card comes beside it. */
function activate(id, fromCard) {
  P.open = id; link(id);
  const card = cardEl(id), el = fromCard && card ? placeOf(card).el : null;
  if (el) reveal(el, "start");
  layout(); // beside its mark on a wide screen
  if (!fromCard && !wide() && card) card.scrollIntoView({ behavior: "smooth", block: "center" });
  const ids = visibleCardIds(); const i = ids.indexOf(id); $("#c-pos").textContent = ids.length ? `${i < 0 ? "—" : i + 1} / ${ids.length}` : "—";
}
/** The cards shown, in the order they sit down the rail. */
function visibleCardIds() {
  const rects = new Map(), rect = (el) => rects.get(el) ?? rects.set(el, el.getBoundingClientRect()).get(el);
  return $$("#rail-cards .card").filter((c) => !c.classList.contains("hidden-by-filter")).map((c) => ({ id: c.dataset.card, el: placeOf(c, rect).el })).filter((x) => x.el)
    .map((x) => ({ id: x.id, t: rect(x.el).top })).sort((x, y) => x.t - y.t).map((x) => x.id);
}
function step(d) {
  const ids = visibleCardIds(); if (!ids.length) return;
  let i = ids.indexOf(P.open); i = i < 0 ? (d > 0 ? 0 : ids.length - 1) : (i + d + ids.length) % ids.length;
  activate(ids[i], true);
}

/* proof map: layered from the core's dependencies, implied edges left out */
function drawMap() {
  const rs = P.detail.results.filter((r) => /theorem|lemma|proposition|corollary/.test(r.kind));
  const ids = new Set(rs.map((r) => r.id));
  const uses = Object.fromEntries(rs.map((r) => [r.id, r.deps.filter((d) => ids.has(d))]));
  const reach = (a, b, skip, seen = new Set()) => (uses[a] || []).some((m) => !(a === skip[0] && m === skip[1]) && !seen.has(m) && (seen.add(m), m === b || reach(m, b, skip, seen)));
  const edges = rs.flatMap((r) => uses[r.id].filter((b) => !reach(r.id, b, [r.id, b])).map((b) => [r.id, b]));
  const layer = {}; const L = (id, st = new Set()) => { if (layer[id] !== undefined) return layer[id]; if (st.has(id)) return 0; st.add(id); const u = uses[id]; layer[id] = u.length ? 1 + Math.max(...u.map((x) => L(x, st))) : 0; return layer[id]; };
  rs.forEach((r) => L(r.id));
  const maxL = Math.max(0, ...Object.values(layer));
  const W = 260, CW = 56, CH = 18, PER = 4, RH = 36; // four to a row: room for "Prop D.10"
  const rowsOf = [];
  for (let l = maxL; l >= 0; l--) { const at = rs.filter((r) => layer[r.id] === l).map((r) => r.id); for (let k = 0; k < at.length; k += PER) rowsOf.push(at.slice(k, k + PER)); }
  const pos = {};
  rowsOf.forEach((row, ri) => { row.forEach((id, k) => { pos[id] = [((k + 0.5) * W) / row.length, 14 + ri * RH]; }); });
  const H = 14 + rowsOf.length * RH;
  $("#pm-svg").setAttribute("viewBox", `0 0 ${W} ${Math.max(H, 30)}`);
  const fit = (t) => (t.length > 10 ? `${t.slice(0, 9)}…` : t);
  // as the paper names it (Thm 2, Lem 1); a result the page cannot place keeps its kind
  // a corollary a repair split off has no number of its own: it is named after its result, also before the paper shows its block
  const split = (r) => shortHeading(splitHeading(r));
  // a citation a proof invokes is named by its citation ([Ber]); it has no environment of its own
  const label = (r) => { if (r.citedIn) return fit(`[${r.cites}]`); const h = r.splitFrom ? null : envOf(r.id)?.heading ?? P.paper?.anchorHeadings?.[r.id]; return fit(r.splitFrom ? split(r) : h ? shortHeading(h) : `${shortHeading(r.kind.charAt(0).toUpperCase() + r.kind.slice(1))} ?`); };
  MAP_USES = uses;
  // an arrow reads "used by": from a result up to the one whose proof uses it
  const svgE = edges.map(([a, b]) => { const [x1, y1] = pos[a], [x2, y2] = pos[b]; return `<path class="pm-edge" data-a="${esc(a)}" data-b="${esc(b)}" marker-end="url(#pm-a)" d="M${x2},${y2 - CH / 2} C${x2},${y2 - CH / 2 - 10} ${x1},${y1 + CH / 2 + 10} ${x1},${y1 + CH / 2 + 1}"></path>`; }).join("");
  const svgN = rs.map((r) => { const [x, y] = pos[r.id]; const cls = ["pm-node", `st-${r.state}`, r.key ? "pm-top" : "", r.needs ? "needs" : "", r.proved ? "lean" : ""].join(" "); return `<g class="${cls}" data-pm="${esc(r.id)}" tabindex="0" role="button"><title>${esc(envOf(r.id)?.heading ?? (r.splitFrom ? splitHeading(r) : r.id))}</title><rect x="${x - CW / 2}" y="${y - CH / 2}" width="${CW}" height="${CH}" rx="5"></rect><text x="${x}" y="${y + 3}" text-anchor="middle">${esc(label(r))}</text><circle class="pm-need" cx="${x - CW / 2 + 1}" cy="${y - CH / 2 + 1}" r="3.4"></circle><circle class="pm-lean" cx="${x + CW / 2 - 3.5}" cy="${y - CH / 2 + 3.5}" r="2.2"></circle></g>`; }).join("");
  // a citation the paper's proof invokes and the proof as it now stands (after a repair) does not use
  const svgD = rs.filter((r) => citedDropped(r) && pos[r.citedIn]).map((r) => { const [x1, y1] = pos[r.citedIn], [x2, y2] = pos[r.id]; return `<path class="pm-edge pm-dropped" data-a="${esc(r.citedIn)}" data-b="${esc(r.id)}" d="M${x2},${y2 - CH / 2} C${x2},${y2 - CH / 2 - 10} ${x1},${y1 + CH / 2 + 10} ${x1},${y1 + CH / 2 + 1}"><title>The paper's proof invokes this citation; the proof as corrected does not use it.</title></path>`; }).join("");
  $("#pm-marks").innerHTML = svgE + svgD + svgN;
  paintMap();
}
/* Selection only restyles the map: rebuilding it under the pointer would cost the double-click its
   second click (the browser counts clicks on one element). */
let MAP_USES = {};
function paintMap() {
  const sel = P.sel, uses = MAP_USES;
  const rel = sel ? new Set([sel, ...(uses[sel] || []), ...Object.keys(uses).filter((k) => uses[k].includes(sel))]) : null;
  for (const g of $$("#pm-marks [data-pm]")) { g.classList.toggle("is-sel", g.dataset.pm === sel); g.classList.toggle("is-dim", Boolean(rel) && !rel.has(g.dataset.pm)); }
  for (const e of $$("#pm-marks .pm-edge")) { const { a, b } = e.dataset; e.classList.toggle("is-cites", Boolean(sel) && a === sel); e.classList.toggle("is-citedby", Boolean(sel) && b === sel); e.classList.toggle("is-dim", Boolean(sel) && a !== sel && b !== sel); }
  if (sel) drawMapCard(); else $("#pm-card").hidden = true;
}
function selectNode(id) { P.sel = id; paintMap(); }
function drawMapCard() {
  const r = resultById(P.sel); if (!r) { $("#pm-card").hidden = true; return; }
  const usedBy = P.detail.results.filter((x) => x.deps.includes(r.id));
  const chips = (xs) => xs.length ? xs.map((x) => `<button type="button" data-pmgo="${esc(x.id ?? x)}">${esc(envOf(x.id ?? x)?.heading ?? (x.id ?? x))}</button>`).join("") : `<span class="none">none</span>`;
  $("#pm-card").innerHTML = `<div style="display:flex;justify-content:space-between"><b>${esc(envOf(r.id)?.heading ?? r.id)}</b><button class="linkbtn" type="button" data-x>✕</button></div><div>${badge(r)}</div>
    <div style="margin-top:0.35rem"><span class="mono" style="font-size:0.6rem;color:var(--ink-faint)">ITS PROOF USES</span><div class="pm-chips">${chips(r.deps.map(resultById).filter(Boolean))}</div></div>
    <div style="margin-top:0.35rem"><span class="mono" style="font-size:0.6rem;color:var(--ink-faint)">USED BY</span><div class="pm-chips">${chips(usedBy)}</div></div>
    <div class="acts">${envOf(r.id) ? `<button class="linkbtn" type="button" data-pmto="${esc(r.id)}">go to statement ↓</button>` : ""}<button class="linkbtn" type="button" data-pmdet="${esc(r.id)}">details</button></div>`;
  $("#pm-card").hidden = false;
}
/* To a result's place in the paper; one the page cannot place opens its drawer instead. */
function jumpTo(id) {
  const el = resEl(id);
  if (el) goTo(el); else openDrawer(id);
}
// to where the block begins — its heading on the first line under the pinned bars: centring a tall block hides it
function goTo(el) { reveal(el, "start"); el.classList.add("flash"); setTimeout(() => el.classList.remove("flash"), 1200); }
/** The id a link points at within the page (`#lbl-…`), or null. Pure. */
const inPageId = (href) => /^#([^/].*)$/.exec(href ?? "")?.[1] ?? null;
// A link within the page (a `\ref`, in the paper, a note or the drawer) is followed here: the address
// hash is the route, so the browser following it would leave the paper.
document.addEventListener("click", (e) => {
  if (e.defaultPrevented) return;
  const id = inPageId(e.target.closest?.("a[href]")?.getAttribute("href")); if (!id) return;
  e.preventDefault();
  const to = document.getElementById(id);
  if (to) goTo(to.closest(".eq") ?? to);
});
/* The paper's off-screen parts take an estimated height until drawn (content-visibility), so a smooth
   scroll lands short as they are drawn under it: jump, then re-aim once the parts around have settled. */
let revealRun = 0;
function reveal(el, block = "start") {
  const run = ++revealRun;
  // "start" is just under what stays pinned at the top of the window: the top bar and the review toolbar
  const pinned = () => ($(".topbar")?.offsetHeight ?? 0) + ($(".rtool")?.offsetHeight ?? 0) + 10;
  const go = () => { if (block === "start") window.scrollBy(0, el.getBoundingClientRect().top - pinned()); else el.scrollIntoView({ block }); };
  go();
  let want = el.getBoundingClientRect().top, still = 0, frames = 0;
  const check = () => {
    if (run !== revealRun) return; // the reader scrolled, or another jump began
    const t = el.getBoundingClientRect().top;
    if (Math.abs(t - want) > 1) { go(); want = el.getBoundingClientRect().top; still = 0; } else still++;
    if (still < 4 && ++frames < 60) requestAnimationFrame(check);
  };
  requestAnimationFrame(check);
}
for (const ev of ["wheel", "touchstart"]) window.addEventListener(ev, () => { revealRun++; }, { passive: true });
window.addEventListener("keydown", (e) => { if (/^(Page|Arrow|Home|End| )/.test(e.key)) revealRun++; });

/* drawer */
function openDrawer(id) {
  const r = resultById(id); if (!r) return;
  P.drawer = id; P.drawn.drawer = JSON.stringify(r);
  xlClear();
  const at = resEl(id), e = envOf(id);
  $$("#paper-body .open").forEach((f) => f.classList.remove("open"));
  at?.classList.add("open");
  const m = P.paper?.macros;
  $("#d-kind").textContent = r.kind; $("#d-title").textContent = e?.heading ?? r.id;
  const page = r.label ? P.paper?.pages?.[r.label] : null;
  $("#d-sub").innerHTML = `${esc(r.id)}${P.paper?.pdf ? ` · <a href="${esc(P.paper.pdf)}${page ? `#page=${encodeURIComponent(page)}` : ""}" target="_blank" rel="noopener">view in the PDF${page ? `, page ${esc(page)}` : ""}</a>` : ""}`;
  const g = (lbl, v) => v ? `<span class="pill ${v === "ok" ? "b-verified" : v === "error" ? "b-error" : v === "pinned" ? "b-pending" : "b-vwb"}">${lbl} ${esc(v)}</span>` : "";
  let lean = "";
  const gate = citedDef(r);
  if (r.lean) {
    lean = `<dl class="kv"><dt>declaration</dt><dd><code>${esc(r.lean.decl)}</code></dd><dt>file</dt><dd>${SNAP?.leanDir ? `<a href="${esc(`${SNAP.leanDir}/${r.lean.file}`)}" target="_blank" rel="noopener">` : ""}<code>${esc(r.lean.file)}${r.lean.line ? `:${esc(r.lean.line)}` : ""}</code>${SNAP?.leanDir ? "</a>" : ""}</dd>${r.axioms ? `<dt>axioms</dt><dd>${esc(r.axioms.join(", "))}</dd>` : ""}</dl>`;
    if (r.rows) {
      // As on a library page: the paper's statement once, its phrases linked to the Lean rows that
      // state them; the rows below it, one hypothesis to a row. Hover (or click, to keep it) a row
      // and its phrases light up, and the other way round.
      const segs = r.segments ?? [];
      const un = new Set(r.uncovered ?? []);
      // The phrases a row states light up in the paper itself (`xlLocate`), never repeated here.
      // its environment, or — a corollary a repair split off — its own block; a result stated in prose has no block
      const found = xlLocate(resEl(r.id), segs);
      // links on file that are not shown, and how they come back: F5 again, or `relink` for this result
      const relink = `<code>paperformalizer relink ${esc(S.slug)} --toolkit &lt;toolkit&gt; --only ${esc(r.id)}</code>`;
      const nl = r.linksStale === "truncated" ? `<p class="stmt-note">The links on file were written against this statement cut short (an older reader stopped before its end), so none is shown. ${relink} links the whole statement again.</p>`
        : r.linksStale === "recut" ? `<p class="stmt-note">The links on file were written by an earlier link step for rows that are not this statement's rows now (it changed since, or that step cut it otherwise), so none is shown. They return when F5 runs again, or with ${relink}.</p>`
        : r.linksStale ? `<p class="stmt-note">The links on file were written for an earlier version of this statement, so none is shown. They return when F5 runs again, or with ${relink}.</p>`
        : r.linksUnanswered ? `<p class="stmt-note">F5 asked these rows, but no answer came back: none is linked. ${relink} asks again.</p>`
        : xlNote(segs, found);
      const rowHTML = (row) => `<div class="srow ${row.kind === "conclusion" ? "concl" : row.kind === "instance" ? "side" : "hyp"} ${row.unstated && segs.length ? "unstated" : ""}" data-binder="${esc((row.segments ?? []).join(" "))}"><div class="sl">${row.kind === "binder" ? `<span class="sn">${esc(row.names)}</span><span class="sc">:</span>` : row.kind === "conclusion" && row.id.startsWith("⊢") ? `<span class="sn" title="what the result concludes">then</span>` : ""}<span class="st">${leanLayoutHTML(row.lean)}</span></div>${row.unstated && segs.length && row.kind !== "instance" ? `<span class="rtag">not in the paper's text</span>` : ""}</div>`;
      // binders first; then each clause of the conclusion with the hypotheses it states for itself
      const hyps = r.rows.filter((row) => row.kind === "binder" || row.kind === "instance");
      const clauses = new Map();
      for (const row of r.rows) if (row.kind === "premise" || row.kind === "conclusion") { const k = row.id.startsWith("⊢") ? row.id.split(".")[0] : "⊢"; (clauses.get(k) ?? clauses.set(k, []).get(k)).push(row); }
      const clauseHTML = [...clauses].map(([k, rows]) => `<div class="stmt-lbl">${clauses.size > 1 ? `claim ${esc(k.replace("⊢", ""))}` : "conclusion"}${rows.some((x) => x.kind === "premise") ? " — its hypotheses, then what it concludes" : ""}</div>${rows.map(rowHTML).join("")}`).join("");
      // the statement as it now stands: nested (hypothesis rows over clause cards), or flat rows when it does not structure
      if (P.foldsOf !== id) { P.folds = new Set(); P.foldsOf = id; }
      const stmt = r.leanView ? dsViewHTML(r.leanView, { terms: DS_TERMS.theorem, linked: segs.length > 0, found: found ? new Set(XLP.ranges.keys()) : null, whole: XLP.whole, path: "", depth: 0, n: { k: 0 } }) : `<div class="stmt">${hyps.length ? `<div class="stmt-lbl">hypotheses</div>${hyps.map(rowHTML).join("")}` : ""}${clauseHTML}</div>`;
      lean += `<div class="xlscope">${nl}${stmt}${un.size ? `<p class="stmt-note">Phrases shown faint are stated by no Lean row.</p>` : ""}${!segs.length && !r.linksStale ? `<p class="stmt-note">F5 links these rows to the paper's words when it runs (nl_links.json).</p>` : ""}</div>`;
    }
    else if (r.leanMissing) lean += `<p class="stmt-note">The file no longer holds this declaration (it was renamed, moved or removed since the report): no statement to show.</p>`;
  } else if (r.umbrella) {
    // An umbrella has no declaration of its own: it holds exactly when its propositions do.
    const bs = (r.blocks ?? []).map(resultById).filter(Boolean);
    lean = `<p>Established through its propositions: it has no Lean declaration of its own and holds exactly when all of them do${bs.length ? ` (${bs.filter((b) => b.proved).length} of ${bs.length} proved in Lean)` : ""}.${r.axioms ? ` Axioms of the propositions together: ${esc(r.axioms.join(", ") || "none")}.` : ""}</p>
      <ul class="conds umb-blocks">${bs.map((b) => `<li><button class="linkbtn" type="button" data-umbgo="${esc(b.id)}">${esc(envOf(b.id)?.heading ?? b.id)}</button> ${badge(b) || `<span class="pill b-neutral">${b.proved ? "proved" : b.lean ? "not proved yet" : "not formalized yet"}</span>`}${b.lean ? ` <code>${esc(b.lean.decl)}</code>` : ""}</li>`).join("")}</ul>`;
  } else if (gate) {
    const [key, d] = gate;
    if (P.foldsOf !== id) { P.folds = new Set(); P.foldsOf = id; }
    lean = `<p class="stmt-note">The paper cites this result and does not prove it. Lean states it as the proposition below, and every result whose proof uses it assumes that proposition.</p><dl class="kv"><dt>declaration</dt><dd><code>${esc(d.name)}</code></dd><dt>file</dt><dd><code>${esc(d.file)}:${esc(d.line)}</code></dd></dl>${dsDefHTML(d, `/${key}`, 1)}`;
  } else if (r.citedIn) {
    // a citation with no Lean statement: its host's Lean does not assume it
    const host = resultById(r.citedIn), name = esc(envOf(r.citedIn)?.heading ?? r.citedIn);
    lean = `<p class="none">${citedDropped(r) ? `The paper's proof of ${name} invoked this result; the proof as corrected does not use it (see the correction on ${name}), so Lean has no statement of it.` : host?.lean ? `Lean has no statement of this cited result: the Lean proof of ${name} does not assume it.` : `No Lean statement yet — the Lean stages decide whether the proof of ${name} assumes it.`}</p>`;
  } else lean = r.citedLean ? `<p class="none">The paper cites this result and does not prove it; Lean states it as a proposition the results that use it assume.</p>` : `<p class="none">Not formalized yet — the Lean stages run after the referee accepts the core.</p>`;
  $("#d-body").innerHTML = `${r.cites ? `<h4>Cited from</h4><p><code>${esc(r.cites)}</code></p>${r.citedSource?.copy ? `<details class="ds-fold" open><summary>The source's statement, as copied for this run</summary><div class="cited-src">${typeset(r.citedSource.copy, m, esc)}${r.citedSource.cut ? "\n… (cut; the whole text is in the run's discovery/cited_sources/)" : ""}</div></details>` : r.citedSource?.unavailable ? `<p class="stmt-note">The source could not be obtained, so the citation is taken as printed and not checked: ${esc(r.citedSource.unavailable)}</p>` : r.citedSource === null ? `<p class="stmt-note">The run holds no copy of the source's statement.</p>` : ""}` : ""}${r.citedLean || (r.citedIn && !r.lean) ? "" : `<h4>Verdict</h4><div class="grades">${badge(r) || `<span class="pill b-neutral">not graded yet</span>`}</div>`}
    ${r.review ? `<h4>Referee (V1.5)</h4><div class="grades">${g("faithful", r.review.faithfulness)}${g("ambiguity", r.review.ambiguity)}${g("correctness", r.review.correctness)}</div>${r.review.detail ? `<div class="prose">${texEnum(r.review.detail, m)}</div>` : ""}${r.review.reading ? `<p><b>Pinned reading:</b> ${tex(r.review.reading, m)}</p>` : ""}` : ""}
    ${r.paperError ? `<h4>${r.paperError.kind === "clarification" ? "Clarification" : r.paperError.kind === "undetermined" ? "Not determined as printed" : "Error in the paper"}</h4><div class="prose">${texEnum(r.paperError.detail, m)}</div>${r.paperError.witness ? `<details class="cmore" open><summary>Counterexample</summary><div class="prose">${texEnum(r.paperError.witness, m)}</div></details>` : ""}` : ""}
    ${r.conditions?.length ? `<h4>Conditions added (${r.conditions.length})</h4><ul class="conds">${r.conditions.map((c) => `<li data-cond="${esc(c.id)}">${tex(c.condition, m)} <code>${esc(c.id)}</code></li>`).join("")}</ul>` : ""}
    <h4>${r.umbrella ? "Its propositions" : "Lean"}</h4>${lean}
    ${r.deps.length && !r.umbrella ? `<h4>Its proof uses</h4><p>${r.deps.map((d) => esc(envOf(d)?.heading ?? d)).join(", ")}</p>` : ""}`;
  // an umbrella's propositions: to the block in the paper, its drawer in place of this one
  $$("#d-body [data-umbgo]").forEach((b) => b.addEventListener("click", () => { jumpTo(b.dataset.umbgo); openDrawer(b.dataset.umbgo); }));
  $("#drawer").classList.add("on"); $("#drawer").setAttribute("aria-hidden", "false");
  // the paper moves aside so the statement and its Lean are read next to each other
  if (!document.body.classList.contains("drawer-on")) {
    document.body.classList.add("drawer-on");
    requestAnimationFrame(() => { at?.scrollIntoView({ block: "nearest" }); });
  }
}
/** The note over linked rows: how to read them against the paper's `segs`, `found` of them on the page. */
const xlNote = (segs, found) => (!segs.length ? "" : `<p class="stmt-note">${found ? `Point at a row to see where the paper says it; click to jump there. Point at the paper's statement — its linked phrases are underlined — to find its row.${found < segs.length ? ` ${segs.length - found} of its ${segs.length} phrases could not be found on this page.` : ""}` : "The paper's phrases for these rows could not be located on this page."}</p>`);
/** The Lean declarations that formalize what a block of the paper states: those tagged with a core node
    whose place is in the block (`[key, declaration]`). */
function blockDefs(f) {
  const nodes = new Set(Object.entries(P.detail?.places ?? {}).filter(([, p]) => { const at = p.anchor ? document.getElementById(p.anchor) : null; return at && (at === f || f.contains(at)); }).map(([n]) => n));
  return Object.entries(P.detail?.leanDefs ?? {}).filter(([, d]) => nodes.has(d.node));
}
/* The drawer of an assumption or definition block: the Lean that formalizes it, its rows linked to
   the block's phrases as a result's are — no verdict, it is not a result. A block of another kind with no Lean of its own (a remark, an example) opens nothing. */
function openBlockDrawer(f) {
  const defs = blockDefs(f), env = (P.paper?.envs ?? []).find((e) => e.label === f.dataset.label);
  if (!defs.length && !/^(assumption|definition|condition)/i.test(env?.envName ?? "")) return;
  closeDrawer();
  f.classList.add("open");
  $("#d-kind").textContent = env?.envName ?? "block"; $("#d-title").textContent = env?.heading ?? f.dataset.label;
  $("#d-sub").textContent = f.dataset.label;
  P.folds = new Set(); P.foldsOf = null;
  const formalized = Object.keys(P.detail?.leanDefs ?? {}).length > 0;
  const segs = defs.flatMap(([, d]) => d.segments ?? []), found = xlLocate(f, segs);
  const links = { found: found ? new Set(XLP.ranges.keys()) : null, whole: XLP.whole };
  const linked = (key, d) => (d.segments?.length ? `<div class="xlscope">${dsDefHTML(d, `/${key}`, 1, links)}${d.uncovered?.length ? `<p class="stmt-note">Phrases shown faint are stated by no Lean row.</p>` : ""}</div>` : "");
  $("#d-body").innerHTML = `<h4>Lean</h4>${xlNote(segs, found)}${defs.length ? defs.map(([key, d]) => `<dl class="kv"><dt>declaration</dt><dd><code>${esc(d.name)}</code></dd><dt>file</dt><dd><code>${esc(d.file)}:${esc(d.line)}</code></dd></dl>${linked(key, d) || dsDefHTML(d, `/${key}`, 1)}`).join("")
    : `<p class="none">${formalized ? "No Lean declaration shown for the results is tagged with this block: either no result's Lean statement names it, or its Lean carries no tag for it." : "Not formalized yet — the Lean stages run after the referee accepts the core."}</p>`}`;
  $("#drawer").classList.add("on"); $("#drawer").setAttribute("aria-hidden", "false");
  if (!document.body.classList.contains("drawer-on")) { document.body.classList.add("drawer-on"); requestAnimationFrame(() => { f.scrollIntoView({ block: "nearest" }); }); }
}
/* The open drawer drawn again from the run's current record (its scroll and open folds kept); closed
   when its result is gone. */
function refreshDrawer() {
  if (!resultById(P.drawer)) { closeDrawer(); return; }
  const body = $("#d-body"), at = body.scrollTop;
  openDrawer(P.drawer);
  body.scrollTop = at;
}
/* Nothing of a result's Lean is lit in the paper: the drawer is closing, or opening on another result. */
function xlClear() {
  xlPaint([]); plPaint([]);
  $$(".xl-has, .xl-on").forEach((x) => { x.classList.remove("xl-has", "xl-on"); x.style.cursor = ""; });
  XLP.ranges.clear(); XLP.whole.clear(); XLP.root = null; xlPinned = null;
}
function closeDrawer() {
  xlClear();
  const open = $("#paper-body .open");
  if (document.body.classList.contains("drawer-on")) {
    document.body.classList.remove("drawer-on");
    requestAnimationFrame(() => { open?.scrollIntoView({ block: "nearest" }); layout(); });
  }
  P.drawer = null;
  $("#drawer").classList.remove("on"); $("#drawer").setAttribute("aria-hidden", "true"); open?.classList.remove("open");
}
$("#drawer-x").addEventListener("click", closeDrawer);
document.addEventListener("keydown", (e) => { if (e.key !== "Escape" || !$("#modal").hidden) return; if (!document.body.classList.contains("drawer-on") && P.open && wide()) fold(); else closeDrawer(); });

/* promotion round on the paper page */
const PROMO_KINDS = [["accept", "Accept"], ["accept_with_edits", "Accept with edits"], ["generalize_first", "Generalize first"], ["defer", "Defer"], ["decline", "Decline"]];
/**
 * "Accept all recommendations", over the items of a decision that waits on the owner: `chosen(x)` —
 * they set it by hand; `entry(x)` — what the agent's recommendation enters on it, null when it gave
 * none that can be entered. The entries for the items not set by hand (`fill`: [item, entry]), the
 * items left with neither (`missing`: never guessed) and how many stand as set by hand. Pure.
 */
function recFill(items, chosen, entry) {
  const open = items.filter((x) => !chosen(x)).map((x) => [x, entry(x)]);
  return { fill: open.filter(([, e]) => e), missing: open.filter(([, e]) => !e).map(([x]) => x), byHand: items.length - open.length };
}
/** Its button: disabled, naming them, while an item has no recommendation. */
const recButton = (id, missing) => `<button class="btn" type="button" id="${id}" ${missing.length ? `disabled title="${esc(`No recommendation yet for: ${missing.join(", ")}`)}"` : ""}>Accept all recommendations</button>`;
/** Its one confirmation, in plain words: `n` decisions go out, `byHand` of them as the owner set them. Pure. */
const recSummary = (lead, n, byHand, counts) => `${lead} ${n} decision${n === 1 ? "" : "s"}${byHand ? ` — ${n - byHand} as recommended, ${byHand} as you set ${byHand === 1 ? "it" : "them"}` : " as recommended"}: ${counts}?`;
const promoDec = (pr, id) => P.promo[id] ?? pr.decisions[id] ?? { kind: "pending" };
const promoItems = (pr) => [...(pr.topics ?? []), ...pr.proposals];
/* A round's recommendations: a new topic is created or declined; an entry takes one of its own choices. */
function promoRecs(pr) {
  return recFill(promoItems(pr), (x) => promoDec(pr, x.key ?? x.id).kind !== "pending", (x) => {
    const k = x.recommendation?.kind;
    if (x.key) return k === "accept" || k === "decline" ? { kind: k } : null;
    if (!PROMO_KINDS.some(([kind]) => kind === k) || (k === "generalize_first" && !x.is_paper_result)) return null;
    return k === "accept_with_edits" ? { kind: k, edits: { target_module: x.target_module } } : { kind: k };
  });
}
function drawPromo() {
  const pr = P.detail.promotion, host = $("#promo");
  if (!pr || (!pr.waiting && !pr.applied)) { host.innerHTML = ""; return; }
  const dec = (id) => promoDec(pr, id);
  const recs = promoRecs(pr);
  const topics = pr.topics ?? [];
  const total = pr.proposals.length + topics.length;
  const decided = pr.proposals.filter((p) => dec(p.id).kind !== "pending").length + topics.filter((t) => dec(t.key).kind !== "pending").length;
  const titleOf = (id) => pr.proposals.find((p) => p.id === id)?.title ?? id;
  const pm = P.paper?.macros;
  host.innerHTML = `<section class="promo-sec" id="promo-sec"><h2>Promote to toolkit <span class="pill ${pr.applied ? "b-done" : "b-pending"}">round ${pr.round}${pr.applied ? " · applied" : ""}</span></h2>
    <p class="meta">PaperFormalizer proposes the results proved in this paper's Lean that are general enough to reuse. Each one you accept is built into your toolkit. ${pr.skipped} more were set aside automatically.</p>
    ${pr.error ? `<p class="empty-note">The checklist does not parse: ${esc(pr.error)}</p>` : ""}
    ${pr.refusal ? `<p class="empty-note"><b>The round was not applied.</b> <span style="white-space:pre-wrap">${esc(pr.refusal)}</span></p>` : ""}
    ${topics.map((t) => { const d = dec(t.key); return `<div class="pentry"><h3>New topic for your toolkit: <code>${esc(t.path.split("/").join(" › "))}</code></h3><p class="pstmt">${mixed(t.scope, pm)}</p>
      <p class="meta">Needed by: ${t.for.map((id) => mixed(titleOf(id), pm)).join("; ")}. Accepting adds it to your topic tree; declining keeps the tree as it is — then give those entries an existing topic with “Accept with edits”.</p>${t.recommendation ? `<p class="meta"><b>The agent recommends: ${esc(t.recommendation.kind)}</b> — ${tex(t.recommendation.why, P.paper?.macros)}</p>` : ""}
      ${pr.applied ? `<div class="choice"><span class="pill b-neutral">${esc(pr.decisions[t.key]?.kind ?? "pending")}</span></div>` : `<div class="choice" data-id="${esc(t.key)}"><button type="button" data-k="accept" aria-pressed="${d.kind === "accept"}">Create the topic</button><button type="button" data-k="decline" aria-pressed="${d.kind === "decline"}">Decline</button></div>`}</div>`; }).join("")}
    ${pr.proposals.map((p) => { const d = dec(p.id); const kinds = p.is_paper_result ? PROMO_KINDS : PROMO_KINDS.filter(([k]) => k !== "generalize_first"); return `<div class="pentry"><h3>${mixed(p.title, pm)}</h3><p class="pstmt">${mixed(p.content, pm)}</p>
      ${p.relation_to_paper ? `<p class="meta">${mixed(p.relation_to_paper, pm)}</p>` : ""}${p.recommendation ? `<p class="meta"><b>The agent recommends: ${esc(p.recommendation.kind.replace(/_/g, " "))}</b> — ${tex(p.recommendation.why, P.paper?.macros)}</p>` : ""}<div class="pmeta"><span>name <code>${esc(p.proposed_name)}</code></span><span>into <code>${esc(p.target_module)}</code></span><span>${esc(p.division)}</span></div>
      <details><summary>Why it may recur · independent check</summary><p>${mixed(p.reuse_evidence, pm)}</p>${p.checker ? `<p>${mixed(p.checker, pm)}</p>` : ""}${p.lean_type ? `<pre class="st">${esc(p.lean_type)}</pre>` : ""}</details>
      ${pr.applied ? `<div class="choice"><span class="pill b-neutral">${esc((pr.decisions[p.id]?.kind ?? "pending").replace(/_/g, " "))}</span></div>` : `<div class="choice" data-id="${esc(p.id)}">${kinds.map(([k, l]) => `<button type="button" data-k="${k}" aria-pressed="${d.kind === k}">${l}</button>`).join("")}${d.kind === "accept_with_edits" ? `<input type="text" data-edit="${esc(p.id)}" value="${esc(d.edits?.target_module ?? p.target_module)}" aria-label="Target module">` : ""}</div>`}</div>`; }).join("")}
    ${pr.applied ? "" : `<div class="resume-in" style="margin-top:0.8rem"><span class="msg">${decided} of ${total} decided</span><span class="grow"></span>${pr.waiting && recs.fill.length + recs.missing.length ? recButton("promo-accept-recs", recs.missing.map((x) => x.title ?? x.path)) : ""}${pr.proposals.some((p) => p.recommendation) ? `<button class="btn" type="button" id="promo-recs" title="Fills every entry with the recommendation, for you to review before applying">Fill in recommendations</button>` : ""}<button class="btn" type="button" id="promo-save">Save decisions</button><button class="btn btn-primary" type="button" id="promo-apply" ${decided < total || !pr.waiting ? "disabled" : ""} title="${decided < total ? "Decide every entry and new topic first" : ""}">Apply round ${pr.round}</button></div>`}</section>`;
}
async function promoClick(e) {
  const pr = P.detail.promotion;
  const b = e.target.closest(".choice [data-k]");
  if (b) {
    const id = b.closest(".choice").dataset.id; const k = b.dataset.k;
    const p = pr.proposals.find((x) => x.id === id);
    P.promo[id] = k === "accept_with_edits" && p ? { kind: k, edits: { target_module: p.target_module } } : { kind: k };
    drawPromo(); return;
  }
  if (e.target.id === "promo-recs") {
    for (const p of pr.proposals) if (p.recommendation) P.promo[p.id] = p.recommendation.kind === "accept_with_edits" ? { kind: "accept_with_edits", edits: { target_module: p.target_module } } : { kind: p.recommendation.kind };
    drawPromo(); return;
  }
  if (e.target.id === "promo-accept-recs") {
    // the entries not set by hand take the agent's recommendation; the round is then applied as by
    // "Apply", after the one confirmation that says what goes out
    const { fill, missing, byHand } = promoRecs(pr);
    if (missing.length || !fill.length) return;
    for (const [x, d] of fill) P.promo[x.key ?? x.id] = d;
    drawPromo();
    const all = promoItems(pr), n = (k) => all.filter((x) => promoDec(pr, x.key ?? x.id).kind === k).length;
    await promoSubmit(pr, true, `<p>${recSummary(`Apply round ${pr.round} with`, all.length, byHand, PROMO_KINDS.map(([k, l]) => `${l.toLowerCase()} ${n(k)}`).join(", "))}</p>`);
    return;
  }
  if (e.target.id === "promo-save" || e.target.id === "promo-apply") await promoSubmit(pr, e.target.id === "promo-apply");
}
/* A round's decisions written into its checklist and, to `apply`, the round applied. `what`: the
   confirmation of "Accept all recommendations" — nothing is written before it is given. */
async function promoSubmit(pr, apply, what = "") {
  const decisions = {};
  for (const [id, d] of Object.entries(P.promo)) decisions[id] = d.kind === "accept_with_edits" ? { kind: d.kind, edits: { ...d.edits } } : { kind: d.kind };
  const save = async () => { if (Object.keys(decisions).length) { await post(`/api/runs/${encodeURIComponent(S.slug)}/promotion`, { round: pr.round, decisions }); P.promo = {}; toast("Decisions saved in the checklist"); } };
  try {
    if (!what) await save();
    if (apply) await runAction({ kind: "apply-promotion", round: pr.round }, what ? "Accept all recommendations" : `Apply round ${pr.round}`, what, what ? "Continue" : "Apply", what ? save : null);
  } catch (err) { toast(err.message, true); }
}

/* Repairs that would weaken a main result: the owner accepts each, declines it, or asks for another. */
const REC_WORDS = { accept: "accept", redo: "redo with guidance", decline: "decline (report it as an error)" };
const REPAIR_KINDS = [["accept", "Accept", "Accept the proposed statement: it becomes the corrected result"], ["redo", "Redo with guidance", "Discard this proposal: the result is revised again along what you write"], ["decline", "Decline (report it as an error)", "Report the result as not holding as printed; it and what rests on it leave the Lean development"]];
/* Each waits beside its statement, as a card in the margin; the status box only points there. */
function repairsPointerHTML(d) {
  const n = d.repairs.length, recs = repairRecs(d.repairs);
  const links = d.repairs.map((r) => `<button class="linkbtn" type="button" data-goto="${esc(r.node)}">${esc(envOf(r.node)?.heading ?? r.node)}</button>${r.recommendation ? ` (the agent recommends: ${esc(REC_WORDS[r.recommendation.kind] ?? r.recommendation.kind)})` : ""}`).join(" · ");
  return `<p>${n === 1 ? "A revision" : `${n} revisions`} would make a result of the paper weaker. ${n === 1 ? "It waits" : "Each waits"} for your decision beside its statement, marked red on the proof map: ${links}</p>${recs.fill.length + recs.missing.length ? `<div class="actions" style="justify-content:flex-end">${recButton("repair-recs", recs.missing.map((r) => envOf(r.node)?.heading ?? r.node))}</div>` : ""}`;
}
/* What the agent's recommendation enters on a repair: the choice, with the guidance it offered for a
   redo or its reason for a decline — none when that text is missing. */
function repairRecs(repairs) {
  return recFill(repairs, (r) => repairChoice(P.repair, r).kind, (r) => {
    const rec = r.recommendation, text = (rec?.kind === "redo" ? rec.guidance : rec?.kind === "decline" ? rec.why : "") ?? "";
    return rec && REC_WORDS[rec.kind] && (rec.kind === "accept" || text.trim()) ? { kind: rec.kind, text, of: r.proposed } : null;
  });
}
/* "Accept all recommendations": the repairs not decided by hand take the agent's recommendation, and
   all go out as by "Send my decisions", after the one confirmation that says what goes out. */
function acceptRepairRecs() {
  const all = P.detail.repairs, { fill, missing, byHand } = repairRecs(all);
  if (missing.length || !fill.length) return false;
  for (const [r, c] of fill) P.repair[r.node] = c;
  drawCards(); drawStatus();
  const n = (k) => all.filter((r) => repairChoice(P.repair, r).kind === k).length;
  return sendRepairs(`<p>${recSummary("Send", all.length, byHand, `accept ${n("accept")}, redo ${n("redo")}${fill.some(([, c]) => c.kind === "redo") ? " (with the suggested guidance)" : ""}, decline ${n("decline")}`)}</p>`, "Accept all recommendations", "Continue");
}
/** What the owner has entered on the repair `r` (`{ kind, text }`), or {}: an entry made on an earlier
 *  proposal for the same result (`of`) is no ruling on this one. Pure. */
const repairChoice = (entered, r) => (entered[r.node]?.of === r.proposed ? entered[r.node] : {});
/** The repairs waiting, as the rulings sent on them name them: a new proposal is a new wait. Pure. */
const sentKey = (repairs) => JSON.stringify(repairs.map((r) => [r.node, r.proposed]));
/**
 * What became of the rulings sent (`sent`: the repairs they were on, and how often the run was seen
 * since), from the run as the server now shows it: "taken" — it is at work on them (a run at work
 * shows no repair to rule on) or has halted with other ones; "dropped" — it is not at work and the
 * same repairs still wait, seen more than twice: it did not start, or halted at once; else
 * "waiting". Pure.
 */
function sentState(sent, repairs, live) {
  if (sent.key !== sentKey(repairs)) return "taken";
  return !live && sent.seen > 2 ? "dropped" : "waiting";
}
function repairCardHTML(r, d) {
  const m = P.paper?.macros;
  const c = repairChoice(P.repair, r);
  const decided = d.repairs.filter((x) => repairChoice(P.repair, x).kind).length;
  const anchor = envOf(r.node)?.anchor ?? "";
  const rec = r.recommendation;
  const recHTML = rec ? `<div class="agent-rec"><div class="cbyline"><span class="av">AG</span><span class="cname">The agent recommends</span><span class="ctag">${esc(REC_WORDS[rec.kind] ?? rec.kind)}</span></div><div class="prose">${tex(rec.why, m)}</div>${rec.guidance ? `<p class="meta">What it would ask of the new repair — choosing “Redo with guidance” starts from this text, for you to edit:</p><div class="rec-guidance">${tex(rec.guidance, m)}</div>` : ""}</div>` : "";
  // the owner's ruling: the three choices, the text a redo or a decline needs, and the one button that
  // sends every ruling — or, once sent, that it was
  const wantsText = c.kind === "redo" || c.kind === "decline";
  const ruling = P.sent
    ? `<p class="meta"><b>Your decision was sent</b> (${esc(REPAIR_KINDS.find(([k]) => k === c.kind)?.[1] ?? "")}) — the run is taking it up.</p>`
    : `<div class="choice">${REPAIR_KINDS.map(([k, l, t]) => `<button type="button" data-rk="${k}" title="${esc(t)}" aria-pressed="${c.kind === k}">${l}</button>`).join("")}</div>
      ${wantsText ? `<textarea data-rtext rows="${c.kind === "redo" && (c.text ?? "").length > 160 ? 7 : 2}" style="width:100%;margin-top:0.4rem" placeholder="${c.kind === "redo" ? "What the new revision should do" : "Why you decline it"}">${esc(c.text ?? "")}</textarea>` : ""}
      <div class="resume-in" style="margin-top:0.6rem"><span class="msg">${decided} of ${d.repairs.length} decided</span><span class="grow"></span><button class="btn btn-primary" type="button" data-repairs-send ${decided === d.repairs.length ? "" : "disabled"}>Send my decisions</button></div>`;
  return `<div class="card decision" data-card="repair:${esc(r.node)}" data-kind="note" data-chip="Findings" data-node="${esc(r.node)}" ${anchor ? `data-anchor="${esc(anchor)}"` : ""} data-repair="${esc(r.node)}" tabindex="0">
    <div class="cbyline"><span class="av">PF</span><span class="cname">Your decision</span><span class="cwhen">${esc(envOf(r.node)?.heading ?? r.node)}</span><span class="ctag">weaker revision</span></div>
    <div class="cbody"><p>${r.undetermined ? "The statement as printed does not determine what it claims (nothing was shown false). The proposed revision — in blue beside the statement — states one reading, and claims less." : "The statement as printed does not hold. The proposed revision — in blue beside the statement — is true but claims less."}</p>
      <details><summary>The proposed statement, as shown in the paper</summary><div class="pstmt">${tex(r.proposed, m)}</div>
      ${(r.corollaries ?? []).map((x, k) => `<p class="meta">With split-off result ${k + 1}${x.title ? ` — ${tex(x.title, m)}` : ""} (a result of its own: a corollary of the statement, or a claim it bundled in)</p><div class="pstmt">${tex(x.statement, m)}</div>`).join("")}</details>
      <div class="prose"><b>What it gives up.</b> ${texEnum(r.given_up, m)}</div>
      ${r.detail || r.witness ? `<details><summary>${r.undetermined ? "What the printed statement leaves undetermined" : "What is wrong with the printed statement"}</summary>${r.detail ? `<div class="prose">${texEnum(r.detail, m)}</div>` : ""}${r.witness ? `<div class="prose">${texEnum(r.witness, m)}</div>` : ""}</details>` : ""}
      ${r.guidance ? `<p class="meta">Your earlier guidance:</p><div class="prose">${tex(r.guidance, m)}</div>` : ""}
      ${recHTML}
      ${ruling}
    </div></div>`;
}
function repairClick(e) {
  const entry = e.target.closest("[data-repair]");
  if (entry && e.target.dataset.rk) {
    const node = entry.dataset.repair, r = P.detail.repairs.find((x) => x.node === node); if (!r) return true;
    // a redo starts from the guidance the agent offered, for the owner to edit
    const offered = e.target.dataset.rk === "redo" ? r.recommendation?.guidance ?? "" : "";
    P.repair[node] = { kind: e.target.dataset.rk, text: repairChoice(P.repair, r).text || offered, of: r.proposed };
    redrawCard(`repair:${node}`); drawStatus(); activate(`repair:${node}`, false); return true;
  }
  if (!e.target.closest("[data-repairs-send]")) return false;
  sendRepairs();
  return true;
}
/* Every repair's ruling, sent as the resume that carries them (`what`: said in its confirmation). */
function sendRepairs(what = "", title = "Apply your decisions on the revisions", ok = "Continue") {
  const pick = (k) => P.detail.repairs.filter((r) => repairChoice(P.repair, r).kind === k);
  const said = (r) => (P.repair[r.node].text ?? "").trim();
  const declined = pick("decline");
  if ([...declined, ...pick("redo")].some((r) => !said(r))) { toast("Say why you decline, or what the new revision should do.", true); return false; }
  const slug = S.slug;
  return runAction({
    kind: "rule-repairs", accept: pick("accept").map((r) => r.node),
    ...(declined.length ? { decline: { nodes: declined.map((r) => r.node), reason: declined.map(said).join("; ") } } : {}),
    redo: pick("redo").map((r) => ({ node: r.node, guidance: said(r) })),
  }, title, what, ok).then((started) => {
    if (!started || S.slug !== slug) return started;
    // The run takes a moment to come up and take the decisions: the cards say so at once, and the
    // page asks again until it has (`sentState`; a missed change event must not leave them asking).
    P.sent = { key: sentKey(P.detail.repairs), seen: 0 };
    drawStatus(); drawCards(); requestAnimationFrame(layout);
    let tries = 0;
    const again = () => { if (P.sent && S.view === "paper" && S.slug === slug && tries++ < 60) { onChange(`run:${slug}`); setTimeout(again, 3000); } };
    setTimeout(again, 3000);
    return true;
  });
}

/* ── Lean, nested: hypothesis rows over numbered clause cards ──────────────
   The drawer (`structuredHtml`), from the run's `leanView`: shared hypotheses one to a
   row; each clause a card with the hypotheses it states for itself, an `∃ …,` line its parts
   share, and either its leaf (what it concludes) or the inset sub-cards it splits into. Under a line that names a
   Prop-valued declaration of the paper's own Lean, a fold opens that declaration the same way; when
   the declaration formalizes a core node the page has a place for (`plOf`), the fold's header names
   the place and the line carries the node (`data-places`). A clause written `type_of% @name` (`of`)
   is the statement of the paper's theorem `name`: a quiet line names it and its rows follow in place.
   Every line opens with a chip saying in a word what it is, so a card reads down as a sentence
   (given … assume … then …); the chip's tooltip gives the Lean term.
   CARRIER RULE: a row's phrases ride on a content LINE (`.srow`: a hypothesis row, a conclusion's
   leaf, an `∃` line) — never on a card, so one line lights at a time.
   A link a row does not have alone (`coarse`: its clause's, or one list F5 gave many rows) is drawn
   quieter, and a run of rows sharing it is labelled once, on its first row — a row whose declaration
   has a place in the paper too: the place is its own link, the phrases stay its clause's.
   A binder of the section's `variable`s says so; a named hypothesis with parts is its head line (the
   name, what it quantifies or assumes — the name alone is a label, no row) over its parts; the parts of a
   hypothesis read "and", the alternatives of a disjunction "either" / "or". Of a theorem's claims side by
   side only the first reads "then", each later one "and"; the first after an `∃ …,` reads "such that". */
const DS_TERMS = {
  theorem: { shared: "Hypotheses", section: "", clause: "Conclusion", mark: "then", markTip: "what the result concludes", also: true, hyp: "assume", decl: "given", side: "where" },
  assumption: { shared: "Parameters", section: "", clause: "Clause", mark: "then", markTip: "a field of the record: one of the claims it bundles", also: true, hyp: "if", decl: "given", side: "where" },
  // a `def … : Prop`: the conjunction of its clauses, a hypothesis where it is assumed and a conclusion where
  // it is claimed — so its clauses read as claims ("then", "and"), like a theorem's; nothing is "defined as" a clause
  condition: { shared: "Parameters", section: "", clause: "Clause", mark: "then", markTip: "one of the claims this proposition makes", also: true, hyp: "if", decl: "given", side: "where" },
  definition: { shared: "Parameters", section: "Given by", clause: "Clause", mark: "defined as", markTip: ":=, the definition's value", hyp: "if", decl: "given", side: "where" },
};
/** The Lean term behind a chip's word, for its tooltip. */
const DS_TIPS = { also: "one more claim, alongside the one above", such: "what holds of the names just introduced", part: "one part of the hypothesis above", alt: "one alternative of a disjunction (∨)", section: "a binder of the section's `variable`s that this statement uses", hyp: "hypothesis", cited: "hypothesis: a cited result, assumed", decl: "binder", side: "a condition on the names just introduced", def: "the declaration: its name, parameters and type", prem: "a hypothesis that states a claim of its own: its parts follow" };
/** The chip of a line its parts share, by how the line opens (`mark`: the word for a field's name); a plain
    `∃ …,` line reads as it stands and has none. */
const DS_INTROS = [[/^∃ᶠ/, "frequently", "∃ᶠ, frequently along a filter"], [/^∃!/, "there exists exactly one", "∃!, unique existence"], [/^∃/, "", ""], [/^∀ᵐ/, "for almost every", "∀ᵐ, for almost every point of a measure"], [/^∀ᶠ/, "eventually", "∀ᶠ, eventually along a filter"],
  [/^if\b/, "if", "if … then, a case split: this branch"], [/^else\b/, "otherwise", "else, the other branch"], [/^match\b/, "by cases", "match, a case split on a value"], [/^\|/, "case", "one alternative of the match"]];
const dsIntroChip = (c, x) => { const hit = DS_INTROS.find(([re]) => re.test(c.intro.trimStart())); return hit ? (hit[1] ? dsChip("intro", hit[1], hit[2]) : "") : dsChip("intro", x.terms.mark, x.terms.markTip); };
/** A line's text with one quantifier or binder group to a line. */
const dsIntroText = (t) => t.replace(/,\s+(?=[∃∀])/g, ",\n").replace(/\)\s+(?=\()/g, ")\n");
const dsChip = (cls, text, tip) => `<span class="ds-chip ds-chip-${cls}" title="${esc(tip)}">${esc(text)}</span>`;
/** Card nesting followed (the server splits to 6) and folds opened inside one another. */
const DS_MAX_DEPTH = 8, DS_FOLD_DEPTH = 6;
const dsLeaf = (c) => typeof c.code === "string" && c.code.trim() !== "";
/** A leaf that only qualifies the names an `∃` line introduced (`0 < a`): not one of the claims. */
const dsSide = (c) => !c.hyps?.length && !c.intro && !c.sub?.length && dsLeaf(c);
/** A content line's class and phrases; a declaration's own rows (`x.linked` false) carry none. */
const dsLine = (r, cls, x) => {
  const xl = x.linked ? r.xl ?? "" : "", places = dsPlaces(r), run = x.run ?? (x.run = {});
  const coarse = Boolean(xl && r.coarse);
  x.first = coarse && run.xl !== xl; run.xl = coarse ? xl : null;
  return `class="srow ${cls}${r.unstated && x.linked ? " unstated" : ""}${coarse ? " xl-coarse" : ""}" data-binder="${esc(xl)}"${places}`;
};
/** A line's places: the core nodes, among those its declarations formalize, the page has a place for. */
const dsPlaces = (r) => { const ns = [...new Set((r.refs ?? []).map((key) => P.detail.leanDefs?.[key]?.node).filter((n) => n && plOf(n)))]; return ns.length ? ` data-places="${esc(ns.join(" "))}"` : ""; };
/** What a linked statement's line with no phrase says of itself (an instance binder: nothing). */
const dsTag = (r, x) => {
  if (!x.linked || /^\s*\[/.test(r.code ?? "")) return "";
  if (r.unstated) return `<span class="rtag">not in the paper's text</span>`;
  if (!r.xl) return dsPlaces(r) ? "" : `<span class="rtag">not linked yet</span>`;
  const ids = r.xl.split(" ");
  if (x.found && !ids.some((i) => x.found.has(i))) return `<span class="rtag">phrase not found on this page</span>`;
  if (x.first) return `<span class="rtag rtag-coarse">this clause as a whole ↔ these phrases — not linked row by row yet</span>`;
  return x.whole && ids.some((i) => x.whole.has(i)) ? `<span class="rtag rtag-coarse">lights its formula whole</span>` : "";
};
/** The folds under a line: one per declaration it names, drawn when opened (`P.folds` keeps them open). */
function dsFolds(r, x) {
  if (!r.refs?.length || x.depth >= DS_FOLD_DEPTH) return "";
  return r.refs.map((key) => {
    const d = P.detail.leanDefs?.[key]; if (!d) return "";
    const path = `${x.path}/${x.n.k++}:${key}`, open = P.folds.has(path), pl = plOf(d.node);
    const chip = pl ? `<button type="button" class="ds-place" data-place="${esc(d.node)}" title="Where the paper states this — click to go there">→ ${esc(pl.label)}</button>` : "";
    return `<details class="ds-fold" data-fold="${esc(path)}" data-def="${esc(key)}" data-depth="${x.depth + 1}"${open ? " open" : ""}><summary><span class="ds-fold-kind">${esc(d.kind)}</span><code>${esc(d.name)}</code>${chip}<span class="ds-fold-at">${esc(d.file)}:${esc(d.line)}</span></summary><div class="ds-fold-body">${open ? dsDefHTML(d, path, x.depth + 1) : ""}</div></details>`;
  }).join("");
}
/** `links` (`found`, `whole`): the declaration's rows drawn with its own links, in its block's drawer. */
function dsDefHTML(d, path, depth, links) {
  return d.view ? dsViewHTML(d.view, { terms: DS_TERMS[d.role] ?? DS_TERMS.definition, linked: Boolean(links), ...links, path, depth, n: { k: 0 } }) : `<pre class="ds-raw">${esc(d.source)}</pre>`;
}
/** `x` for the parts of a hypothesis: a part that only states (no hypothesis, no line of its own) reads "and", not "then". */
const dsPartX = (s, x) => (!s.hyps?.length && !s.intro ? dsMark(x, "and", DS_TIPS.part) : x);
/** `x` with another word for what a line concludes; `then` keeps the statement's own. */
const dsMark = (x, mark, markTip) => ({ ...x, then: x.then ?? { mark: x.terms.mark, markTip: x.terms.markTip }, terms: { ...x.terms, mark, markTip } });
/** `x` for the `k`-th of the claims that stand side by side: of a theorem's conclusions only the first reads
    "then", each later one "and" (so do the claims after a "such that"); a part with hypotheses of its own
    reads "assume … then …" inside (`dsBodyHTML`). So do the clauses of a condition (a record's fields, a
    `def … : Prop`): "then", then "and"; a value's definition keeps "defined as". */
const dsNext = (x, k) => (k > 0 && (x.terms.also || x.then) ? dsMark(x, "and", DS_TIPS.also) : x);
/** `x` for what follows a line that ends in an `∃ …,` header: its first claim reads "such that". */
const dsSuch = (line, x) => (/,\s*$/.test(line ?? "") && line.lastIndexOf("∃") > line.lastIndexOf("∀") && !/∃ᶠ[^∃]*$/.test(line) ? dsMark(x, "such that", DS_TIPS.such) : x);
function dsHypHTML(r, x0) {
  // `hypAnd` is this row's word only: the parts of the hypothesis start afresh
  const word = x0.hypAnd ? "and" : x0.terms.hyp, x = x0.hypAnd ? { ...x0, hypAnd: false } : x0;
  // a premise with parts of its own: the word for a hypothesis — or, for a named one, its head line —
  // then its clauses as cards
  if (r.sub?.length) {
    // a head that is the name alone (`(h :`) is no row of the statement (no id): a label, never linked
    const hx = x.linked && !r.id ? { ...x, linked: false } : x;
    const head = r.head ? `<div ${dsLine(r, "ds-row ds-row-hyp ds-head", hx)}>${dsChip("hyp", r.chip === "cited" ? "cited" : word, r.chip === "cited" ? DS_TIPS.cited : DS_TIPS.prem)}<div class="ds-code">${esc(r.head)}</div>${dsTag(r, hx)}</div>${dsFolds(r, x)}` : dsChip("hyp", word, DS_TIPS.prem);
    return `<div class="ds-prem">${head}<div class="ds-subs">${r.sub.map((s, k) => `<div class="ds-sub">${dsBodyHTML(s, k === 0 && dsSuch(r.head, x) !== x ? dsSuch(r.head, x) : dsPartX(s, x), 1)}</div>`).join("")}</div></div>`;
  }
  const chip = r.chip === "decl" ? "decl" : "hyp", t = x.terms, each = chip === "decl" && r.code.trimStart().startsWith("∀"), intro = each && DS_INTROS.find(([re]) => re.test(r.code.trimStart()));
  const label = r.chip === "cited" ? dsChip(chip, "cited", DS_TIPS.cited) : intro ? dsChip(chip, intro[1], intro[2]) : each ? "<span></span>" : dsChip(chip, chip === "hyp" ? word : t[chip], DS_TIPS[chip]);
  const section = r.section ? `<span class="rtag rtag-section" title="${esc(DS_TIPS.section)}">from the section</span>` : "";
  return `<div ${dsLine(r, `ds-row ds-row-${chip}`, x)}>${label}<div class="ds-code">${esc(r.code)}</div>${section}${dsTag(r, x)}</div>${dsFolds(r, x)}`;
}
/** A row some sentence of the paper states: it, or a part of it, has phrases. */
const dsStated = (c) => Boolean(c.xl || c.hyps?.some(dsStated) || c.sub?.some(dsStated));
/** A run of rows this long that the paper says nowhere is folded (`x.more`: in a statement with links). */
const DS_MORE_MIN = 3;
/** Of the hypotheses of one list only the first reads "if" / "assume", each later one "and". In a linked
    statement a run of rows the paper says nowhere (what Lean needs: types, instances, side conditions) is
    one closed fold where it stands, its rows drawn inside as they are (`P.folds` keeps it open). */
const dsRowsHTML = (rows, x) => {
  if (!rows?.length) return "";
  const more = { ...x, hypAnd: true };
  let seen = false;
  const html = rows.map((r) => { const hyp = r.chip !== "decl", h = dsHypHTML(r, hyp && seen ? more : x); seen ||= hyp; return h; });
  const out = [];
  for (let i = 0, j; i < rows.length; i = j) {
    for (j = i; x.more && j < rows.length && !dsStated(rows[j]); j++);
    if (j - i < DS_MORE_MIN) { j = Math.max(j, i + 1); out.push(...html.slice(i, j)); continue; }
    const path = `${x.path}/+${(x.n.more = (x.n.more ?? 0) + 1)}`, decls = rows.slice(i, j).filter((r) => r.chip === "decl").length, hyps = j - i - decls;
    const what = [decls ? `${decls} binder${decls > 1 ? "s" : ""}` : "", hyps ? `${hyps} hypothes${hyps > 1 ? "es" : "is"}` : ""].filter(Boolean).join(", ");
    out.push(`<details class="ds-fold ds-more" data-fold="${esc(path)}"${P.folds.has(path) ? " open" : ""}><summary title="Rows Lean needs that no sentence of the paper states (types, instances, measurability, …) — click to show them">${j - i} rows Lean adds (${what})</summary>${html.slice(i, j).join("")}</details>`);
  }
  return `<div class="ds-rows">${out.join("")}</div>`;
};
/** A leaf: the line that states something — what a clause concludes, a definition's value, a record's field. */
function dsConclHTML(c, x) {
  return `<div ${dsLine(c, "ds-concl", x)}>${dsChip("concl", x.terms.mark, x.terms.markTip)}<div class="ds-code">${esc(c.code ?? "")}</div>${dsTag(c, x)}</div>${dsFolds(c, x)}`;
}
/** A declaration's own row: its kind, then its name, parameters and type. */
const dsDefRowHTML = (c, x, kind) => `<div ${dsLine(c, "ds-concl ds-def", x)}>${dsChip("def", kind, DS_TIPS.def)}<div class="ds-code">${esc(c.code ?? "")}</div>${dsTag(c, x)}</div>${dsFolds(c, x)}`;
/** The `∃ …,` line of a card that splits: the card's own content line. */
const dsIntroHTML = (c, x) => `<div ${dsLine(c, "ds-intro", x)}>${dsIntroChip(c, x)}${esc(dsIntroText(c.intro))}${dsTag(c, x)}</div>${dsFolds(c, x)}`;
const dsSideHTML = (c, x) => `<div ${dsLine(c, "ds-row ds-row-side", x)}>${dsChip("side", x.terms.side, DS_TIPS.side)}<div class="ds-code">${esc(c.code ?? "")}</div>${dsTag(c, x)}</div>${dsFolds(c, x)}`;
/** The line of a clause that is another theorem's statement: which one — and, when that theorem is a
    result of the paper with links of its own, the way to it. Its rows follow as the card's own. */
function dsOfHTML(c, x) {
  const o = c.of, r = o.node ? resultById(o.node) : null;
  const go = r?.segments?.length ? `<button type="button" class="linkbtn" data-umbgo="${esc(r.id)}" title="A result of the paper, linked to its own statement there — open it">→ ${esc(envOf(r.id)?.heading ?? r.id)}</button>` : "";
  return `<div ${dsLine(c, "ds-of", x)}><span>the statement of</span><span class="ds-fold-kind">${esc(o.kind)}</span><code>${esc(o.name)}</code>${go}<span class="ds-fold-at">${esc(o.file)}:${esc(o.line)}</span>${c.xl || c.unstated ? dsTag(c, x) : ""}</div>`;
}
/** One clause, recursively: its own hypothesis rows, its `∃` line, then its leaf or its sub-cards. */
function dsBodyHTML(c, x, depth) {
  const leaf = dsLeaf(c), subs = Array.isArray(c.sub) ? c.sub : [];
  // what a clause concludes from hypotheses of its own (`C → D`) reads "then" wherever it stands; else one
  // alternative of a disjunction: a leaf reads "either" / "or"; one with parts is labelled so, its parts "and"
  if (c.hyps?.length) { if (x.terms.also || x.then) x = { ...x, terms: { ...x.terms, ...(x.terms.also ? { mark: DS_TERMS.theorem.mark, markTip: DS_TERMS.theorem.markTip } : x.then) } }; }
  else if (c.alt) x = dsMark(x, leaf ? c.alt : "and", leaf ? DS_TIPS.alt : DS_TIPS.part);
  const parts = [c.alt && !(leaf && !c.hyps?.length) ? `<div class="ds-label ds-alt" title="${esc(DS_TIPS.alt)}">${c.alt}</div>` : "", c.of ? dsOfHTML(c, x) : "", dsRowsHTML(c.hyps, x)];
  if (c.intro?.trim()) parts.push(leaf ? `<div class="ds-intro">${dsIntroChip(c, x)}${esc(dsIntroText(c.intro))}</div>` : dsIntroHTML(c, x));
  x = dsSuch(c.intro, x);
  if (leaf || !subs.length || depth >= DS_MAX_DEPTH) { if (leaf) parts.push(dsConclHTML(c, x)); }
  else parts.push(`<div class="ds-subs">${subs.map((s, k) => `<div class="ds-sub">${dsBodyHTML(s, dsNext(x, k), depth + 1)}</div>`).join("")}</div>`);
  return parts.join("");
}
/** A whole view: shared hypotheses / parameters, a definition's `def` row, then the numbered clauses. */
function dsViewHTML(v, x) {
  if (v.defRow && (x.terms === DS_TERMS.theorem || x.terms === DS_TERMS.definition)) x = { ...x, terms: /:\s*Prop\s*$/.test(v.defRow.code ?? "") ? DS_TERMS.condition : DS_TERMS.definition };
  const t = x.terms, parts = [], cs = v.conclusions ?? [], only = cs[0], lone = cs.length === 1;
  // rows are folded only where some row is linked: a statement with no link at all is drawn whole
  x = { ...x, more: x.linked && [...(v.sharedHyps ?? []), ...cs].some(dsStated) };
  if (v.sharedHyps?.length) parts.push(`<div class="ds-sect"><div class="ds-label">${t.shared}</div>${dsRowsHTML(v.sharedHyps, x)}</div>`);
  if (v.defRow && dsLeaf(v.defRow)) parts.push(`<div class="ds-sect ds-sect-def">${dsDefRowHTML(v.defRow, x, v.role ?? "def")}</div>`);
  if (cs.length && t.section) parts.push(`<div class="ds-label ds-label-section">${t.section}</div>`);
  const card = (c, i, depth, cx) => `<div class="ds-card"><div class="ds-label">${t.clause} ${i + 1}</div>${dsBodyHTML(c, dsNext(cx, i), depth)}</div>`;
  if (lone && !only.hyps?.length && !only.intro && dsLeaf(only) && !only.sub?.length) parts.push(dsConclHTML(only, x));
  else if (lone && only.intro && only.sub?.length) {
    // one `∃ …, (1) ∧ … ∧ (k)`: the ∃ line stays unnumbered and the numbers go to the claims under
    // it; leading conditions on the introduced names are quiet rows — unless every part is one
    const subs = only.sub; let lead = 0;
    while (only.intro.trimStart().startsWith("∃") && lead < subs.length && dsSide(subs[lead])) lead++;
    if (lead === subs.length) lead = 0;
    parts.push(`<div class="ds-lift">${dsRowsHTML(only.hyps, x)}${dsIntroHTML(only, x)}${lead ? `<div class="ds-rows ds-sides">${subs.slice(0, lead).map((s) => dsSideHTML(s, x)).join("")}</div>` : ""}</div>`);
    subs.slice(lead).forEach((c, i) => parts.push(card(c, i, 1, dsSuch(only.intro, x))));
  } else cs.forEach((c, i) => parts.push(card(c, i, 0, x)));
  return `<div class="ds">${parts.join("")}</div>`;
}
// a fold is drawn when first opened (`toggle` does not bubble: captured)
document.addEventListener("toggle", (e) => {
  const f = e.target; if (!f.matches?.("#drawer details.ds-fold")) return;
  if (!f.open) { P.folds.delete(f.dataset.fold); return; }
  P.folds.add(f.dataset.fold);
  const body = f.querySelector(":scope > .ds-fold-body"), d = P.detail?.leanDefs?.[f.dataset.def];
  if (d && body && !body.firstChild) body.innerHTML = dsDefHTML(d, f.dataset.fold, Number(f.dataset.depth));
}, true);

/* ── Lean, laid out by its structure (the flat rows) ──────────────────── */
const L_OPEN = "([{⦃⟨", L_CLOSE = ")]}⦄⟩";
/** The pieces of `t` at the top level (outside every bracket) around the separator `sep`. */
function leanSplit(t, sep) {
  const out = []; let depth = 0, from = 0;
  for (let i = 0; i < t.length; i++) {
    const c = t[i];
    if (L_OPEN.includes(c)) depth++;
    else if (L_CLOSE.includes(c)) depth = Math.max(0, depth - 1);
    else if (depth === 0 && t.startsWith(sep, i)) { out.push(t.slice(from, i).trim()); from = i + sep.length; i += sep.length - 1; }
  }
  out.push(t.slice(from).trim());
  return out.filter(Boolean);
}
/** `t` without one pair of brackets that encloses all of it, or null. */
function leanUnwrap(t) {
  if (t[0] !== "(" || t.at(-1) !== ")") return null;
  let depth = 0;
  for (let i = 0; i < t.length; i++) {
    if (L_OPEN.includes(t[i])) depth++;
    else if (L_CLOSE.includes(t[i]) && --depth === 0 && i < t.length - 1) return null;
  }
  return t.slice(1, -1).trim();
}
/**
 * A Lean proposition as indented lines: a conjunction one conjunct to a line, an implication chain
 * one premise to a line with its conclusion last, a leading quantifier on its own line, a
 * bracketed part that is itself such a formula opened up and indented. Short text stays one line.
 * The text is the source's, re-spaced only. Pure: [{ indent, mark, text }].
 */
function leanLines(text, indent = 0, mark = "", out = []) {
  const t = text.trim();
  const emit = (x, m = mark, ind = indent) => { out.push({ indent: ind, mark: m, text: x }); return out; };
  if (t.length <= 64) return emit(t);
  const conj = leanSplit(t, "∧");
  if (conj.length > 1) { conj.forEach((x, k) => leanLines(x, indent, k === 0 ? mark : "∧", out)); return out; }
  const chain = leanSplit(t, "→");
  if (chain.length > 1) { chain.forEach((x, k) => leanLines(x, indent, k === 0 ? mark : "→", out)); return out; }
  const q = /^([∀∃][^,]*,)\s*([\s\S]+)$/.exec(t);
  if (q && leanSplit(q[1].slice(0, -1), ",").length === 1) { emit(q[1]); return leanLines(q[2], indent + 1, "", out); }
  const inner = leanUnwrap(t);
  if (inner !== null) { emit("(", mark); leanLines(inner, indent + 1, "", out); return emit(")", "", indent); }
  return emit(t);
}
function leanLayoutHTML(text) {
  const lines = leanLines(text);
  if (lines.length === 1) return esc(lines[0].text);
  return lines.map((l) => `<span class="ll" style="--in:${l.indent}"><span class="lm">${esc(l.mark)}</span>${esc(l.text)}</span>`).join("");
}

/* ── prose with an inline enumeration: (a) … (b) … (c) …, (i) … (ii) …, (1) … (2) … ───── */
const ENUM_FAMILIES = [
  ["a", "b", "c", "d", "e", "f", "g", "h"],
  ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii"],
  ["1", "2", "3", "4", "5", "6", "7", "8"],
];
/** `s` cut at consecutive markers of one family, outside mathematics: [lead, [marker, text]…], or
 *  null when it holds no enumeration of at least two items. The run starts at the family's first
 *  marker, or — a text answering clauses (b) and (c) of a statement — at a later one that opens it. */
function enumParts(s) {
  const math = []; // spans of $…$, \(…\), \[…\]
  for (const m of s.matchAll(/\$\$[\s\S]+?\$\$|\\\[[\s\S]+?\\\]|\\\([\s\S]+?\\\)|\$(?:\\\$|[^$])+?\$/g)) math.push([m.index, m.index + m[0].length]);
  const free = (i) => !math.some(([a, b]) => i >= a && i < b);
  for (const fam of ENUM_FAMILIES) for (let first = 0; first + 1 < fam.length; first++) {
    const cuts = []; let from = 0;
    for (const k of fam.slice(first)) {
      const re = new RegExp(`(^|[\\s;:,.])\\(${k}\\)\\s`, "g"); re.lastIndex = from;
      let m; let hit = null;
      while ((m = re.exec(s))) { const at = m.index + m[1].length; if (free(at)) { hit = at; break; } }
      if (hit === null) break;
      cuts.push([hit, k]); from = hit + k.length + 2;
    }
    if (cuts.length < 2 || (first > 0 && s.slice(0, cuts[0][0]).trim() !== "")) continue;
    const parts = cuts.map(([at, k], n) => [k, s.slice(at + k.length + 2, n + 1 < cuts.length ? cuts[n + 1][0] : s.length).trim()]);
    return { lead: s.slice(0, cuts[0][0]).trim(), parts };
  }
  return null;
}
/** A TeX fragment as HTML, an inline enumeration as a list. */
function texEnum(s, macros) {
  const e = s ? enumParts(s) : null;
  if (!e) return tex(s, macros);
  return `${e.lead ? `${tex(e.lead, macros)}` : ""}<ol class="enum">${e.parts.map(([k, t]) => `<li><span class="ek">(${esc(k)})</span> ${tex(t, macros)}</li>`).join("")}</ol>`;
}

/* A run moves only under an attached agent session (it acts at the next halt): how to start one. */
function noOrchHTML(slug) {
  const tk = S.toolkit?.toolkit;
  return `<p>No agent session is attached to <b>${esc(slug)}</b>, so nothing would act at its next halt.</p><p>Open a terminal in <code>${esc(tk?.repo ?? "the PaperFormalizer folder")}</code>, start <code>claude</code> or <code>codex</code>, and ask it:</p>${cmdBox(`Orchestrate the PaperFormalizer run ${slug}${tk ? ` (toolkit ${tk.root})` : ""}.`)}<p>It attaches itself and decides the run's halts; this page then shows the agent, and Resume works.</p>`;
}
/* `before`: what the confirmed action needs done first (a round's decisions written). */
async function runAction(action, title, what = "", ok = "Continue", before = null) {
  try {
    const pv = await post(`/api/runs/${encodeURIComponent(S.slug)}/preview`, { action });
    if (!(await confirmRun(title, `${what}<p>This runs in the background; the page updates as it goes.</p>${cmdBox(pv.command)}`, ok))) return false;
    if (before) await before();
    const r = await post(`/api/runs/${encodeURIComponent(S.slug)}/action`, { action });
    toast(r.demo ? "Sent to the demo run" : r.queued ? "Sent to the agent's job, which starts it" : `Started — log: ${r.log}`);
    setTimeout(() => onChange(`run:${S.slug}`), 800);
    return true;
  } catch (err) {
    if (err.message === "no-orch") await confirmRun("Start an agent session first", noOrchHTML(S.slug), "OK");
    else toast(err.message, true);
  }
  return false;
}

/* Share the finished paper on the public site: what will be published and the warning, the owner's
   tick, then the send — nothing leaves before the tick and the click, and the send carries the
   one-time key this dialog was shown with (what is sent is what was shown). The owner then signs in
   to GitHub and confirms on the share service's page, in a tab opened on the click (a tab opened
   later would be blocked); the status line follows the share until it is published or refused. */
const SHARE_FINAL = new Set(["published", "review", "refused", "expired"]);
const extLink = (u, text) => (/^https?:\/\//.test(u ?? "") ? `<a href="${esc(u)}" target="_blank" rel="noopener">${esc(text)}</a>` : "");
function shareLineHTML(sh) {
  const on = esc(String(sh.started_at).slice(0, 10)), by = sh.login ? ` by @${esc(sh.login)}` : "";
  switch (sh.status) {
    case "published": return `<p>Published${by} on ${on} — ${extLink(sh.url, "its public page")}.</p>`;
    case "review": return `<p>Shared${by} on ${on}; waiting for the owner's review before it is published${sh.pr_url ? ` — ${extLink(sh.pr_url, "the pull request")}` : ""}.</p>`;
    case "refused": return `<p>Not published: the registry refused the share of ${on}.</p>${sh.problems?.length ? `<ul>${sh.problems.map((x) => `<li>${esc(x)}</li>`).join("")}</ul>` : ""}`;
    case "expired": return `<p>The share started on ${on} ${sh.note ? `ended: ${esc(sh.note)}` : "expired before it was confirmed"}.</p>`;
    case "submitted": return `<p>Confirmed${by}: ${SHARE_STALE.has(sh.slug) ? "the registry is still checking the paper — reload this page later" : "the registry is checking the paper…"}</p>${unreachableHTML(sh.slug)}`;
    default: return `<p>Waiting for you to sign in to GitHub and confirm the share: ${extLink(sh.claim_url, "Open GitHub sign-in")} (check code <b>${esc(sh.check_code)}</b>).</p>${unreachableHTML(sh.slug)}`;
  }
}
/** Why the share's status could not be asked, while it cannot (the server's `unreachable`). */
const unreachableHTML = (slug) => (SHARE_DOWN.has(slug) ? `<p class="share-warn">The share service could not be reached: ${esc(SHARE_DOWN.get(slug))}</p>` : "");
/** A paper's share in the list's Share column: the button of a finished paper never shared (or
 *  whose last share was refused or expired), else where its last share stands. */
function shareCellHTML(r) {
  if (r.status !== "done") return "";
  const sh = r.share, busy = SHARING.has(r.slug);
  const btn = (label) => r.shareable?.ok === false
    ? `<span class="pill b-neutral" title="${esc(r.shareable.reason ?? "its bundle cannot be shared")}">not ready</span>`
    : `<button class="sh-act" type="button" data-share="${esc(r.slug)}"${busy ? " disabled" : ""}>${busy ? "sharing…" : label}</button>`;
  const pill = (cls, body, title = "") => `<span class="pill ${cls}"${title ? ` title="${esc(title)}"` : ""}>${body}</span>`;
  if (!sh) return btn("Share");
  if (!SHARE_FINAL.has(sh.status)) sharePoll(r.slug);
  switch (sh.status) {
    case "published": return pill("b-done", extLink(sh.url, "published ↗") || "published");
    case "review": return pill("b-neutral", extLink(sh.pr_url, "in review ↗") || "in review");
    case "refused": return `${pill("b-error", "refused", (sh.problems ?? []).join("\n") || "the registry refused the share")}${btn("Share again")}`;
    case "expired": return `${pill("b-neutral", "expired")}${btn("Share again")}`;
    case "submitted": return SHARE_STALE.has(r.slug) ? pill("b-neutral", "still checking", "the registry is still checking the paper — reload this page later") : pill("b-neutral", "checking…", SHARE_DOWN.get(r.slug) ?? "");
    default: return pill("b-neutral", extLink(sh.claim_url, "sign in ↗") || "sign in", SHARE_DOWN.get(r.slug) ?? "waiting for you to sign in to GitHub and confirm");
  }
}
/** Shares being sent from this page (the dialog was confirmed, the upload is under way), by slug. */
const SHARING = new Set();
const SHARE_POLL = new Map();
/** Since when this page asks after each share in progress; the shares it stopped asking after (a
 *  check that ran past `SHARE_PATIENCE`), and why the service could not be reached, by slug. */
const SHARE_SINCE = new Map(), SHARE_STALE = new Set(), SHARE_DOWN = new Map();
const SHARE_PATIENCE = 30 * 60 * 1000;
function sharePoll(slug) {
  if (SHARE_POLL.has(slug) || SHARE_STALE.has(slug)) return;
  if (!SHARE_SINCE.has(slug)) SHARE_SINCE.set(slug, Date.now());
  SHARE_POLL.set(slug, setTimeout(async () => {
    let now = null;
    try { now = (await api(`/api/runs/${encodeURIComponent(slug)}/share-status`)).data; } catch { /* asked again on the next draw */ }
    SHARE_POLL.delete(slug);
    if (now?.unreachable) SHARE_DOWN.set(slug, String(now.unreachable)); else if (now) SHARE_DOWN.delete(slug);
    if (now?.status && SHARE_FINAL.has(now.status)) SHARE_SINCE.delete(slug);
    // a check that runs this long has stalled (the registry's workflow failed): the page stops asking
    else if (now?.status === "submitted" && Date.now() - SHARE_SINCE.get(slug) > SHARE_PATIENCE) SHARE_STALE.add(slug);
    shareRedraw(slug);
    // asked again while it is in progress and a view shows it (a draw finding it unchanged starts none)
    if (now?.status && !SHARE_FINAL.has(now.status) && (S.view === "toolkit" || (S.view === "paper" && S.slug === slug))) sharePoll(slug);
  }, 4000));
}
/** The views that show `slug`'s share drawn again: its paper page, or the list. */
function shareRedraw(slug) {
  if (S.view === "paper" && S.slug === slug) onChange(`run:${slug}`);
  else if (S.view === "toolkit") onChange("toolkit");
}
async function shareRun(slug = S.slug) {
  const url = `/api/runs/${encodeURIComponent(slug)}/share`;
  const redrawBusy = () => { if (S.view === "paper" && S.slug === slug) drawStatusBox(); else if (S.view === "toolkit" && $("#runs-body")) drawRuns(); };
  let tab = null;
  try {
    const p = (await api(url)).data;
    const asked = confirmRun("Share this paper publicly", `<p><b>${esc(p.title)}</b> (${esc(p.slug)}): ${p.files} files, ${esc(p.size)}, published at <code>${esc(p.url)}</code>.</p><p>${esc(p.parts.join(", "))}</p><p>${esc(p.signIn)}</p><p class="share-warn">${esc(p.warning)}</p><label class="share-ack"><input type="checkbox" id="share-ack"> I understand this publishes the paper's TeX source and PDF</label>`, "Share");
    const ok = $("#modal-ok"), box = $("#share-ack");
    ok.disabled = true;
    box.onchange = () => { ok.disabled = !box.checked; };
    const yes = await asked;
    ok.disabled = false;
    if (!yes) return;
    // the sign-in tab, opened while the click still counts; it waits for the upload
    try {
      tab = window.open("about:blank", "_blank");
      if (tab) { tab.opener = null; tab.document.title = "Sharing…"; tab.document.body.textContent = "Sending the paper… this tab opens GitHub's sign-in when it is sent."; }
    } catch { tab = null; }
    SHARING.add(slug); redrawBusy();
    let r;
    try { r = await post(url, { understood: true, nonce: p.nonce }); } finally { SHARING.delete(slug); redrawBusy(); }
    let opened = false;
    try { if (tab && !tab.closed) { tab.location.href = r.claim_url; opened = true; } } catch { /* the tab is gone */ }
    await confirmRun("Finish in your browser", `<p>The paper was sent. ${opened ? "A new tab opened" : "Open the sign-in page"}: sign in to GitHub there and press <b>Share publicly</b>.</p><p>Check code: <b class="share-code">${esc(r.check_code)}</b> — continue only if the page shows the same code.</p><p>${extLink(r.claim_url, "Open GitHub sign-in")}</p><p>This page shows the outcome once you confirm.</p>`, "OK");
  } catch (err) {
    try { tab?.close(); } catch { /* already closed */ }
    await confirmRun("Not shared", `<p>${esc(err.message)}</p>`, "OK");
  }
  shareRedraw(slug);
}

/* ── the demo's tour (`paperformalizer demo`): the step, what it points at, its Next ── */
const TOUR = { on: false, v: null, folded: false, step: null };
const tourHref = (v) => (v.current.view === "paper" ? `#/paper/${encodeURIComponent(v.slug)}` : v.current.view === "library" ? "#/library" : "#/");
async function refreshTour() {
  let r;
  try { r = await fetch("/api/demo", { credentials: "same-origin" }); } catch { return; }
  if (!r.ok) { TOUR.on = false; return; }
  TOUR.on = true; TOUR.v = await r.json();
  // a step begun (Next, or what the page sent): its view is opened
  if (TOUR.step !== null && TOUR.step !== TOUR.v.step && !TOUR.v.busy) location.hash = tourHref(TOUR.v);
  if (!TOUR.v.busy) TOUR.step = TOUR.v.step;
  drawTour();
}
function drawTour() {
  const v = TOUR.v; if (!TOUR.on || !v) return;
  let host = $("#tour");
  if (!host) { host = document.createElement("aside"); host.id = "tour"; host.setAttribute("aria-label", "Demo tour"); document.body.append(host); }
  const c = v.current, away = (location.hash || "#/") !== tourHref(v);
  host.className = TOUR.folded ? "tour folded" : "tour";
  const wait = v.expect === "rule-repairs" ? "Waiting for your decisions on the revisions" : v.expect ? "Waiting for you to apply the round" : "";
  host.innerHTML = TOUR.folded
    ? `<button class="btn" type="button" data-tour="unfold">Demo · step ${v.step + 1} of ${v.total}</button>`
    : `<div class="tour-head"><span class="pill b-agent">Demo</span><span class="meta">step ${v.step + 1} of ${v.total}</span><span class="grow"></span><button class="linkbtn" type="button" data-tour="fold" title="Fold the tour away">Hide</button></div>
      <h3>${esc(c.title)}</h3><div class="tour-body">${c.body}</div>
      ${v.busy ? `<p class="meta tour-busy">The run is at work…</p>` : ""}
      <div class="tour-actions">${away ? `<a class="btn" href="${tourHref(v)}">Show me</a>` : ""}<button class="linkbtn" type="button" data-tour="restart">Start over</button><span class="grow"></span>${wait ? `<span class="meta">${wait}</span>` : v.step + 1 < v.total ? `<button class="btn btn-primary" type="button" data-tour="next" ${v.busy ? "disabled" : ""}>Next</button>` : `<span class="meta">The end of the tour</span>`}</div>`;
  markTour();
}
/* the step's target, marked on the page as drawn (the page redraws itself as the run changes) */
function markTour() {
  $$(".tour-target").forEach((e) => e.classList.remove("tour-target"));
  const sel = TOUR.on && !TOUR.folded && !TOUR.v?.busy ? TOUR.v?.current.target : null;
  let els = [];
  if (sel) { try { els = $$(sel); } catch { /* not on this view */ } }
  els.forEach((e) => e.classList.add("tour-target"));
  // the spotlight goes on the first one drawn; the page scrolls to it once per step
  TOUR.el = els.find((e) => e.getClientRects().length) ?? null;
  if (TOUR.el && TOUR.scrolled !== TOUR.v.current.id) { TOUR.scrolled = TOUR.v.current.id; TOUR.el.scrollIntoView({ behavior: "smooth", block: "center" }); }
  placeSpot();
}
/* the spotlight: the page dimmed around the step's target, a ring on it (clicks pass through) */
function placeSpot() {
  const el = TOUR.el?.isConnected ? TOUR.el : null, r = el?.getBoundingClientRect();
  let spot = $("#tour-spot");
  if (!el || !r.width || !r.height) { spot?.remove(); placeTour(null); return; }
  if (!spot) { spot = document.createElement("div"); spot.id = "tour-spot"; spot.setAttribute("aria-hidden", "true"); document.body.append(spot); }
  const pad = 6;
  Object.assign(spot.style, { top: `${r.top - pad}px`, left: `${r.left - pad}px`, width: `${r.width + 2 * pad}px`, height: `${r.height + 2 * pad}px` });
  placeTour(r);
}
/* the tour's box in the corner that hides least of the target `r` (bottom right when there is none) */
function placeTour(r) {
  const host = $("#tour"); if (!host || TOUR.folded) return;
  const corners = ["br", "bl", "tr", "tl"], cls = { bl: "at-bl", tr: "at-tr", tl: "at-tl" };
  host.classList.remove(...Object.values(cls));
  if (!r) return;
  const w = host.offsetWidth, h = host.offsetHeight, vw = window.innerWidth, vh = window.innerHeight, m = 16, top = 60;
  const box = { br: [vw - m - w, vh - m - h], bl: [m, vh - m - h], tr: [vw - m - w, top], tl: [m, top] };
  const hidden = (c) => { const [x, y] = box[c]; return Math.max(0, Math.min(x + w, r.right) - Math.max(x, r.left)) * Math.max(0, Math.min(y + h, r.bottom) - Math.max(y, r.top)); };
  const best = corners.reduce((a, c) => (hidden(c) < hidden(a) ? c : a), "br");
  if (cls[best]) host.classList.add(cls[best]);
}
window.addEventListener("scroll", () => { if (TOUR.el) requestAnimationFrame(placeSpot); }, { capture: true, passive: true });
window.addEventListener("resize", () => { if (TOUR.el) placeSpot(); });
document.addEventListener("click", async (e) => {
  const b = e.target.closest("[data-tour]"); if (!b) return;
  const what = b.dataset.tour;
  if (what === "fold" || what === "unfold") { TOUR.folded = what === "fold"; drawTour(); return; }
  if (what === "restart" && !window.confirm("Start the demo over from its first step?")) return;
  try { TOUR.v = await post(`/api/demo/${what}`, {}); if (what === "restart") { TOUR.step = 0; location.hash = tourHref(TOUR.v); } drawTour(); } catch (err) { toast(err.message, true); }
});

/* ── boot ─────────────────────────────────────────────────────────────── */
if (SNAP) {
  // a shared paper: drawn once from its snapshot; what the build wrote in #app stays if that fails
  SNAP.views = snapLoad();
  SNAP.views.then((v) => { SNAP.slug = v.page.summary.slug; return route(); }).then(() => { if (location.hash === "#report") openReport(); }, (err) => { app.classList.add("snap-failed"); app.insertAdjacentHTML("afterbegin", `<p class="empty-note">The interactive page could not be drawn: ${esc(err.message)}</p>`); });
} else {
connect();
refreshInbox().catch(() => {});
route();
refreshTour();
window.addEventListener("hashchange", drawTour);
new MutationObserver(() => { if (TOUR.on) { clearTimeout(TOUR.t); TOUR.t = setTimeout(markTour, 100); } }).observe(app, { childList: true, subtree: true });
document.addEventListener("visibilitychange", wake);
window.addEventListener("pageshow", wake);
window.addEventListener("online", wake);
// the net under the pushes: whatever one missed is on the page within this (an unchanged view costs a 304)
setInterval(wake, 15_000);
setInterval(() => { if (S.view === "toolkit" && $("#runs-body")) drawRuns(); }, 30_000); // keep "updated" times fresh
}
})();
