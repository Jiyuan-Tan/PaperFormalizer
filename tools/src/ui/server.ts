// The local UI server: 127.0.0.1 only, a random token (handed over in the printed URL, then kept in
// a SameSite=Strict HttpOnly cookie), the Host header checked against DNS rebinding. Views are JSON,
// gzipped, with ETags; pushes go out as server-sent events when the watcher sees a change. A run's
// views (its page detail, its drawers, its paper) are answered from memory while unchanged.
import { createHash, randomBytes, timingSafeEqual } from "node:crypto";
import { createReadStream, existsSync, lstatSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, statSync, writeFileSync } from "node:fs";
import { open } from "node:fs/promises";
import http from "node:http";
import { createRequire } from "node:module";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { gzipSync } from "node:zlib";
import type { ToolkitConfig } from "../toolkit/config.js";
import type { ChecklistDecision } from "../proposals/checklist.js";
import type { ProposalBatch } from "../proposals/schema.js";
import { buildArgv, displayCommand, launch, needsAgent, writeChecklistDecisions, type Action } from "./actions.js";
import { derive, readJsonCached, signature } from "./fscache.js";
import { readLibrary } from "./library_model.js";
import { ASSET_EXT, MATH_OVERRIDES_FILE, runPaper, texStrings, type Fragment, type PaperView } from "./page_snapshot.js";
import { applyOf, renderCheckpointOf, checklistPath, DECISIONS_FILE, listRunSlugs, markApplying, markStarted, OBJECTIONS_FILE, START_REQUEST_FILE, MESSAGES_FILE, drawersOf, pageOf, runDetail, runDir, runLive, runSummary, validSlug, type MessageFile, type OrchDecision, type OrchMessage, type OwnerObjection } from "./run_model.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { clearMessages, nextMessageId, updateMessages } from "../../scripts/messages_store.mjs";
import { planFingerprint, pollShare, readShare, sharePaper, sharePlan, shareRecordView, shareView, type ShareDeps } from "../verify/share.js";
import type { MathFailure } from "./tex_html.js";
import { TIKZ_DIR } from "./tikz.js";
import { ChangeWatcher } from "./watch.js";
import type { DemoDriver } from "../demo/driver.js";

const STATIC_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "static");
/** The TheoremChecker checkout, where the owner starts an interactive agent session. */
const REPO_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "..");
const KATEX_DIR = path.dirname(createRequire(import.meta.url).resolve("katex/dist/katex.min.css"));
const PDFJS_DIR = path.dirname(path.dirname(createRequire(import.meta.url).resolve("pdfjs-dist/build/pdf.min.mjs")));
const TYPES: Record<string, string> = {
  ".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8", ".css": "text/css; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8", ".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".gif": "image/gif", ".webp": "image/webp", ".pdf": "application/pdf", ".eps": "application/postscript", ".ps": "application/postscript",
  ".woff2": "font/woff2", ".woff": "font/woff", ".ttf": "font/ttf", ".svg": "image/svg+xml", ".json": "application/json",
};

/** Formulas neither renderer reads, for the orchestrating agent (written by the UI). */
export const MATH_FAILURES_FILE = path.join("logs", "ui_math_failures.json");
/** What the page could not draw besides formulas (`RenderProblems`), rewritten as the paper changes; the
 *  orchestrating agent's watcher reports a new list once. */
export const RENDER_PROBLEMS_FILE = path.join("logs", "ui_render_problems.json");

/** The owner's messages to the agent (`OrchMessage`): the length of one, and what it may carry —
 *  files of these kinds only (documents, pictures, archives: nothing a browser would run). */
export const MESSAGE_LIMITS = { chars: 4000, files: 5, fileBytes: 40 * 1024 * 1024, bytes: 100 * 1024 * 1024 };
export const UPLOAD_EXT = new Set([".pdf", ".txt", ".tex", ".bib", ".md", ".png", ".jpg", ".jpeg", ".zip", ".tar", ".gz", ".tgz"]);
/** The name an attached file is kept under: the client's name without its path, of plain characters,
 *  with no leading dot, at most 100 long, and none of `taken`. */
export function safeUploadName(name: string, taken: string[] = []): string {
  let base = (name.split(/[\\/]/).pop() ?? "").replace(/[^A-Za-z0-9._-]/g, "_").replace(/^\.+/, "_");
  const ext = path.extname(base);
  base = base.slice(0, base.length - ext.length).slice(0, 100 - ext.length) || "file";
  for (let k = 1; ; k++) { const n = `${base}${k > 1 ? `-${k}` : ""}${ext}`; if (!taken.includes(n)) return n; }
}
const megabytes = (n: number) => `${Math.round(n / (1024 * 1024))} MB`;
const sha256Of = (file: string) => new Promise<string>((resolve, reject) => {
  const h = createHash("sha256");
  createReadStream(file).on("data", (c) => h.update(c)).on("end", () => resolve(h.digest("hex"))).on("error", reject);
});
/** `dir` as a plain directory (made when absent), never a link to one. */
const plainDir = (dir: string): boolean => {
  try { mkdirSync(dir, { mode: 0o700 }); } catch { /* there already */ }
  try { return lstatSync(dir).isDirectory(); } catch { return false; }
};

/** When this server process started: part of every keyed ETag. */
const BOOT = Date.now().toString(36);
/** The pace of the event stream's pings (the page takes three missed for a lost connection). */
const PING_MS = 10_000;
/** The page's files as they stand on disk: a tab that loaded others runs an older page. */
const assetsTag = (): string => ["index.html", "app.js", "app.css"].map((f) => signature(path.join(STATIC_DIR, f))).join("|");

export interface UiServer { server: http.Server; url: string; token: string; close: () => Promise<void> }

/** `demo`: the page of `theoremchecker demo` — its tour (`/api/demo`), and what the owner sends taken
 *  by the demo's stand-in agent instead of started (`DemoDriver`). */
export async function startUiServer(cfg: ToolkitConfig, opts: { port: number; host?: string; token?: string; share?: ShareDeps; demo?: DemoDriver }): Promise<UiServer> {
  const token = opts.token ?? randomBytes(18).toString("base64url");
  const host = opts.host ?? "127.0.0.1";
  const clients = new Set<http.ServerResponse>();
  // a run's paper re-renders when its files change (a no-op when the sources did not), keeping
  // MATH_FAILURES_FILE current for the agent without the page being open
  const rerender = new Map<string, NodeJS.Timeout>();
  const watcher = new ChangeWatcher(cfg, (scope) => {
    for (const c of clients) c.write(`event: change\ndata: ${JSON.stringify({ scope })}\n\n`);
    const slug = scope.startsWith("run:") ? scope.slice(4) : null;
    if (slug) { clearTimeout(rerender.get(slug)); rerender.set(slug, setTimeout(() => { rerender.delete(slug); void warmPaper(slug).catch(() => null); }, 5000)); }
  });
  // the demo's tour moves on: the page asks for it again
  if (opts.demo) opts.demo.onChange = () => { for (const c of clients) c.write(`event: change\ndata: ${JSON.stringify({ scope: "demo" })}\n\n`); };
  const gzCache = new Map<string, Buffer>();
  /** The runs whose bundle is being sent to the share service. */
  const sharing = new Set<string>();
  // per run: when its share's status was last asked of the service (the page asks every few seconds)
  const sharePolled = new Map<string, number>();
  // the key a share dialog was shown with: of one slug and one plan, good once, for ten minutes
  const shareKeys = new Map<string, { slug: string; plan: string; until: number }>();
  // a view's answer, held while its key stands: its tag, and its gzip once a client asked for the body
  const answers = new Map<string, { key: string; etag: string; gz: Buffer | null }>();
  const answerOf = (name: string, key: string) => {
    let hit = answers.get(name);
    if (!hit || hit.key !== key) answers.set(name, hit = { key, etag: `"${createHash("sha1").update(`${BOOT}:${name}:${key}`).digest("base64url")}"`, gz: null });
    return hit;
  };
  // per run: the paper's fragment renderer, what it rendered, and the formulas no renderer read
  const fragmenters = new Map<string, { fragment: Fragment; done: Map<string, string>; failures: Array<MathFailure & { where: string }> }>();
  const recordFailures = (slug: string) => {
    const f = fragmenters.get(slug); if (!f) return;
    const file = path.join(runDir(cfg, slug), MATH_FAILURES_FILE);
    const seen = new Set<string>();
    const failures = f.failures.filter((x) => !seen.has(x.tex) && seen.add(x.tex));
    const text = JSON.stringify({ how: `add "<tex>": "<replacement TeX>" to ${MATH_OVERRIDES_FILE} in the run directory`, failures }, null, 2) + "\n";
    if (!failures.length && !existsSync(file)) return;
    try { if (!existsSync(file) || readFileSync(file, "utf8") !== text) { mkdirSync(path.dirname(file), { recursive: true }); writeFileSync(file, text); } } catch { /* best effort */ }
  };
  /** The run detail's TeX strings rendered: string → HTML (the page looks them up). */
  const texHtmlFor = (slug: string, detail: unknown): Record<string, string> => {
    const f = fragmenters.get(slug); if (!f) return {};
    const out: Record<string, string> = {};
    let fresh = false;
    for (const v of texStrings(detail)) {
      let html = f.done.get(v);
      if (html === undefined) {
        const r = f.fragment(v); html = r.html; f.done.set(v, html);
        if (r.failures.length) { f.failures.push(...r.failures.map((x) => ({ ...x, where: "run record" }))); fresh = true; }
      }
      out[v] = html;
    }
    if (fresh) recordFailures(slug);
    return out;
  };
  let port = opts.port;

  const okToken = (t: string | undefined | null) => {
    if (!t) return false;
    const a = Buffer.from(t);
    const b = Buffer.from(token);
    return a.length === b.length && timingSafeEqual(a, b);
  };
  // Cookies are shared by every port of a host: the name carries the port, so a second UI (another
  // toolkit, or the fallback port) does not overwrite the first one's key.
  const cookieName = () => `tc_token_${port}`;
  const cookieToken = (req: http.IncomingMessage) => new RegExp(`(?:^|;\\s*)${cookieName()}=([^;]+)`).exec(req.headers.cookie ?? "")?.[1];

  const sendJson = (req: http.IncomingMessage, res: http.ServerResponse, value: unknown, etagKey?: string, status = 200) => {
    const body = JSON.stringify(value);
    // A keyed tag names the inputs, not the bytes: it also carries this server's start, so a page
    // drawn by newer code is never answered "not modified" against what an older server drew.
    const etag = `"${etagKey ? createHash("sha1").update(`${BOOT}:${etagKey}`).digest("base64url") : createHash("sha1").update(body).digest("base64url")}"`;
    if (req.headers["if-none-match"] === etag) { res.writeHead(304, { ETag: etag }); res.end(); return; }
    const headers: Record<string, string> = { "Content-Type": "application/json; charset=utf-8", ETag: etag, "Cache-Control": "no-cache" };
    if (/\bgzip\b/.test(String(req.headers["accept-encoding"] ?? "")) && body.length > 1024) {
      let gz = gzCache.get(etag);
      if (!gz) { gz = gzipSync(body); if (gzCache.size > 64) gzCache.clear(); gzCache.set(etag, gz); }
      headers["Content-Encoding"] = "gzip";
      res.writeHead(status, headers); res.end(gz); return;
    }
    res.writeHead(status, headers); res.end(body);
  };
  /**
   * Answer the view `name`, made from what `key` names and written out by `body`: "not modified" to
   * a client that holds it, else its gzip — made once per key. A keyed tag also carries this
   * server's start (as in `sendJson`).
   */
  const sendView = (req: http.IncomingMessage, res: http.ServerResponse, name: string, key: string, body: () => string) => {
    const hit = answerOf(name, key);
    if (req.headers["if-none-match"] === hit.etag) { res.writeHead(304, { ETag: hit.etag }); res.end(); return; }
    const headers: Record<string, string> = { "Content-Type": "application/json; charset=utf-8", ETag: hit.etag, "Cache-Control": "no-cache" };
    if (!/\bgzip\b/.test(String(req.headers["accept-encoding"] ?? ""))) { res.writeHead(200, headers); res.end(body()); return; }
    hit.gz ??= gzipSync(body());
    res.writeHead(200, { ...headers, "Content-Encoding": "gzip" }); res.end(hit.gz);
  };
  const fail = (res: http.ServerResponse, status: number, message: string) => {
    res.writeHead(status, { "Content-Type": "application/json; charset=utf-8" });
    res.end(JSON.stringify({ error: message }));
  };
  const readBody = (req: http.IncomingMessage) => new Promise<unknown>((resolve, reject) => {
    let data = "";
    req.on("data", (c) => { data += c; if (data.length > 1_000_000) reject(new Error("request too large")); });
    req.on("end", () => { try { resolve(data ? JSON.parse(data) : {}); } catch { reject(new Error("the request is not JSON")); } });
    req.on("error", reject);
  });
  const serveFile = (req: http.IncomingMessage, res: http.ServerResponse, file: string, immutable: boolean, untrusted = false) => {
    if (!existsSync(file) || !statSync(file).isFile()) { fail(res, 404, "not found"); return; }
    const st = statSync(file);
    const etag = `"${st.mtimeMs.toString(36)}-${st.size.toString(36)}"`;
    if (req.headers["if-none-match"] === etag) { res.writeHead(304, { ETag: etag }); res.end(); return; }
    const ext = path.extname(file).toLowerCase();
    const type = TYPES[ext] ?? "application/octet-stream";
    const data = readFileSync(file);
    const gz = /\bgzip\b/.test(String(req.headers["accept-encoding"] ?? "")) && /text|json|svg/.test(type) && data.length > 1024;
    // a paper's SVG opened on its own would run its scripts on this origin: sandboxed
    const sandbox = untrusted && ext === ".svg" ? { "Content-Security-Policy": "script-src 'none'; sandbox" } : {};
    res.writeHead(200, { "Content-Type": type, ETag: etag, "Cache-Control": immutable ? "public, max-age=604800, immutable" : "no-cache", "X-Content-Type-Options": "nosniff", ...sandbox, ...(gz ? { "Content-Encoding": "gzip" } : {}) });
    res.end(gz ? gzipSync(data) : data);
  };

  const toolkitView = async () => {
    const slugs = listRunSlugs(cfg);
    // a run redone on the same paper is history: the later run stands for the paper
    const runs = (await Promise.all(slugs.map((s) => runSummary(cfg, s)))).filter((r) => r.status !== "superseded");
    runs.sort((a, b) => (rank(a.status) - rank(b.status)) || b.updatedAt - a.updatedAt);
    return {
      toolkit: {
        root: cfg.toolkitRoot, repo: REPO_DIR, name: path.basename(cfg.toolkitRoot), owner: cfg.owner.name, lean: cfg.leanToolchain,
        base: cfg.baseLibraries.map((b) => b.name), divisions: cfg.divisions,
      },
      runs,
    };
  };

  const recordRenderProblems = (slug: string, p: PaperView["renderProblems"]) => {
    const file = path.join(runDir(cfg, slug), RENDER_PROBLEMS_FILE);
    const any = Object.keys(p.unknownCommands).length + Object.keys(p.unknownEnvironments).length + p.missingFigures.length + p.omittedDrawings + (p.tikz ? 1 : 0) + p.unresolvedRefs.length + p.unnamedResults.length > 0;
    const text = JSON.stringify({ how: "fix in the run (its source copy, or a renderer gap with a test); the page shows each of these as source text or a placeholder", ...p }, null, 2) + "\n";
    if (!any && !existsSync(file)) return;
    try { if (!existsSync(file) || readFileSync(file, "utf8") !== text) { mkdirSync(path.dirname(file), { recursive: true }); writeFileSync(file, text); } } catch { /* best effort */ }
  };
  const paperView = async (slug: string) => {
    const p = await runPaper(runDir(cfg, slug), `/api/runs/${encodeURIComponent(slug)}/asset`);
    if (!p) return { value: null, key: "none" };
    return derive(`paper:${slug}`, p.inputs, p.base, async () => {
      const { view, fragment } = await p.render();
      fragmenters.set(slug, { fragment, done: new Map(), failures: view.health.mathFailures.map((x) => ({ ...x, where: "paper" })) });
      recordFailures(slug);
      recordRenderProblems(slug, view.renderProblems);
      return view;
    });
  };

  /** The paper rendered and its answer zipped, ahead of the page asking. */
  const warmPaper = async (slug: string) => {
    const { value, key } = await paperView(slug);
    answerOf(`paper:${slug}`, key).gz ??= gzipSync(JSON.stringify(value));
  };

  const server = http.createServer(async (req, res) => {
    try {
      const url = new URL(req.url ?? "/", `http://${host}`);
      const hostHeader = String(req.headers.host ?? "");
      // Any local port: an `ssh -L <other port>:127.0.0.1:<port>` forward arrives with its own port;
      // a foreign host name (DNS rebinding) is refused.
      if (!/^(127\.0\.0\.1|localhost)(:\d{1,5})?$/.test(hostHeader)) { fail(res, 421, "wrong host"); return; }
      const p = url.pathname;
      if (p.startsWith("/katex/")) { serveFile(req, res, safeJoin(KATEX_DIR, p.slice("/katex/".length)), true); return; }
      if (p.startsWith("/pdfjs/")) { serveFile(req, res, safeJoin(PDFJS_DIR, p.slice("/pdfjs/".length)), true); return; }
      if (p.startsWith("/assets/")) { serveFile(req, res, safeJoin(STATIC_DIR, p.slice("/assets/".length)), false); return; }
      if (p === "/" || p === "/index.html") {
        const t = url.searchParams.get("token");
        if (okToken(t)) {
          res.writeHead(302, { "Set-Cookie": `${cookieName()}=${token}; HttpOnly; SameSite=Strict; Path=/`, Location: "/" });
          res.end(); return;
        }
        if (!okToken(cookieToken(req))) {
          res.writeHead(403, { "Content-Type": "text/html; charset=utf-8" });
          res.end(`<!doctype html><meta charset=utf-8><title>TheoremChecker</title><body style="font-family:Georgia,serif;padding:3rem;max-width:40rem">Open the link that <code>theoremchecker ui</code> printed in your terminal — it carries this session's key.</body>`);
          return;
        }
        serveFile(req, res, path.join(STATIC_DIR, "index.html"), false); return;
      }
      if (!p.startsWith("/api/")) { fail(res, 404, "not found"); return; }
      if (!okToken(cookieToken(req))) { fail(res, 403, "open the link printed by `theoremchecker ui`"); return; }
      if (req.method === "POST" && req.headers["x-tc"] !== "1") { fail(res, 403, "missing request header"); return; }

      if (p === "/api/events") {
        res.writeHead(200, { "Content-Type": "text/event-stream", "Cache-Control": "no-cache", Connection: "keep-alive" });
        res.write(`event: hello\ndata: ${JSON.stringify({ boot: BOOT, assets: assetsTag() })}\n\n`);
        clients.add(res);
        // an event, not a comment: the page hears it, and takes a silence for a lost connection
        const ping = setInterval(() => res.write(`event: ping\ndata: ${JSON.stringify({ assets: assetsTag() })}\n\n`), PING_MS);
        req.on("close", () => { clearInterval(ping); clients.delete(res); });
        return;
      }
      if (p === "/api/toolkit" && req.method === "GET") { sendJson(req, res, await toolkitView()); return; }
      if (p === "/api/demo" || p.startsWith("/api/demo/")) {
        // the demo's tour: where it stands, its Next, and a restart from the first step
        const demo = opts.demo;
        if (!demo) { fail(res, 404, "not a demo"); return; }
        if (p === "/api/demo/next" && req.method === "POST") { const why = await demo.next(); if (why) { fail(res, 409, why); return; } }
        else if (p === "/api/demo/restart" && req.method === "POST") { const why = demo.restart(); if (why) { fail(res, 409, why); return; } }
        else if (p !== "/api/demo" || req.method !== "GET") { fail(res, 404, "not found"); return; }
        sendJson(req, res, demo.view());
        return;
      }
      if (p === "/api/library" && req.method === "GET") { const { lib, key } = await readLibrary(cfg); sendJson(req, res, lib, `lib:${key}`); return; }
      const am = /^\/api\/runs\/([^/]+)\/asset\/(.+)$/.exec(p);
      if (am && req.method === "GET") {
        const slug = decodeURIComponent(am[1]!);
        if (!validSlug(slug)) { fail(res, 404, "no such run"); return; }
        const rel = am[2]!;
        if (!ASSET_EXT.has(path.extname(decodeURIComponent(rel)).toLowerCase())) { fail(res, 403, "not a figure or PDF"); return; }
        const dir = runDir(cfg, slug);
        // a TikZ picture typeset for the page (`tikz.ts`)
        if (rel.startsWith("_tikz/")) { serveFile(req, res, safeJoin(path.join(dir, TIKZ_DIR), rel.slice("_tikz/".length)), false, true); return; }
        const base = existsSync(path.join(dir, "annotated")) ? path.join(dir, "annotated") : path.join(dir, "source");
        const file = safeJoin(base, rel);
        serveFile(req, res, existsSync(file) ? file : safeJoin(path.join(dir, "source"), rel), false, true);
        return;
      }
      const m = /^\/api\/runs\/([^/]+)(?:\/([a-z-]+))?$/.exec(p);
      if (m) {
        const slug = decodeURIComponent(m[1]!);
        if (!validSlug(slug) || !existsSync(path.join(runDir(cfg, slug), "state.json"))) { fail(res, 404, `no run ${slug}`); return; }
        const sub = m[2] ?? "";
        if ((sub === "" || sub === "drawers") && req.method === "GET") {
          // the page's detail, and apart from it what only the results' drawers show (`RunPage`,
          // `RunDrawers`): each keyed by its own content and the paper its TeX is rendered under
          const detail = await runDetail(cfg, slug, { lean: sub === "drawers" });
          const paper = await paperView(slug).catch(() => null); // the fragment renderer comes with the paper
          const part = sub ? drawersOf(detail) : pageOf(detail);
          sendView(req, res, `${sub || "page"}:${slug}`, `${paper?.key}\n${JSON.stringify(part)}`, () => JSON.stringify({ ...part, texHtml: texHtmlFor(slug, part) }));
          return;
        }
        if (sub === "paper" && req.method === "GET") { const { value, key } = await paperView(slug); sendView(req, res, `paper:${slug}`, key, () => JSON.stringify(value)); return; }
        if ((sub === "preview" || sub === "action") && req.method === "POST") {
          const body = await readBody(req) as { action?: Action };
          if (!body.action) { fail(res, 400, "no action"); return; }
          const detail = await runDetail(cfg, slug, { lean: false });
          // a run resumes, and a promotion round is applied, only under an attached agent session
          if (needsAgent(body.action) && !detail.summary.orch) { fail(res, 409, "no-orch"); return; }
          // the runner answers a render / contract checkpoint before it reads a ruling: none is sent into one
          const rcp = body.action.kind === "rule-repairs" ? renderCheckpointOf((await readJsonCached<{ verify?: unknown }>(path.join(runDir(cfg, slug), "state.json")))?.verify) : null;
          if (rcp) { fail(res, 409, `${slug} is halted at a ${rcp.kind} checkpoint, which comes before every ruling: your decisions are not sent until the agent has cleared it`); return; }
          const argv = buildArgv(body.action, { toolkitRoot: cfg.toolkitRoot, slug, source: detail.source.input });
          if (sub === "preview") { sendJson(req, res, { argv, command: displayCommand(argv) }); return; }
          if (opts.demo) {
            // the demo's stand-in agent takes it as the cue for its next step; nothing is started
            const why = opts.demo.act(body.action);
            if (why) { fail(res, 409, why); return; }
            sendJson(req, res, { pid: 0, command: displayCommand(argv), demo: true });
            return;
          }
          if (body.action.kind === "stop") {
            const { live, pid, elsewhere } = runLive(cfg, slug);
            // a runner on another machine of the mount: its pid is not a process of this one
            if (live && elsewhere) {
              // under a batch job's session, the job stops it on its machine
              if (detail.summary.orch?.starts) {
                await writeJsonAtomic(path.join(runDir(cfg, slug), START_REQUEST_FILE), { argv, command: displayCommand(argv), kind: "stop", at: new Date().toISOString() });
                sendJson(req, res, { queued: true, command: displayCommand(argv) }); return;
              }
              fail(res, 409, `${slug} runs on ${elsewhere}: stop it there — ${displayCommand(argv)}`); return;
            }
            if (live && pid) { try { process.kill(pid, "SIGTERM"); } catch { /* gone */ } }
            // Windows ends the runner at once (no signal handler runs), so its workers are stopped by
            // the CLI's own `--stop`, which reads the run's recorded children.
            if (live && process.platform === "win32") launch(argv, path.join(runDir(cfg, slug), "logs", `ui_${stamp()}.log`));
            sendJson(req, res, { stopped: live, command: displayCommand(argv) }); return;
          }
          if (runLive(cfg, slug).live) { fail(res, 409, `${slug} is running; wait for it to halt`); return; }
          const log = path.join(runDir(cfg, slug), "logs", `ui_${stamp()}.log`);
          const applying = body.action.kind === "apply-promotion" ? body.action.round : null;
          if (applying && applyOf(runDir(cfg, slug), applying) === "live") { fail(res, 409, `promotion round ${applying} of ${slug} is being applied; wait for it to end`); return; }
          if (detail.summary.orch?.starts) {
            // the attached session runs in a batch job: it starts the run there, not this
            // server (which stays a light page)
            const request = path.join(runDir(cfg, slug), START_REQUEST_FILE);
            if (existsSync(request)) { fail(res, 409, `a start of ${slug} you asked for is still waiting for the agent's job`); return; }
            await writeJsonAtomic(request, { argv, command: displayCommand(argv), kind: body.action.kind, ...(applying ? { round: applying } : {}), at: new Date().toISOString() });
            sendJson(req, res, { queued: true, command: displayCommand(argv) });
            return;
          }
          const started = launch(argv, log);
          // an apply is no runner: it reads "applying" (nothing to stop), a resume "starting"
          if (applying) markApplying(cfg, slug, applying, started);
          else markStarted(cfg, slug, started);
          sendJson(req, res, { pid: started, log, command: displayCommand(argv) });
          return;
        }
        // the demo's paper is made up: never shared, and the demo keeps no files
        if (opts.demo && (sub === "share" || sub === "share-status" || sub === "upload")) { fail(res, 409, "not in the demo"); return; }
        if (sub === "share" && (req.method === "GET" || req.method === "POST")) {
          // the owner shares a finished paper on the public site (`theoremchecker share`, in this
          // process): GET is what would be published, or the refusal; POST sends it to the share
          // service, and only with the confirmation the page's dialog collects and the key that GET
          // gave — so what is sent was shown, to a page that asked, and is still what the bundle
          // holds. The answer is the address where the owner signs in to GitHub and confirms.
          if (runLive(cfg, slug).live) { fail(res, 409, `${slug} is running: a paper is shared once its run has finished`); return; }
          const plan = () => sharePlan({ toolkitRoot: cfg.toolkitRoot, slug, deps: opts.share });
          if (req.method === "GET") {
            const p = await plan();
            for (const [k, v] of shareKeys) if (v.until < Date.now()) shareKeys.delete(k);
            const nonce = randomBytes(18).toString("base64url");
            shareKeys.set(nonce, { slug, plan: planFingerprint(p), until: Date.now() + 10 * 60_000 });
            sendJson(req, res, { ...shareView(p), nonce });
            return;
          }
          const body = await readBody(req) as { understood?: unknown; nonce?: unknown };
          if (body.understood !== true) { fail(res, 400, "not shared: the confirmation is missing"); return; }
          const key = typeof body.nonce === "string" ? shareKeys.get(body.nonce) : undefined;
          if (typeof body.nonce === "string") shareKeys.delete(body.nonce);
          if (!key || key.slug !== slug || key.until < Date.now()) { fail(res, 400, "not shared: open the Share dialog again (its confirmation is good once, for ten minutes)"); return; }
          if (sharing.has(slug)) { fail(res, 409, `${slug} is being shared; wait for it to end`); return; }
          sharing.add(slug);
          try {
            const p = await plan();
            if (planFingerprint(p) !== key.plan) { fail(res, 409, "not shared: the bundle changed after it was shown — open the Share dialog again"); return; }
            sendJson(req, res, shareRecordView(await sharePaper(p, opts.share)));
          } finally { sharing.delete(slug); }
          return;
        }
        if (sub === "share-status" && req.method === "GET") {
          // where the run's last share stands, asked of the share service at most every few seconds
          // (the page asks while it waits for the owner's confirmation in the browser)
          const dir = runDir(cfg, slug);
          let r = await readShare(dir);
          if (!r) { fail(res, 404, `${slug} has not been shared`); return; }
          if (Date.now() - (sharePolled.get(slug) ?? 0) > 2500) {
            sharePolled.set(slug, Date.now());
            try { r = await pollShare(dir, r, opts.share); } catch (e) { sendJson(req, res, { ...shareRecordView(r), unreachable: (e as Error).message }); return; }
          }
          sendJson(req, res, shareRecordView(r));
          return;
        }
        if (sub === "review" && req.method === "POST") {
          // the owner's review of a ruling the agent made: approved, or rejected with guidance (the
          // agent's watcher wakes on a rejection and acts on it)
          const body = await readBody(req) as { id?: string; verdict?: string; guidance?: string };
          const file = path.join(runDir(cfg, slug), DECISIONS_FILE);
          // a copy: the cached value stays what is on disk if the write fails
          const all = structuredClone((await readJsonCached<OrchDecision[]>(file)) ?? []);
          const d = all.find((x) => x.id === body.id);
          if (!d) { fail(res, 404, "no such decision"); return; }
          const verdict = body.verdict === "reject" ? "reject" : "approve";
          const guidance = String(body.guidance ?? "").trim();
          if (verdict === "reject" && !guidance) { fail(res, 400, "say what the agent should do instead"); return; }
          d.review = { verdict, ...(guidance ? { guidance } : {}), at: new Date().toISOString() };
          // whole (temp file, then rename): the agent's `orch.mjs decided` writes the same file
          const tmp = `${file}.${process.pid}.tmp`;
          writeFileSync(tmp, JSON.stringify(all, null, 2) + "\n");
          renameSync(tmp, file);
          sendJson(req, res, { review: d.review });
          return;
        }
        if (sub === "objection" && req.method === "POST") {
          // the owner reports an issue with a margin comment that asks no decision of them (optional;
          // the agent's watcher wakes on it): a new one on `comment`, or `id` reworded or withdrawn —
          // until the agent has acted on it
          const body = await readBody(req) as { id?: string; comment?: string; text?: string; withdraw?: boolean };
          const file = path.join(runDir(cfg, slug), OBJECTIONS_FILE);
          const all = structuredClone((await readJsonCached<OwnerObjection[]>(file)) ?? []);
          const text = String(body.text ?? "").trim();
          if (!body.withdraw && !text) { fail(res, 400, "describe the issue"); return; }
          let o = body.id ? all.find((x) => x.id === body.id) : all.find((x) => x.comment === body.comment && !x.handled);
          if (body.id && !o) { fail(res, 404, "no such report"); return; }
          if (o?.handled) { fail(res, 409, "the agent has already acted on this report"); return; }
          if (body.withdraw) { if (!o) { fail(res, 404, "no such report"); return; } all.splice(all.indexOf(o), 1); }
          else if (o) Object.assign(o, { text, at: new Date().toISOString() });
          else {
            const c = (await paperView(slug)).value?.comments.find((x) => x.key === body.comment);
            if (!c) { fail(res, 404, "no such comment"); return; }
            // a note awaiting a ruling is decided, not reported on
            if (c.kind === "rewind" || c.kind === "cap") { fail(res, 400, "this comment awaits a ruling"); return; }
            const node = (c.env && (await runDetail(cfg, slug, { lean: false })).results.find((r) => r.label === c.env)?.id) || null;
            o = { id: `obj-${1 + Math.max(0, ...all.map((x) => Number(String(x.id).slice(4)) || 0))}`, comment: c.key, node, kind: c.kind, excerpt: c.excerpt, text, at: new Date().toISOString() };
            all.push(o);
          }
          await writeJsonAtomic(file, all);
          sendJson(req, res, { objection: body.withdraw ? null : o });
          return;
        }
        if (sub === "upload" && req.method === "POST") {
          // a file the owner attaches to a message they are writing: its bytes are the body, kept in
          // the draft's folder until the message is sent (`message`). Data for the agent: never read,
          // unpacked or served back from here. Drain refused bodies without buffering: closing a
          // socket with unread upload bytes can reset it before the browser receives the error.
          const refuse = (status: number, message: string) => { req.resume(); fail(res, status, message); };
          const draft = url.searchParams.get("draft") ?? "";
          if (!/^[a-z0-9]{8,40}$/.test(draft)) { refuse(400, "no draft to attach the file to"); return; }
          const uploads = path.join(runDir(cfg, slug), "uploads"), dir = path.join(uploads, `draft-${draft}`);
          if (!plainDir(uploads) || !plainDir(dir)) { refuse(400, "the run's uploads folder is not a folder"); return; }
          // (a draft never sent — its page closed, a file refused — is cleared a day later)
          for (const d of readdirSync(uploads)) if (d.startsWith("draft-") && d !== `draft-${draft}` && Date.now() - lstatSync(path.join(uploads, d)).mtimeMs > 86_400_000) rmSync(path.join(uploads, d), { recursive: true, force: true });
          const there = readdirSync(dir);
          const name = safeUploadName(url.searchParams.get("name") ?? "", there);
          if (!UPLOAD_EXT.has(path.extname(name).toLowerCase())) { refuse(400, `${name}: not a kind of file a message carries (${[...UPLOAD_EXT].join(" ")})`); return; }
          if (there.length >= MESSAGE_LIMITS.files) { refuse(400, `a message carries at most ${MESSAGE_LIMITS.files} files`); return; }
          const room = MESSAGE_LIMITS.bytes - there.reduce((n, f) => n + lstatSync(path.join(dir, f)).size, 0);
          const tooLarge = (n: number) => n > MESSAGE_LIMITS.fileBytes ? `${name}: a file is at most ${megabytes(MESSAGE_LIMITS.fileBytes)}` : n > room ? `the files of a message are at most ${megabytes(MESSAGE_LIMITS.bytes)} together` : null;
          const announced = tooLarge(Number(req.headers["content-length"] ?? 0));
          if (announced) { refuse(413, announced); return; }
          const file = path.join(dir, name);
          // new, the owner's alone and not executable (`wx`: never through a link); stopped at the limit
          const fh = await open(file, "wx", 0o600);
          let bytes = 0, over: string | null = null;
          try {
            for await (const c of req.iterator({ destroyOnReturn: false }) as AsyncIterable<Buffer>) {
              bytes += c.length;
              if ((over = tooLarge(bytes))) break;
              await fh.write(c);
            }
          } catch (err) { rmSync(file, { force: true }); throw err; } finally { await fh.close(); }
          if (over) { rmSync(file, { force: true }); refuse(413, over); return; }
          sendJson(req, res, { name, bytes });
          return;
        }
        if (sub === "message" && req.method === "POST") {
          // the owner writes to the agent on the page — a message, or their reply to a request of
          // its own (`re`) — with the files of `draft` (`upload`). Stored for the agent, whose watcher
          // wakes on it: it is no ruling and no resume, and changes nothing in the run. A reply
          // whose request was cleared meanwhile is kept as a message that names it.
          const body = await readBody(req) as { text?: string; re?: string; draft?: string };
          const dir = runDir(cfg, slug);
          const text = String(body.text ?? "").trim();
          if (text.length > MESSAGE_LIMITS.chars) { fail(res, 400, `a message is at most ${MESSAGE_LIMITS.chars} characters`); return; }
          if (body.re !== undefined && !/^q\d+$/.test(String(body.re))) { fail(res, 400, "no such request"); return; }
          const from = body.draft === undefined ? null : path.join(dir, "uploads", `draft-${body.draft}`);
          if (from && (!/^[a-z0-9]{8,40}$/.test(String(body.draft)) || !lstatSync(from, { throwIfNoEntry: false })?.isDirectory())) { fail(res, 400, "the attached files were not received: attach them again"); return; }
          const names = from ? readdirSync(from) : [];
          const sizes = names.map((n) => lstatSync(path.join(from!, n)));
          if (names.length > MESSAGE_LIMITS.files || sizes.some((st, i) => !st.isFile() || st.size > MESSAGE_LIMITS.fileBytes || !UPLOAD_EXT.has(path.extname(names[i]!).toLowerCase())) || sizes.reduce((n, st) => n + st.size, 0) > MESSAGE_LIMITS.bytes) { fail(res, 400, "the attached files are not what a message carries"); return; }
          if (!text && !names.length) { fail(res, 400, "write the message"); return; }
          const sums = await Promise.all(names.map((n) => sha256Of(path.join(from!, n))));
          // under the store's lock (the agent's `orch.mjs` writes it too): its number, its files' folder, its entry
          const message = updateMessages(path.join(dir, MESSAGES_FILE), (all: OrchMessage[]) => {
            const id = nextMessageId(path.join(dir, MESSAGES_FILE), all, from ? readdirSync(path.join(dir, "uploads")) : []);
            if (from) renameSync(from, path.join(dir, "uploads", id));
            const files: MessageFile[] = names.map((n, i) => ({ name: n, bytes: sizes[i]!.size, sha256: sums[i]!, path: `uploads/${id}/${n}` }));
            // writing back, the owner has read what the agent said
            for (const m of all) if (m.from === "agent") m.seen = true;
            const message: OrchMessage = { id, from: "user", text, at: new Date().toISOString(), ...(body.re ? { re: body.re } : {}), ...(files.length ? { files } : {}) };
            all.push(message);
            return message;
          });
          opts.demo?.message();
          sendJson(req, res, { message });
          return;
        }
        if (sub === "message-clear" && req.method === "POST") {
          // the owner clears the conversation: archived beside the store (`orch_messages.archive.json`),
          // its files left where they are. What the agent has not acted on is not cleared away
          // unless they say so again (`force`).
          const body = await readBody(req) as { force?: boolean };
          const r = clearMessages(path.join(runDir(cfg, slug), MESSAGES_FILE), body.force === true);
          if (r.pending) { fail(res, 409, `The agent has not acted yet on ${r.pending} message(s) of yours: cleared now, ${r.pending === 1 ? "it" : "they"} would never reach it.`); return; }
          sendJson(req, res, r);
          return;
        }
        if (sub === "message-seen" && req.method === "POST") {
          // the owner has read the agent's messages
          let seen = 0;
          updateMessages(path.join(runDir(cfg, slug), MESSAGES_FILE), (all: OrchMessage[]) => {
            for (const m of all) if (m.from === "agent" && !m.seen) { m.seen = true; seen++; }
            return seen > 0;
          });
          sendJson(req, res, { seen });
          return;
        }
        if (sub === "dismiss" && req.method === "POST") {
          // the owner clears a question of the agent's they have answered (on the page, or in its session)
          const body = await readBody(req) as { id?: string };
          const file = path.join(runDir(cfg, slug), "orch_requests.json");
          const all = (await readJsonCached<Array<{ id?: string }>>(file)) ?? [];
          const rest = all.filter((r) => r.id !== body.id);
          if (rest.length === all.length) { fail(res, 404, "no such question"); return; }
          if (rest.length) { const tmp = `${file}.${process.pid}.tmp`; writeFileSync(tmp, JSON.stringify(rest, null, 2) + "\n"); renameSync(tmp, file); }
          else rmSync(file, { force: true });
          sendJson(req, res, { dismissed: body.id });
          return;
        }
        if (sub === "promotion" && req.method === "POST") {
          const body = await readBody(req) as { round?: "A" | "B"; decisions?: Record<string, ChecklistDecision> };
          const round = body.round === "A" ? "A" : "B";
          const batch = await readJsonCached<ProposalBatch>(path.join(runDir(cfg, slug), "proposals", `${round}.json`));
          if (!batch) { fail(res, 404, `no round ${round} for ${slug}`); return; }
          const decisions = await writeChecklistDecisions(checklistPath(cfg, slug, round), batch, body.decisions ?? {});
          sendJson(req, res, { decisions });
          return;
        }
        if (sub === "asset" && req.method === "GET") { fail(res, 404, "name the file"); return; }
      }
      fail(res, 404, "not found");
    } catch (err) {
      if (res.headersSent) res.destroy();
      else fail(res, 400, err instanceof Error ? err.message : String(err));
    }
  });

  await new Promise<void>((resolve, reject) => {
    server.once("error", reject);
    server.listen(opts.port, host, () => resolve());
  });
  port = (server.address() as { port: number }).port;
  watcher.start();
  // Warm every paper (those needing the owner first): the first open is instant, and formulas no
  // renderer reads are on record for the agent.
  void (async () => {
    const all = await Promise.all(listRunSlugs(cfg).map(async (s) => ({ s, needs: (await runSummary(cfg, s).catch(() => null))?.status === "needs-you" })));
    for (const { s } of all.sort((a, b) => Number(b.needs) - Number(a.needs))) { try { await warmPaper(s); } catch { /* best effort */ } }
  })();
  return {
    server, token, url: `http://${host}:${port}/?token=${token}`,
    close: async () => { watcher.stop(); for (const t of rerender.values()) clearTimeout(t); for (const c of clients) c.end(); await new Promise<void>((r) => server.close(() => r())); },
  };
}

const rank = (s: string) => ({ "needs-you": 0, running: 1, agent: 2, idle: 3, done: 4, superseded: 5 } as Record<string, number>)[s] ?? 6;
const stamp = () => new Date().toISOString().replace(/[:.]/g, "-");

/** Join under `root`, refusing an escape (`..`, absolute). */
function safeJoin(root: string, rel: string): string {
  const p = path.resolve(root, decodeURIComponent(rel));
  if (!p.startsWith(path.resolve(root) + path.sep)) return path.join(root, "__nope__");
  return p;
}
