/**
 * `paperformalizer share <slug>` — publish a finished run's bundle on the public site of shared
 * papers. The WHOLE bundle is sent, the corrected paper's TeX source and PDF included; nothing is
 * sent before the person sharing confirms.
 *
 * The bundle goes to the share service (a Cloudflare Worker of the registry, PaperFormalizerPapers):
 * the manifest first, then the bundle as one archive. The person then confirms in the browser, on
 * the service's page: they sign in to GitHub there (identity only — the sign-in app asks for no
 * permission, so the service learns their name and account and nothing else) and press "Share
 * publicly". The registry checks the paper and publishes it, or holds it for its owner's review.
 * No git, no gh and no token on this machine; `runs/<slug>/share.json` records the share and its
 * outcome, polled from the service.
 *
 * What is sent is what was shown: the bundle is read here, file by file and through no link, checked
 * against the registry's own rules before the summary, and read again at the send — a file that
 * differs from the plan by then is a refusal. The archive is made of the bytes read then.
 */
import { execFile } from "node:child_process";
import { constants } from "node:fs";
import { lstat, open, readdir, readFile, realpath } from "node:fs/promises";
import path from "node:path";
import { createInterface } from "node:readline/promises";
import { gzipSync } from "node:zlib";
import { verifyRunDir } from "../paths.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { loadToolkitConfig } from "../toolkit/config.js";
import { BUNDLE_DIR, isBlockingTodo, PAPER_DIR, type TodoItem } from "./bundle.js";
import { checkF4Seal, F4_REVIEWS_FILE, F4_SEAL_FILE, sealedPaths, sha256 } from "./f4_seal.js";
import { isFinal, readShare, SHARE_FILE, STATUSES, type ShareRecord, type ShareStatus } from "./share_record.js";
export { isFinal, readShare, SHARE_FILE, shareRecordView, type ShareRecord, type ShareStatus, type ShareView } from "./share_record.js";

/** The share service, unless `PAPERFORMALIZER_SHARE_URL` names another. The Worker keeps the name it
 *  was deployed under (its OAuth callback and secrets are bound to it): renaming the project leaves it. */
export const DEFAULT_SHARE_URL = "https://share.paperformalizer.org";
export const SHARE_URL_ENV = "PAPERFORMALIZER_SHARE_URL";
/** The public site of shared papers: a paper's page is `<site>papers/<slug>/`. */
export const SITE_URL = "https://paperformalizer.org/";
const PAGE_FILE = "page/page.json";
/** A paper folder's name in the registry. */
const REGISTRY_SLUG = /^[a-z0-9][a-z0-9_-]{0,79}$/u;

/** What the registry takes. These MIRROR its check, `checks/check_paper.mjs` of the registry
 *  (PaperFormalizerPapers) — the limits, the layout, the types a browser would run — so that a
 *  bundle it would refuse is refused here, before anything is shown or sent. Keep the two in step. */
const MAX_TOTAL_BYTES = 60 * 1024 * 1024;
const MAX_FILE_BYTES = 24 * 1024 * 1024;
const MAX_FILES = 3000;
/** A path's limit — the share service's manifest check holds it too. */
const MAX_PATH_BYTES = 255;
const TOP_FILES = new Set(["bundle.json", F4_SEAL_FILE, F4_REVIEWS_FILE, "REPORT.md", "MATCH.md", "README.md"]);
const TOP_DIRS = ["lean", PAPER_DIR, "page"];
const REQUIRED = ["bundle.json", F4_SEAL_FILE, PAGE_FILE, "REPORT.md", "MATCH.md", "lean", PAPER_DIR];
const ACTIVE_EXT = new Set([".html", ".htm", ".xhtml", ".xht", ".xml", ".js", ".mjs"]);
/** The manifest's limits of the share service. */
const MAX_TITLE = 300;
const MAX_AUTHORS = 1000;
/** How long the CLI waits for the confirmation in the browser. */
const WAIT_MS = 20 * 60_000;

export const SHARE_USAGE =
  "Usage: paperformalizer share <slug> [--toolkit <path>] [--dry-run]\n" +
  "  publish the finished run's bundle — the corrected paper's TeX source and PDF, the findings and the referee's\n" +
  `  notes, the Lean code and the report — on the public site of shared papers (${SITE_URL}). It prints what will\n` +
  "  be published and sends only after you type the slug at a terminal (or confirm on the paper's page); you then\n" +
  "  sign in to GitHub in your browser (your name and account only) and confirm there. --dry-run prints it and stops.\n" +
  `  The share service is ${SHARE_URL_ENV}, else ${DEFAULT_SHARE_URL}.`;

export interface ShareDeps {
  /** The share service's address (else `SHARE_URL_ENV`, else the default). */
  service?: string;
  fetch?: typeof fetch;
  now?: () => Date;
  /** Opens an address in the user's browser (the CLI; best effort). */
  open?: (url: string) => void;
  sleep?: (ms: number) => Promise<void>;
}

/** What a share sends: all its preconditions hold. */
export interface SharePlan {
  slug: string;
  title: string;
  authors: string;
  runDir: string;
  bundleDir: string;
  /** The share service it goes to. */
  service: string;
  /** The arXiv identifier under the seal; null when none was declared. */
  arxiv: string | null;
  /** Every file of the bundle, by its path from it, as it was read for the plan. */
  files: Array<{ rel: string; bytes: number; sha256: string }>;
  bytes: number;
  /** The bundle's top-level parts, as shown before sending. */
  parts: string[];
}

/** Where a share stands: the service's word for it. The last four are final. */


const serviceOf = (deps: ShareDeps): string => (deps.service || process.env[SHARE_URL_ENV] || DEFAULT_SHARE_URL).replace(/\/+$/u, "");
/** A paper's page on the site. */
export const paperUrl = (slug: string): string => `${SITE_URL}papers/${slug}/`;

/** A bundle as it is read: the bytes of every file by its path from the bundle, each read once,
 *  and what is there that the registry does not take. No link is followed: the bundle folder, a
 *  folder in it or a file that is one is a problem, never read through. */
async function readBundle(bundleDir: string): Promise<{ files: Map<string, Buffer>; problems: string[] }> {
  const files = new Map<string, Buffer>();
  const problems: string[] = [];
  const root = await realpath(bundleDir);
  const walk = async (rel: string): Promise<void> => {
    for (const name of (await readdir(path.join(bundleDir, rel))).sort()) {
      const r = rel ? `${rel}/${name}` : name;
      const shown = JSON.stringify(r);
      const full = path.join(bundleDir, r);
      const st = await lstat(full);
      if (name.startsWith(".")) problems.push(`${shown}: a dotfile is not part of a bundle`);
      else if (/[\\\p{Cc}]/u.test(name)) problems.push(`${shown}: the name holds a backslash or a control character`);
      else if (st.isSymbolicLink()) problems.push(`${shown}: a symbolic link (a bundle holds regular files only)`);
      else if (st.isDirectory()) await walk(r);
      else if (!st.isFile()) problems.push(`${shown}: not a regular file`);
      else if (st.size > MAX_FILE_BYTES) problems.push(`${shown}: ${st.size} bytes, over the limit of ${MAX_FILE_BYTES} for one file`);
      else {
        // (O_NOFOLLOW: a link put there since the lstat is an error, not a file read through it)
        const fh = await open(full, constants.O_RDONLY | constants.O_NOFOLLOW).catch(() => null);
        try {
          if (fh && (await fh.stat()).isFile() && (await realpath(full)) === path.join(root, r)) files.set(r, await fh.readFile());
          else problems.push(`${shown}: not a regular file of the bundle`);
        } finally {
          await fh?.close();
        }
      }
    }
  };
  await walk("");
  return { files, problems };
}

/** What keeps the bundle `files` of the run `slug` from being a paper of the registry — the rules
 *  of its `check_paper` (see the limits above), the seal included; empty when nothing does. Pure. */
function bundleProblems(slug: string, files: ReadonlyMap<string, Buffer>): string[] {
  const problems: string[] = [];
  const json = <T>(rel: string): T | null => {
    try {
      return JSON.parse(files.get(rel)!.toString("utf8")) as T;
    } catch {
      problems.push(`${rel}: does not parse as JSON`);
      return null;
    }
  };
  const names = [...files.keys()];
  for (const f of names) {
    const [head, ...rest] = f.split("/");
    // (the share writes its own: one in the bundle would stand in for it)
    if (f === SHARE_FILE) problems.push(`${SHARE_FILE}: a bundle holds none — the share writes it`);
    else if (rest.length === 0 ? !TOP_FILES.has(head!) : !TOP_DIRS.includes(head!)) problems.push(`${JSON.stringify(f)}: outside the layout of a paper folder`);
    const ext = path.extname(f).toLowerCase();
    if (ACTIVE_EXT.has(ext)) problems.push(`${JSON.stringify(f)}: a ${ext} file is not part of a bundle`);
    // (the site serves the folder as it is, and cannot keep an SVG opened on its own from running a script)
    else if (ext === ".svg") problems.push(`${JSON.stringify(f)}: an .svg file is not part of a bundle — the site cannot keep one from running a script; give the figure as PDF or PNG`);
    if (Buffer.byteLength(f, "utf8") > MAX_PATH_BYTES) problems.push(`${JSON.stringify(f)}: the path is too long for the archive (at most ${MAX_PATH_BYTES} bytes)`);
  }
  for (const r of REQUIRED) if (TOP_DIRS.includes(r) ? !names.some((f) => f.startsWith(`${r}/`)) : !files.has(r)) problems.push(`${r}: missing`);
  const total = [...files.values()].reduce((n, b) => n + b.length, 0);
  if (total > MAX_TOTAL_BYTES) problems.push(`the bundle holds ${total} bytes, over the limit of ${MAX_TOTAL_BYTES}`);
  // (and share.json)
  if (files.size + 1 > MAX_FILES) problems.push(`the bundle holds ${files.size} files, over the limit of ${MAX_FILES}`);

  const page = files.has(PAGE_FILE) ? json<{ schema?: unknown; slug?: unknown; results?: unknown; paper?: { pdf?: unknown } }>(PAGE_FILE) : null;
  if (page !== null) {
    if (page?.schema !== 1) problems.push(`${PAGE_FILE}: schema is ${JSON.stringify(page?.schema)}, not 1`);
    if (page?.slug !== slug) problems.push(`${PAGE_FILE}: its slug ${JSON.stringify(page?.slug)} is not the run's (${slug})`);
    if (!Array.isArray(page?.results)) problems.push(`${PAGE_FILE}: no results`);
  }
  if (files.has("bundle.json")) json("bundle.json");

  const seal = files.has(F4_SEAL_FILE) ? json<{ slug?: unknown }>(F4_SEAL_FILE) : null;
  if (seal !== null) {
    // the check of `paperformalizer seal`, on the bytes read here
    const named = new Set(sealedPaths(seal));
    const held = checkF4Seal(seal, { reviews: files.get(F4_REVIEWS_FILE)?.toString("utf8") ?? null, files: new Map([...named].filter((p) => files.has(p)).map((p) => [p, sha256(files.get(p)!)])) });
    problems.push(...held.map((p) => `${F4_SEAL_FILE}: ${p}`));
    if (held.length === 0) {
      if (seal.slug !== slug) problems.push(`${F4_SEAL_FILE}: its slug ${JSON.stringify(seal.slug)} is not the run's (${slug})`);
      // a file of a sealed folder that the seal does not name was added afterwards — the compiled
      // PDF apart (the one the sealed page names), which differs from one compile to the next
      const pdf = page?.paper?.pdf;
      for (const f of names) if (TOP_DIRS.includes(f.split("/")[0]!) && !named.has(f) && !(f === pdf && f.startsWith(`${PAPER_DIR}/`) && f.endsWith(".pdf"))) problems.push(`${JSON.stringify(f)}: not named by the seal`);
    }
  }
  return problems;
}

const byPath = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);
const listed = (files: ReadonlyMap<string, Buffer>): SharePlan["files"] => [...files].map(([rel, b]) => ({ rel, bytes: b.length, sha256: sha256(b) })).sort((a, b) => byPath(a.rel, b.rel));
/** What identifies a plan: where it goes and every file with its size and hash. Pure. */
export function planFingerprint(p: Pick<SharePlan, "slug" | "service" | "files">): string {
  return sha256(JSON.stringify([p.slug, p.service, p.files.map((f) => [f.rel, f.bytes, f.sha256])]));
}

/**
 * What sharing the run `slug` would send, after every precondition: the run finished, its bundle is
 * whole, in the current layout and one the registry takes, the seal holds, and nothing blocking is
 * left to do. Throws a refusal otherwise (one line per problem of the bundle). Sends nothing.
 */
export async function sharePlan(a: { toolkitRoot: string; slug: string; deps?: ShareDeps }): Promise<SharePlan> {
  const { slug } = a;
  if (!REGISTRY_SLUG.test(slug)) throw new Error(`cannot share ${slug}: a shared paper's name is lower-case letters, digits, _ and - (at most 80)`);
  const runDir = verifyRunDir(a.toolkitRoot, slug);
  const state = await readFile(path.join(runDir, "state.json"), "utf8").then((t) => JSON.parse(t) as { stage_completed?: string }, () => null);
  if (!state) throw new Error(`cannot share ${slug}: no such run under ${a.toolkitRoot}`);
  if (state.stage_completed !== "V6") throw new Error(`cannot share ${slug}: the run is not finished (its last completed stage is ${state.stage_completed ?? "none"}, not V6)`);
  const bundleDir = path.join(runDir, BUNDLE_DIR);
  const again = `write it again with \`paperformalizer report ${slug}\``;
  const top = await lstat(bundleDir).catch(() => null);
  if (top?.isSymbolicLink()) throw new Error(`cannot share ${slug}: runs/${slug}/${BUNDLE_DIR} is a symbolic link — a bundle is the folder the run wrote`);
  const { files: contents, problems } = top?.isDirectory() ? await readBundle(bundleDir) : { files: new Map<string, Buffer>(), problems: [] };
  const json = <T>(rel: string): T | null => {
    try {
      return JSON.parse(contents.get(rel)!.toString("utf8")) as T;
    } catch {
      return null;
    }
  };
  const bundle = json<{ todo_items?: TodoItem[] }>("bundle.json");
  if (!bundle) throw new Error(`cannot share ${slug}: the run has no bundle (bundle/bundle.json) — ${again}`);
  const page = json<{ title?: string; authors?: string }>(PAGE_FILE);
  if (!page) throw new Error(`cannot share ${slug}: the bundle has no ${PAGE_FILE} (an older layout, or the page snapshot was not written) — ${again}`);
  if (![...contents.keys()].some((f) => f.startsWith(`${PAPER_DIR}/`))) throw new Error(`cannot share ${slug}: the bundle has no ${PAPER_DIR}/ (an older layout) — ${again}`);
  problems.push(...bundleProblems(slug, contents));
  if (problems.length > 0) throw new Error(`cannot share ${slug}: ${problems.length === 1 ? problems[0]! : `the registry would refuse the bundle:${problems.map((p) => `\n  - ${p.replace(/\s+/gu, " ")}`).join("")}`}`);
  const blocking = (bundle.todo_items ?? []).filter(isBlockingTodo);
  if (blocking.length > 0) {
    const shown = blocking.slice(0, 5).map((i) => i.text.replace(/\s+/gu, " ").slice(0, 140)).join("; ");
    throw new Error(`cannot share ${slug}: ${blocking.length} blocking item(s) in ${PAPER_DIR}/TODO.md — ${shown}${blocking.length > 5 ? `; and ${blocking.length - 5} more` : ""}`);
  }
  const files = listed(contents);
  const seal = json<{ arxiv?: string | null }>(F4_SEAL_FILE);
  const tops = [...new Set(files.map((f) => f.rel.split("/")[0]!))];
  const count = (t: string) => files.filter((f) => f.rel.startsWith(`${t}/`)).length;
  const oneLine = (s: unknown, max: number) => (typeof s === "string" ? s : "").replace(/\s+/gu, " ").trim().slice(0, max);
  return {
    slug, title: oneLine(page.title, MAX_TITLE) || slug, authors: oneLine(page.authors, MAX_AUTHORS), runDir, bundleDir, service: serviceOf(a.deps ?? {}),
    arxiv: seal?.arxiv ?? null,
    files, bytes: files.reduce((n, f) => n + f.bytes, 0),
    parts: tops.map((t) => (files.some((f) => f.rel === t) ? t : `${t}/ (${count(t)} file${count(t) === 1 ? "" : "s"})`)),
  };
}

const size = (bytes: number): string => (bytes >= 1024 * 1024 ? `${(bytes / 1024 / 1024).toFixed(1)} MB` : `${Math.max(1, Math.round(bytes / 1024))} kB`);

/** How the share is confirmed, and by whom (the command and the page use the same words). Pure. */
export const SHARE_SIGN_IN = "You confirm in your browser: sign in to GitHub — the share service learns your name and account, nothing else, and asks for no permission — and press \"Share publicly\". The paper is attributed to that account. Unless you are one of the registry's trusted sharers, its owner reviews the paper before it is published.";
/** The warning shown before a share is sent (the command and the page use the same words). Pure. */
export function shareWarning(): string {
  return "Sharing publishes the corrected paper's TeX source and PDF, the findings and the referee's notes, the Lean code and the report on a public site, under your GitHub account. It cannot be fully undone once others have fetched it.";
}

/** What a share will publish, as the command prints it before asking. Pure. */
export function shareSummary(p: SharePlan): string {
  return [
    `Share ${p.slug}: this will be PUBLISHED`,
    "",
    `  paper      ${p.title}`,
    `  slug       ${p.slug}`,
    `  files      ${p.files.length} files, ${size(p.bytes)}`,
    `  parts      ${p.parts.join(", ")}`,
    `  public at  ${paperUrl(p.slug)}`,
    "",
    SHARE_SIGN_IN,
    "",
    `WARNING: ${shareWarning()}`,
  ].join("\n");
}

/** The plan as the page's dialog shows it. Pure. */
export function shareView(p: SharePlan): { slug: string; title: string; files: number; size: string; parts: string[]; url: string; signIn: string; warning: string } {
  return { slug: p.slug, title: p.title, files: p.files.length, size: size(p.bytes), parts: p.parts, url: paperUrl(p.slug), signIn: SHARE_SIGN_IN, warning: shareWarning() };
}

/* ── the archive: ustar, gzip'd, the same bytes for the same files ─────────────────────────── */

/** A path's ustar `prefix` and `name` (at most 155 and 100 bytes, split at a `/`); null when it
 *  cannot be stored so — the archive then gives it in a pax header (see `paxHeader`). Pure. */
export function ustarName(rel: string): { prefix: string; name: string } | null {
  const bytes = (s: string) => Buffer.byteLength(s, "utf8");
  if (bytes(rel) <= 100) return { prefix: "", name: rel };
  if (bytes(rel) > MAX_PATH_BYTES) return null;
  // the first `/` that leaves a name of at most 100 bytes
  for (let i = rel.indexOf("/"); i > 0; i = rel.indexOf("/", i + 1)) {
    const prefix = rel.slice(0, i), name = rel.slice(i + 1);
    if (bytes(prefix) <= 155 && bytes(name) <= 100 && name) return { prefix, name };
  }
  return null;
}

/** A pax record `<length> <key>=<value>\n`, the length counting itself. Pure. */
function paxRecord(key: string, value: string): Buffer {
  const body = Buffer.byteLength(` ${key}=${value}\n`, "utf8");
  let n = body + 1;
  while (String(n).length + body !== n) n = String(n).length + body;
  return Buffer.from(`${n} ${key}=${value}\n`, "utf8");
}

/** The pax header, its record and padding, that gives the next entry the path `rel`: a `path`
 *  record only, the one extension the registry's reader takes. Pure. */
function paxHeader(rel: string): Buffer[] {
  const record = paxRecord("path", rel);
  return [ustarHeader({ prefix: "", name: "PaxHeader" }, record.length, "x"), record, Buffer.alloc((512 - (record.length % 512)) % 512)];
}

/** One ustar header: mode 0644, owner 0, time 0; a regular file unless `type` says otherwise. */
function ustarHeader(at: { prefix: string; name: string }, length: number, type = "0"): Buffer {
  const h = Buffer.alloc(512);
  const put = (text: string, offset: number, width: number) => { h.write(text, offset, width, "utf8"); };
  const octal = (n: number, width: number) => n.toString(8).padStart(width - 1, "0");
  put(at.name, 0, 100);
  put(`${octal(0o644, 8)}\0`, 100, 8);
  put(`${octal(0, 8)}\0`, 108, 8);
  put(`${octal(0, 8)}\0`, 116, 8);
  put(`${octal(length, 12)}\0`, 124, 12);
  put(`${octal(0, 12)}\0`, 136, 12);
  put("        ", 148, 8);
  put(type, 156, 1);
  put("ustar\0", 257, 6);
  put("00", 263, 2);
  put(at.prefix, 345, 155);
  let sum = 0;
  for (const b of h) sum += b;
  put(`${octal(sum, 7)}\0 `, 148, 8);
  return h;
}

/** The gzip'd ustar archive of `files` (path from the bundle → bytes): regular files only, sorted
 *  by path, no directory entries — the same bytes for the same files. A path ustar cannot hold (a
 *  last part over 100 bytes) goes in a pax header before its file. Pure. */
export function bundleArchive(files: ReadonlyMap<string, Buffer>): Buffer {
  const parts: Buffer[] = [];
  for (const rel of [...files.keys()].sort(byPath)) {
    const b = files.get(rel)!;
    if (Buffer.byteLength(rel, "utf8") > MAX_PATH_BYTES) throw new Error(`${rel}: the path is too long for the archive`);
    const at = ustarName(rel);
    if (!at) parts.push(...paxHeader(rel));
    parts.push(ustarHeader(at ?? { prefix: "", name: "long-name" }, b.length), b);
    if (b.length % 512) parts.push(Buffer.alloc(512 - (b.length % 512)));
  }
  parts.push(Buffer.alloc(1024));
  return gzipSync(Buffer.concat(parts));
}

/** The manifest the share service is sent first (see the registry's worker). Pure. */
export function shareManifest(p: SharePlan, archive: Buffer): { v: 1; slug: string; title: string; authors: string; arxiv: string | null; files: Array<{ path: string; size: number; sha256: string }>; archive: { size: number; sha256: string } } {
  return { v: 1, slug: p.slug, title: p.title, authors: p.authors, arxiv: p.arxiv, files: p.files.map((f) => ({ path: f.rel, size: f.bytes, sha256: f.sha256 })), archive: { size: archive.length, sha256: sha256(archive) } };
}

/* ── the service ─────────────────────────────────────────────────────────────────────────────── */

/** A call to the share service; its JSON answer, or a refusal naming what it said. */
async function call<T>(deps: ShareDeps, service: string, method: string, url: string, init: { token?: string; json?: unknown; body?: Buffer } = {}): Promise<T> {
  const headers: Record<string, string> = {};
  if (init.token) headers.Authorization = `Bearer ${init.token}`;
  if (init.json !== undefined) headers["Content-Type"] = "application/json";
  if (init.body) headers["Content-Type"] = "application/gzip";
  let r: Response;
  try {
    r = await (deps.fetch ?? fetch)(url, { method, headers, body: init.json !== undefined ? JSON.stringify(init.json) : init.body ? new Uint8Array(init.body) : undefined, redirect: "error" });
  } catch (e) {
    throw new Error(`the share service at ${service} could not be reached (${(e as Error).message})`);
  }
  const text = await r.text();
  let body: unknown = null;
  try { body = JSON.parse(text); } catch { /* not JSON */ }
  if (!r.ok) throw Object.assign(new Error(`the share service answered ${r.status}: ${plain(String((body as { error?: unknown } | null)?.error ?? (text.trim().slice(0, 200) || r.statusText)))}`), { status: r.status });
  if (!body || typeof body !== "object") throw new Error(`the share service answered ${r.status} with no JSON`);
  return body as T;
}
/** Text from the service with its control characters (terminal escapes among them) made spaces. */
const plain = (t: string): string => t.replace(/\p{Cc}/gu, " ");
/** A pull request of the registry: the only review link the page and the command show. */
const REGISTRY_PULL = /^https:\/\/github\.com\/Jiyuan-Tan\/PaperFormalizerPapers\/pull\/\d+$/u;

/** An address the service gave: on the service itself, else not followed. */
function ownUrl(service: string, url: unknown, what: string): string {
  if (typeof url === "string") {
    try { if (new URL(url).origin === new URL(service).origin) return url; } catch { /* not an address */ }
  }
  throw new Error(`the share service gave a ${what} that is not on ${service}: ${JSON.stringify(url)}`);
}

/**
 * Send the bundle of `p` to the share service: the manifest, then the archive. Called only after
 * the confirmation. The bundle is read again here, and a difference from the plan is a refusal:
 * nothing is sent. Records the share in the run (`share.json`), waiting for the sign-in.
 */
export async function sharePaper(p: SharePlan, deps: ShareDeps = {}): Promise<ShareRecord> {
  // what is sent is what the plan showed: a file changed, added, removed or made a link since is a refusal
  const top = await lstat(p.bundleDir).catch(() => null);
  const { files: contents, problems } = top?.isDirectory() ? await readBundle(p.bundleDir) : { files: new Map<string, Buffer>(), problems: [`${BUNDLE_DIR}/ is not a folder`] };
  problems.push(...bundleProblems(p.slug, contents));
  if (problems.length === 0 && planFingerprint({ ...p, files: listed(contents) }) !== planFingerprint(p)) problems.push("its files are not the ones that were shown");
  if (problems.length > 0) throw new Error(`not shared: the bundle of ${p.slug} changed after it was shown (${problems[0]!.replace(/\s+/gu, " ")}${problems.length > 1 ? `, and ${problems.length - 1} more` : ""}) — share again to see what would be sent`);
  const archive = bundleArchive(contents);
  const fail = (e: Error): never => { throw new Error(`not shared: ${e.message}`); };
  const up = await call<{ id?: unknown; upload_url?: unknown; claim_url?: unknown; poll_token?: unknown; check_code?: unknown; expires_at?: unknown }>(deps, p.service, "POST", `${p.service}/api/uploads`, { json: shareManifest(p, archive) }).catch(fail);
  if (typeof up.id !== "string" || !/^[a-z2-7]{26}$/u.test(up.id) || typeof up.poll_token !== "string" || typeof up.check_code !== "string" || !/^[A-Z2-9]{4}$/u.test(up.check_code)) fail(new Error("the share service's answer is not one of an upload"));
  const uploadUrl = (() => { try { return ownUrl(p.service, up.upload_url, "upload address"); } catch (e) { return fail(e as Error); } })();
  const claimUrl = (() => { try { return ownUrl(p.service, up.claim_url, "sign-in address"); } catch (e) { return fail(e as Error); } })();
  const token = up.poll_token as string;
  await call(deps, p.service, "PUT", uploadUrl, { token, body: archive }).catch(fail);
  const at = (deps.now?.() ?? new Date()).toISOString();
  const record: ShareRecord = {
    slug: p.slug, service: p.service, id: up.id as string, poll_token: token, claim_url: claimUrl, check_code: up.check_code as string,
    expires_at: typeof up.expires_at === "string" ? up.expires_at : "", started_at: at, status: "awaiting_sign_in", updated_at: at,
  };
  await writeJsonAtomic(path.join(p.runDir, SHARE_FILE), record);
  return record;
}


/** Where the share `r` of the run at `runDir` stands now, asked of its service; the record is
 *  written again when it moved. A final share is not asked again. */
export async function pollShare(runDir: string, r: ShareRecord, deps: ShareDeps = {}): Promise<ShareRecord> {
  if (isFinal(r.status)) return r;
  let next: ShareRecord;
  try {
    const s = await call<{ status?: unknown; login?: unknown; result?: { url?: unknown; pr_url?: unknown; problems?: unknown } }>(deps, r.service, "GET", `${r.service}/api/uploads/${r.id}`, { token: r.poll_token });
    if (typeof s.status !== "string" || !STATUSES.has(s.status)) throw new Error(`the share service gave an unknown status ${JSON.stringify(plain(String(s.status)))}`);
    // the links shown are the registry's own: the paper's page on the site, a pull request of the registry
    const url = s.result?.url === paperUrl(r.slug) ? paperUrl(r.slug) : undefined;
    const pr = typeof s.result?.pr_url === "string" && REGISTRY_PULL.test(s.result.pr_url) ? s.result.pr_url : undefined;
    next = {
      ...r, status: s.status as ShareStatus,
      ...(typeof s.login === "string" && /^[A-Za-z0-9-]{1,39}$/u.test(s.login) ? { login: s.login } : {}),
      ...(url ? { url } : {}),
      ...(pr ? { pr_url: pr } : {}),
      ...(Array.isArray(s.result?.problems) ? { problems: s.result.problems.filter((x): x is string => typeof x === "string").slice(0, 50).map((x) => plain(x).slice(0, 500)) } : {}),
    };
  } catch (e) {
    // a share the service no longer knows (its record expired, or the service was replaced) is over
    if ((e as { status?: number }).status !== 404) throw e;
    next = { ...r, status: "expired", note: "the share service no longer knows this share" };
  }
  if (JSON.stringify({ ...next, updated_at: "" }) === JSON.stringify({ ...r, updated_at: "" })) return r;
  next.updated_at = (deps.now?.() ?? new Date()).toISOString();
  await writeJsonAtomic(path.join(runDir, SHARE_FILE), next);
  return next;
}

/** A final share in one sentence (the command's last line). Pure. */
export function shareOutcome(r: ShareRecord): string {
  if (r.status === "published") return `published: ${r.url ?? paperUrl(r.slug)}`;
  if (r.status === "review") return `sent for review: the registry's owner reviews the paper before it is published${r.pr_url ? ` — ${r.pr_url}` : ""}`;
  if (r.status === "refused") return `not published: the registry refused the paper${(r.problems ?? []).map((p) => `\n  - ${p}`).join("")}`;
  if (r.status === "expired") return `not shared: ${r.note ?? "the sign-in was not completed in time"} — share again`;
  return `waiting (${r.status.replace(/_/gu, " ")})`;
}

/** Opens an address in the browser, best effort (nothing waits on it, a failure is silent). */
const openBrowser = (url: string): void => {
  const cmd = process.platform === "darwin" ? "open" : process.platform === "win32" ? "explorer" : "xdg-open";
  try { execFile(cmd, [url], { timeout: 10_000, windowsHide: true }, () => {}).unref(); } catch { /* no browser */ }
};

/** `paperformalizer share <slug>`: show what will be published, ask, send, then wait for the
 *  confirmation in the browser. It sends only when the person at the terminal types the slug: no
 *  flag answers for them, and without a terminal it refuses. */
export async function runShareCli(argv: string[], deps: ShareDeps & { log?: (m: string) => void; ask?: (question: string) => Promise<string>; tty?: boolean } = {}): Promise<void> {
  const log = deps.log ?? ((m: string) => console.log(m));
  let slug: string | null = null;
  let toolkit: string | null = null;
  let dryRun = false;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i]!;
    if (a === "--toolkit") {
      const v = argv[i + 1];
      if (!v || v.startsWith("--")) throw new Error(`${a} needs a value.\n${SHARE_USAGE}`);
      toolkit = v;
      i += 1;
    } else if (a === "--dry-run") dryRun = true;
    else if (a.startsWith("--")) throw new Error(`unknown flag ${a}.\n${SHARE_USAGE}`);
    else if (slug === null) slug = a;
    else throw new Error(`one slug only.\n${SHARE_USAGE}`);
  }
  if (!slug) throw new Error(SHARE_USAGE);
  const cfg = loadToolkitConfig({ explicit: toolkit });
  const plan = await sharePlan({ toolkitRoot: cfg.toolkitRoot, slug, deps });
  log(shareSummary(plan));
  if (dryRun) { log("\ndry run: nothing was sent."); return; }
  const tty = deps.tty ?? (process.stdin.isTTY === true && process.stdout.isTTY === true);
  if (!tty) throw new Error("not shared: sharing asks for confirmation at a terminal or on the paper's page.");
  // (an input that ends without an answer is a no)
  const ask = deps.ask ?? ((q: string) => new Promise<string>((resolve) => {
    const rl = createInterface({ input: process.stdin, output: process.stdout });
    rl.once("close", () => resolve(""));
    void rl.question(q).then((answer) => { resolve(answer); rl.close(); }, () => resolve(""));
  }));
  if ((await ask(`\nType the slug (${slug}) to share it: `)).trim() !== slug) throw new Error("not shared: the answer was not the slug.");
  log(`Sending ${plan.files.length} files to ${plan.service} …`);
  let r = await sharePaper(plan, deps);
  log([
    "",
    "Sent. To finish, open this page, sign in to GitHub and press \"Share publicly\":",
    `  ${r.claim_url}`,
    `Check code: ${r.check_code} (the page you open shows the same code; continue only if it does).`,
    "",
    "Waiting for your confirmation (Ctrl-C stops waiting; the paper's page shows the outcome) …",
  ].join("\n"));
  (deps.open ?? openBrowser)(r.claim_url);
  const sleep = deps.sleep ?? ((ms: number) => new Promise<void>((res) => setTimeout(res, ms)));
  const start = Date.now();
  let was = r.status;
  while (!isFinal(r.status) && Date.now() - start < WAIT_MS) {
    await sleep(3000);
    try { r = await pollShare(plan.runDir, r, deps); } catch (e) { log(`(could not read the share's status: ${(e as Error).message}; trying again)`); continue; }
    if (r.status === "submitted" && was !== "submitted") log(`confirmed by @${r.login ?? "?"}: the registry is checking the paper …`);
    was = r.status;
  }
  if (!isFinal(r.status)) { log(`still waiting after ${WAIT_MS / 60_000} minutes; the paper's page shows the outcome once you confirm (the link stays good until ${r.expires_at || "it expires"}).`); return; }
  if (r.status === "refused" || r.status === "expired") throw new Error(shareOutcome(r));
  log(shareOutcome(r));
}
