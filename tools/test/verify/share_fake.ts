// A share service and a finished run to share, for tests: the service is a `fetch` answering the
// Worker's upload API in memory, the run a small bundle in the current layout, sealed. Nothing here
// reaches a network.
import { createHash, randomBytes } from "node:crypto";
import { chmod, mkdir, mkdtemp, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { gunzipSync } from "node:zlib";
import { sha256, withBundle, type F4Seal } from "../../src/verify/f4_seal.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";

export const SLUG = "a_paper";
export const SERVICE = "https://share.test";
/** The directories made here, for the test to remove. */
export const tmpDirs: string[] = [];
export const tmp = async (name: string): Promise<string> => { const d = await mkdtemp(path.join(os.tmpdir(), `tc-share-${name}-`)); tmpDirs.push(d); return d; };

/** One entry of an archive as a reader sees it. */
export interface TarEntry { path: string; name: string; prefix: string; mode: string; type: string; bytes: Buffer }
/** The entries of a gzip'd ustar archive, in order (a minimal reader: what the registry's ingest does). */
export function readArchive(gz: Buffer): TarEntry[] {
  const tar = gunzipSync(gz);
  const out: TarEntry[] = [];
  const field = (h: Buffer, at: number, n: number) => h.subarray(at, at + n).toString("utf8").replace(/\0.*$/su, "");
  // the path a pax header gave the next entry
  let pax: string | null = null;
  for (let at = 0; at + 512 <= tar.length;) {
    const h = tar.subarray(at, at + 512);
    if (h.every((b) => b === 0)) break;
    // the checksum: the header's bytes with its own field read as spaces
    const sum = [...h].reduce((n, b, i) => n + (i >= 148 && i < 156 ? 32 : b), 0);
    if (parseInt(field(h, 148, 8), 8) !== sum) throw new Error(`bad checksum at ${at}`);
    if (field(h, 257, 6) !== "ustar") throw new Error(`not ustar at ${at}`);
    const name = field(h, 0, 100), prefix = field(h, 345, 155);
    const size = parseInt(field(h, 124, 12), 8);
    const bytes = Buffer.from(tar.subarray(at + 512, at + 512 + size));
    if (field(h, 156, 1) === "x") {
      const m = /^(\d+) path=(.*)\n$/su.exec(bytes.toString("utf8"));
      if (!m || Number(m[1]) !== size) throw new Error(`a pax header at ${at} that is not one path record`);
      pax = m[2]!;
    } else {
      out.push({ path: pax ?? (prefix ? `${prefix}/${name}` : name), name, prefix, mode: field(h, 100, 8), type: field(h, 156, 1), bytes });
      pax = null;
    }
    at += 512 + Math.ceil(size / 512) * 512;
  }
  return out;
}

type Upload = { manifest: { slug: string; files: Array<{ path: string; size: number; sha256: string }>; archive: { size: number; sha256: string } }; token: string; status: string; archive?: Buffer; login?: string; result?: Record<string, unknown> };
/** The share service, in memory: `fetch` answers its upload API (POST manifest, PUT archive, GET
 *  status); `confirm` and `finish` stand in for the sign-in and the registry's ingest. */
export function fakeService(base = SERVICE): { fetch: typeof fetch; uploads: Map<string, Upload>; calls: string[]; confirm: (id: string, login: string) => void; finish: (id: string, result: Record<string, unknown> & { kind: string }) => void; answer: { refuse?: string; claimUrl?: string; down?: boolean } } {
  const uploads = new Map<string, Upload>();
  const calls: string[] = [];
  const answer: { refuse?: string; claimUrl?: string; down?: boolean } = {};
  const json = (status: number, body: unknown) => new Response(JSON.stringify(body), { status, headers: { "Content-Type": "application/json" } });
  const hash = (s: string) => createHash("sha256").update(s).digest("hex");
  const f = async (input: string | URL | Request, init: RequestInit = {}): Promise<Response> => {
    const url = new URL(String(input));
    const method = init.method ?? "GET";
    calls.push(`${method} ${url.pathname}`);
    if (answer.down) throw new TypeError("fetch failed");
    if (url.origin !== base) return json(404, { error: "not this service" });
    const auth = (init.headers as Record<string, string> | undefined)?.Authorization ?? "";
    if (method === "POST" && url.pathname === "/api/uploads") {
      if (answer.refuse) return json(400, { error: answer.refuse });
      const manifest = JSON.parse(String(init.body)) as Upload["manifest"];
      const id = randomBytes(16).toString("hex").replace(/[^a-z2-7]/gu, "a").padEnd(26, "a").slice(0, 26);
      const token = randomBytes(32).toString("base64url");
      uploads.set(id, { manifest, token: hash(token), status: "awaiting_upload" });
      return json(201, { id, upload_url: `${base}/api/uploads/${id}`, claim_url: answer.claimUrl ?? `${base}/claim/${id}`, poll_token: token, check_code: "K7PQ", expires_at: "2026-10-09T13:00:00.000Z" });
    }
    const m = /^\/api\/uploads\/([a-z2-7]{26})$/u.exec(url.pathname);
    const u = m ? uploads.get(m[1]!) : undefined;
    if (!u) return json(404, { error: "no such upload" });
    if (hash(auth.replace(/^Bearer /u, "")) !== u.token) return json(401, { error: "not your upload" });
    if (method === "PUT") {
      const body = Buffer.from(init.body as Uint8Array);
      if (u.status !== "awaiting_upload") return json(409, { error: "already uploaded" });
      if (body.length !== u.manifest.archive.size || sha256(body) !== u.manifest.archive.sha256) return json(400, { error: "the archive is not the one the manifest names" });
      u.archive = body;
      u.status = "awaiting_sign_in";
      return json(200, { status: u.status });
    }
    return json(200, { status: u.status, check_code: "K7PQ", ...(u.login ? { login: u.login } : {}), ...(u.result ? { result: u.result } : {}) });
  };
  return {
    fetch: f as typeof fetch, uploads, calls, answer,
    confirm: (id, login) => { const u = uploads.get(id)!; u.status = "submitted"; u.login = login; },
    finish: (id, result) => { const u = uploads.get(id)!; u.status = result.kind; u.result = result; },
  };
}

/** A toolkit with one finished run and its bundle in the current layout, sealed. */
export async function finishedRun(): Promise<{ root: string; run: string; bundle: string }> {
  const root = await tmp("toolkit");
  await writeFile(path.join(root, "paperformalizer.json"), JSON.stringify(TOOLKIT_JSON));
  const run = path.join(root, "runs", SLUG);
  const bundle = path.join(run, "bundle");
  const files: Record<string, string> = {
    "bundle.json": JSON.stringify({ slug: SLUG, lean: { files: 1 }, todo: { total: 1, blocking: 0 }, todo_items: [{ group: "numbering", file: null, line: null, text: "a new number" }] }),
    "REPORT.md": "# Report\n",
    "MATCH.md": "# Match\n",
    "f4_reviews.log": "===== reviewer convergence/1\nmatched\n",
    "page/page.json": JSON.stringify({ schema: 1, slug: SLUG, title: "A  Paper on\nBounds", authors: "A. Author and\nB. Author", results: [], paper: { pdf: "corrected_paper/main.pdf" } }),
    "corrected_paper/main.tex": "\\documentclass{article}\\begin{document}x\\end{document}\n",
    "corrected_paper/TODO.md": "# TODO\n",
    "corrected_paper/main.pdf": "%PDF-1.5 not sealed\n",
    "lean/Papers/APaper/Main.lean": "theorem t : True := trivial\n",
    "lean/lakefile.toml": 'name = "p"\n',
  };
  for (const [rel, text] of Object.entries(files)) {
    await mkdir(path.dirname(path.join(bundle, rel)), { recursive: true });
    await writeFile(path.join(bundle, rel), text);
  }
  // some source files carry the executable bit
  await chmod(path.join(bundle, "corrected_paper", "main.tex"), 0o755);
  const receipt = { verdict: "matched", evidence_hash: "e" };
  const seal: F4Seal = { version: 1, slug: SLUG, paper_sha256: "p", arxiv: "2105.15197", review_standard: "s", targets: [{ id: "thm:t", codex: receipt, claude: receipt }], unreviewed: [], delivery: [], cited: [], reviews_sha256: null, files: [], code: "" };
  const sealed = Object.entries(files).filter(([rel]) => /^(lean|corrected_paper|page)\//.test(rel) && !rel.endsWith(".pdf"));
  await writeFile(path.join(bundle, "f4_seal.json"), JSON.stringify(withBundle(seal, { reviews: files["f4_reviews.log"]!, files: new Map(sealed.map(([rel, text]) => [rel, sha256(text)])) }), null, 2));
  await writeFile(path.join(run, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "done" } }));
  return { root, run, bundle };
}
