/**
 * `theoremchecker verify` — materialise the user's paper source under `<runDir>/source/`.
 *
 * The input is whatever the user has: a single `.tex`, a directory, a `.zip`, a `.tar`,
 * a `.tar.gz`/`.tgz`, or one of arXiv's extensionless downloads (a bare gzip stream that
 * is either a single `.tex` or a gzipped tar). The kind is decided by MAGIC BYTES, never
 * by the extension, because arXiv's file has none. A bare `.tex` that includes files lying
 * beside it is taken with its directory (`texSiblings`).
 *
 * Everything here is fail-closed. An archive is LISTED before it is extracted and any
 * member whose name escapes the target (`..`, a leading `/`, a drive letter) aborts the
 * run untouched; after extraction the tree is walked and any symlink — or any entry
 * whose `realpath` leaves `sourceDir` — deletes the whole directory and throws. The
 * directory is wiped and recreated first, so a re-run never mixes two papers.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { lstat, mkdir, mkdtemp, open, readFile, readdir, realpath, rename, rm, stat, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { gunzipSync } from "node:zlib";
import { execFileTracked } from "../shared/child_registry.js";
import { blankTexComments } from "../shared/tex_text.js";
import type { PrepareSource, PreparedSource } from "./types.js";

const run = (cmd: string, args: string[], opts: { timeout?: number; maxBuffer?: number } = {}) =>
  execFileTracked("extract", cmd, args, opts);

/** Basenames preferred when several files could be the main one, in order. */
const PREFERRED_MAIN = ["main.tex", "paper.tex", "ms.tex", "arxiv.tex"];

/** Ceiling on what one gzip input may expand to. A gzip bomb is a few kilobytes on
 * disk and gigabytes in memory; without a cap the process just dies. 256 MiB is far
 * above any real paper source (arXiv's own limit is a small fraction of it).
 * Mutable so the refusal path can be tested without building a 256 MiB payload. */
export const GUNZIP_LIMITS = { maxOutputBytes: 256 * 1024 * 1024 };

/** Decompress a gzip input under `GUNZIP_LIMITS`, turning the cap's raw zlib failure
 * into a message that says what to do next. */
function gunzipCapped(data: Buffer, what: string): Buffer {
  const max = GUNZIP_LIMITS.maxOutputBytes;
  try {
    return gunzipSync(data, { maxOutputLength: max });
  } catch (err) {
    const message = (err as Error).message ?? String(err);
    if (/buffer|maxOutputLength|larger than/i.test(message)) {
      const shown = max >= 1024 * 1024 ? `${Math.round(max / (1024 * 1024))} MiB` : `${max} bytes`;
      throw new Error(
        `${what} expands to more than ${shown} of data; refusing to unpack it. Unpack it ` +
          `yourself and pass the directory to \`theoremchecker verify\`.`,
      );
    }
    throw new Error(`${what} is not readable as a gzip stream: ${message}`);
  }
}

// ---------------------------------------------------------------------------
// magic-byte sniffing
// ---------------------------------------------------------------------------

function isGzip(head: Buffer): boolean {
  return head.length >= 2 && head[0] === 0x1f && head[1] === 0x8b;
}

function isZip(head: Buffer): boolean {
  return (
    head.length >= 4 && head[0] === 0x50 && head[1] === 0x4b && head[2] === 0x03 && head[3] === 0x04
  );
}

/** A tar holds the magic `ustar` at offset 257 (POSIX and GNU alike). */
function isTar(head: Buffer): boolean {
  return head.length >= 262 && head.subarray(257, 262).toString("latin1") === "ustar";
}

async function readHead(file: string, bytes = 512): Promise<Buffer> {
  const fh = await open(file, "r");
  try {
    const buf = Buffer.alloc(bytes);
    const { bytesRead } = await fh.read(buf, 0, bytes, 0);
    return buf.subarray(0, bytesRead);
  } finally {
    await fh.close();
  }
}

// ---------------------------------------------------------------------------
// external extractors
// ---------------------------------------------------------------------------

async function requireTool(tool: string, why: string): Promise<void> {
  try {
    await run(tool, ["--help"], { timeout: 20_000 });
  } catch (err) {
    const code = (err as { code?: string }).code;
    if (code === "ENOENT") {
      throw new Error(
        `\`${tool}\` is not installed but is required to ${why}. Install it, or unpack the ` +
          `archive yourself and pass the directory to \`theoremchecker verify\`.`,
      );
    }
    // A non-zero exit from `--help` (some `unzip` builds) still proves the binary runs.
  }
}

/** Reject a member name that could escape the extraction directory. Applied to the
 * archive LISTING, before a single byte is written. */
function assertSafeMembers(names: string[], archive: string): void {
  for (const raw of names) {
    const name = raw.trim();
    if (!name) continue;
    const bad =
      name.startsWith("/") ||
      name.startsWith("\\") ||
      /^[A-Za-z]:[\\/]/.test(name) ||
      name.split(/[\\/]/).includes("..");
    if (bad) {
      throw new Error(
        `refusing to extract ${path.basename(archive)}: member "${name}" escapes the ` +
          `destination directory`,
      );
    }
  }
}

async function extractZip(archive: string, dest: string): Promise<void> {
  await requireTool("unzip", "extract a .zip source bundle");
  const { stdout } = await run("unzip", ["-Z1", archive], { maxBuffer: 64 * 1024 * 1024 });
  assertSafeMembers(stdout.split("\n"), archive);
  // `-n` never overwrites, `-qq` is quiet, `-d` confines the output to `dest`.
  await run("unzip", ["-qq", "-n", archive, "-d", dest], { maxBuffer: 64 * 1024 * 1024 });
}

async function extractTar(archive: string, dest: string): Promise<void> {
  await requireTool("tar", "extract a .tar / .tar.gz source bundle");
  const { stdout } = await run("tar", ["-tf", archive], { maxBuffer: 64 * 1024 * 1024 });
  assertSafeMembers(stdout.split("\n"), archive);
  await run("tar", ["-xf", archive, "-C", dest, "--no-same-owner"], {
    maxBuffer: 64 * 1024 * 1024,
  });
}

// ---------------------------------------------------------------------------
// security walk
// ---------------------------------------------------------------------------

/** Shallowest first, then alphabetically: the order every tie-break and every error
 * message below relies on. */
function comparePaths(a: string, b: string): number {
  const depth = a.split("/").length - b.split("/").length;
  if (depth !== 0) return depth;
  return a < b ? -1 : a > b ? 1 : 0;
}

/** Every file under `dir`, relative and POSIX-separated, in a DETERMINISTIC order.
 * `readdir` returns filesystem order, which differs between machines and between a
 * fresh extraction and a re-run — so without the sort the main-file tie-break would
 * too. */
async function listTree(dir: string): Promise<string[]> {
  const walk = async (at: string): Promise<string[]> => {
    const out: string[] = [];
    for (const entry of await readdir(at, { withFileTypes: true })) {
      const abs = path.join(at, entry.name);
      if (entry.isDirectory()) out.push(...(await walk(abs)));
      else out.push(path.relative(dir, abs).split(path.sep).join("/"));
    }
    return out;
  };
  return (await walk(dir)).sort(comparePaths);
}

/** Walk every entry and refuse a symlink or anything whose realpath leaves `sourceDir`.
 * On refusal the directory is removed: a half-trusted tree is worse than none. */
async function assertNoEscapes(sourceDir: string): Promise<void> {
  const root = await realpath(sourceDir);
  const walk = async (dir: string): Promise<void> => {
    for (const entry of await readdir(dir, { withFileTypes: true })) {
      const abs = path.join(dir, entry.name);
      const info = await lstat(abs);
      if (info.isSymbolicLink()) {
        throw new Error(
          `refusing source tree: ${path.relative(sourceDir, abs)} is a symbolic link`,
        );
      }
      if (!info.isDirectory() && !info.isFile()) {
        throw new Error(
          `refusing source tree: ${path.relative(sourceDir, abs)} is neither a file nor a directory`,
        );
      }
      const real = await realpath(abs);
      const rel = path.relative(root, real);
      if (rel.startsWith("..") || path.isAbsolute(rel)) {
        throw new Error(
          `refusing source tree: ${path.relative(sourceDir, abs)} resolves outside the source directory`,
        );
      }
      if (info.isDirectory()) await walk(abs);
    }
  };
  try {
    await walk(sourceDir);
  } catch (err) {
    await rm(sourceDir, { recursive: true, force: true });
    throw err;
  }
}

/** Archives usually wrap everything in one top-level folder; lift its children up so
 * `mainFile` is relative to `sourceDir` itself. */
async function flattenSingleTopLevelDir(sourceDir: string): Promise<void> {
  const entries = await readdir(sourceDir, { withFileTypes: true });
  const real = entries.filter((e) => !(e.isFile() && e.name === ".DS_Store"));
  if (real.length !== 1 || !real[0]!.isDirectory()) return;
  const inner = path.join(sourceDir, real[0]!.name);
  const staged = path.join(path.dirname(sourceDir), `.${path.basename(sourceDir)}.lift`);
  await rm(staged, { recursive: true, force: true });
  await rename(inner, staged);
  await rm(sourceDir, { recursive: true, force: true });
  await rename(staged, sourceDir);
}

// ---------------------------------------------------------------------------
// main-file detection
// ---------------------------------------------------------------------------

interface Candidate {
  rel: string;
  inputs: number;
}

/** Pick the paper's main `.tex` under `sourceDir` (honouring the user's `--main`).
 * Exported so the candidate rules can be tested directly, without a bundle whose file
 * modes would have to survive a copy. */
export async function detectMainFile(sourceDir: string, mainHint?: string | null): Promise<string> {
  const files = await listTree(sourceDir);
  if (mainHint) {
    const rel = mainHint.split(path.sep).join("/").replace(/^\.\//, "");
    const abs = path.resolve(sourceDir, rel);
    const inside = path.relative(sourceDir, abs);
    if (inside.startsWith("..") || path.isAbsolute(inside)) {
      throw new Error(`--main ${mainHint} points outside the source directory`);
    }
    if (!existsSync(abs)) {
      throw new Error(
        `--main ${mainHint} does not exist in the source. Files present: ${files.join(", ")}`,
      );
    }
    const info = await stat(abs);
    if (!info.isFile()) {
      throw new Error(
        `--main ${mainHint} is ${info.isDirectory() ? "a directory" : "not a regular file"}, ` +
          `not a .tex file. Pass the path of the main .tex file itself.`,
      );
    }
    return inside.split(path.sep).join("/");
  }
  const texFiles = files.filter((f) => /\.tex$/i.test(f));
  const candidates: Candidate[] = [];
  // Every file some other .tex file includes (by `\input`/`\include`/`\subfile`), by base name:
  // the main file is a ROOT of the inclusion graph, whatever it is called.
  const included = new Set<string>();
  for (const rel of texFiles) {
    let text: string;
    try {
      text = blankTexComments(await readFile(path.join(sourceDir, rel), "utf8"));
    } catch {
      continue;
    }
    for (const m of text.matchAll(/\\(?:input|include|subfile)(?![a-zA-Z@])\s*\{([^{}]*)\}/g)) {
      included.add(path.basename(m[1]!.trim()).replace(/\.tex$/i, "").toLowerCase());
    }
  }
  for (const rel of texFiles) {
    // No `.catch(() => "")` here: a `.tex` we cannot read is a broken bundle, and
    // swallowing the error would drop the real main file and let a decoy win.
    let text: string;
    try {
      text = await readFile(path.join(sourceDir, rel), "utf8");
    } catch (err) {
      throw new Error(
        `cannot read ${rel} while looking for the main .tex file: ${(err as Error).message}`,
      );
    }
    // a commented-out `\documentclass` (a template's alternatives) or `\input` is none
    text = blankTexComments(text);
    if (!/\\documentclass/.test(text) || !/\\begin\s*\{document\}/.test(text)) continue;
    // A `subfiles` child compiles alone but is a BODY of the real main file, never the main;
    // nor is any file another file includes.
    if (/\\documentclass\s*\[[^\]]*\]\s*\{subfiles\}/.test(text)) continue;
    if (included.has(path.basename(rel).replace(/\.tex$/i, "").toLowerCase())) continue;
    candidates.push({
      rel,
      inputs: [...text.matchAll(/\\(input|include|subfile)(?![a-zA-Z@])/g)].length,
    });
  }
  if (candidates.length === 0) {
    // A fragment with no `\documentclass` is still usable when it is the only `.tex`
    // in the bundle (arXiv sources built by a wrapper sometimes look like this).
    if (texFiles.length === 1) return texFiles[0]!;
    throw new Error(
      `no main file found: no .tex file contains both \\documentclass and \\begin{document} ` +
        `(.tex files: ${texFiles.join(", ") || "none"}). Pass --main <relpath>.`,
    );
  }
  if (candidates.length === 1) return candidates[0]!.rel;
  for (const preferred of PREFERRED_MAIN) {
    const hit = candidates.find((c) => path.basename(c.rel).toLowerCase() === preferred);
    if (hit) return hit.rel;
  }
  const most = Math.max(...candidates.map((c) => c.inputs));
  const leaders = candidates.filter((c) => c.inputs === most);
  if (most > 0 && leaders.length === 1) return leaders[0]!.rel;
  // Still tied: prefer a candidate that sits strictly closer to the root — a paper's
  // main file is not usually buried under a subdirectory of one that is not.
  const depth = (rel: string): number => rel.split("/").length;
  const shallowest = Math.min(...leaders.map((c) => depth(c.rel)));
  const top = leaders.filter((c) => depth(c.rel) === shallowest);
  if (top.length === 1) return top[0]!.rel;
  throw new Error(
    `ambiguous main file: ${candidates.map((c) => c.rel).join(", ")}. Pass --main <relpath>.`,
  );
}

// ---------------------------------------------------------------------------
// hashing
// ---------------------------------------------------------------------------

/** sha256 over the sorted `(relpath, bytes)` list of every file under `sourceDir`:
 * the path and the byte length are folded in before the content so no rename or
 * concatenation of two files can collide with another tree. V1 re-hashes the tree on every
 * entry: an unchanged hash lets a re-entry revise the existing transcription (`v1EntryMode`). */
export async function hashSourceTree(sourceDir: string): Promise<string> {
  const files = (await listTree(sourceDir)).sort();
  const hash = createHash("sha256");
  for (const rel of files) {
    const bytes = await readFile(path.join(sourceDir, rel));
    hash.update(`${rel}\n${bytes.byteLength}\n`);
    hash.update(bytes);
    hash.update("\n");
  }
  return hash.digest("hex");
}

// ---------------------------------------------------------------------------
// a bare `.tex` and the files beside it
// ---------------------------------------------------------------------------

/** What the directory of a bare `.tex` may hold for it to be taken as the paper's source: the
 * file may sit in a home or a projects directory, which is not a paper. (An explicit directory
 * input is the user's statement and has no limit.) Mutable so the refusal can be tested. */
export const SIBLING_DIR_LIMITS = { maxFiles: 2000, maxBytes: 256 * 1024 * 1024 };

const GRAPHICS_EXTENSIONS = ["", ".pdf", ".png", ".jpg", ".jpeg", ".eps"];

/**
 * The files a bare `.tex` names (`\input`/`\include`/`\subfile`, `\bibliography`,
 * `\includegraphics`), looked up under its own directory: `found` when one is there, and
 * `missing` the `.tex` inclusions that are not. A name built from a macro or a parameter is
 * not resolved (the parser does not expand macros).
 */
async function texSiblings(texPath: string): Promise<{ found: boolean; missing: string[] }> {
  const dir = path.dirname(texPath);
  const text = blankTexComments(await readFile(texPath, "utf8"));
  const beside = async (names: string[]): Promise<boolean> => {
    for (const name of names) {
      const abs = path.resolve(dir, name);
      const rel = path.relative(dir, abs);
      if (!rel || rel.startsWith("..") || path.isAbsolute(rel)) continue;
      if (await stat(abs).then((i) => i.isFile(), () => false)) return true;
    }
    return false;
  };
  const literal = (raw: string | undefined): string | null => {
    const name = (raw ?? "").trim().replace(/^"|"$/g, "");
    return name && !/[#\\]/.test(name) ? name : null;
  };
  let found = false;
  const missing: string[] = [];
  for (const m of text.matchAll(/\\(?:input|include|subfile)(?![a-zA-Z@])\s*(?:\{([^{}]*)\}|([^\s{}\\%,]+))/g)) {
    const name = literal(m[1] ?? m[2]);
    if (!name) continue;
    const ext = /\.[A-Za-z0-9]+$/.exec(name)?.[0].toLowerCase();
    if (await beside(ext ? [name, `${name}.tex`] : [`${name}.tex`, name])) found = true;
    else if ((!ext || ext === ".tex") && !missing.includes(name)) missing.push(name);
  }
  for (const m of text.matchAll(/\\(?:bibliography|addbibresource)(?![a-zA-Z@])\s*(?:\[[^\]]*\])?\{([^{}]*)\}/g)) {
    for (const raw of m[1]!.split(",")) {
      const name = literal(raw);
      if (name && (await beside([/\.bib$/i.test(name) ? name : `${name}.bib`]))) found = true;
    }
  }
  for (const m of text.matchAll(/\\includegraphics(?![a-zA-Z@])\s*(?:\[[^\]]*\])?\s*\{([^{}]*)\}/g)) {
    const name = literal(m[1]);
    if (name && (await beside(GRAPHICS_EXTENSIONS.map((e) => `${name}${e}`)))) found = true;
  }
  return { found, missing };
}

/** Refuse to take `dir` as the source of the bare `.tex` `input` when it is no paper's directory:
 * past `SIBLING_DIR_LIMITS` (the walk stops there), or holding the run itself. */
async function assertPaperDirectory(dir: string, input: string, sourceDir: string): Promise<void> {
  const ask = `Pass the paper's own directory (with --main ${path.basename(input)}) or an archive of it.`;
  const inside = path.relative(dir, path.resolve(sourceDir));
  if (!inside.startsWith("..") && !path.isAbsolute(inside)) {
    throw new Error(`${input} includes files beside it, but its directory ${dir} holds the run itself. ${ask}`);
  }
  const { maxFiles, maxBytes } = SIBLING_DIR_LIMITS;
  let files = 0;
  let bytes = 0;
  const walk = async (at: string): Promise<void> => {
    for (const entry of await readdir(at, { withFileTypes: true })) {
      const abs = path.join(at, entry.name);
      if (entry.isDirectory()) await walk(abs);
      else {
        files += 1;
        bytes += (await lstat(abs)).size;
      }
      if (files > maxFiles || bytes > maxBytes) {
        throw new Error(
          `${input} includes files beside it, but its directory ${dir} holds more than ${maxFiles} files ` +
            `or ${Math.round(maxBytes / (1024 * 1024))} MiB: it is not taken as the paper's source. ${ask}`,
        );
      }
    }
  };
  await walk(dir);
}

// ---------------------------------------------------------------------------
// prepareSource
// ---------------------------------------------------------------------------

/** Name to give a single `.tex` copied into an empty source dir. */
function texName(input: string): string {
  const base = path.basename(input).replace(/\.gz$/i, "");
  if (/\.tex$/i.test(base)) return base;
  return base ? `${base}.tex` : "main.tex";
}

async function copyDirectory(from: string, to: string): Promise<void> {
  // `dereference: false` keeps symlinks as symlinks so the security walk can refuse
  // them; silently following one would copy content from outside the user's tree.
  const { cp } = await import("node:fs/promises");
  await cp(from, to, { recursive: true, dereference: false, preserveTimestamps: false });
}

export const prepareSource: PrepareSource = async ({
  input,
  sourceDir,
  mainHint,
}): Promise<PreparedSource> => {
  const abs = path.resolve(input);
  if (!existsSync(abs)) throw new Error(`verify input not found: ${input}`);
  const info = await stat(abs);

  await rm(sourceDir, { recursive: true, force: true });
  await mkdir(sourceDir, { recursive: true });

  let inputKind: PreparedSource["inputKind"];
  let scratch: string | null = null;
  let main = mainHint;
  let note: string | undefined;
  try {
    if (info.isDirectory()) {
      inputKind = "dir";
      await copyDirectory(abs, sourceDir);
    } else {
      const head = await readHead(abs);
      if (isZip(head)) {
        inputKind = "zip";
        await extractZip(abs, sourceDir);
      } else if (isTar(head)) {
        inputKind = "tar";
        await extractTar(abs, sourceDir);
      } else if (isGzip(head)) {
        const plain = gunzipCapped(await readFile(abs), path.basename(abs));
        if (isTar(plain)) {
          inputKind = "tar.gz";
          scratch = await mkdtemp(path.join(os.tmpdir(), "theoremchecker-verify-"));
          const tarPath = path.join(scratch, "source.tar");
          await writeFile(tarPath, plain);
          await extractTar(tarPath, sourceDir);
        } else {
          inputKind = "gz";
          await writeFile(path.join(sourceDir, texName(abs)), plain);
        }
      } else {
        // A bare `.tex` copied alone loses every file it includes: the run would referee what is left.
        const beside = await texSiblings(abs);
        if (beside.missing.length > 0) {
          throw new Error(
            `${input} includes ${beside.missing.length} .tex file(s) that are not beside it: ${beside.missing.join(", ")}. ` +
              `Pass the paper's directory (with --main ${path.basename(abs)}) or an archive of it; a paper that ` +
              `ships without them is given the same way (the missing files are then warnings).`,
          );
        }
        if (beside.found) {
          await assertPaperDirectory(path.dirname(abs), input, sourceDir);
          inputKind = "dir";
          await copyDirectory(path.dirname(abs), sourceDir);
          main = mainHint ?? path.basename(abs);
          note = `${input} includes files beside it: its directory ${path.dirname(abs)} is the source, ${main} the main file`;
        } else {
          inputKind = "tex";
          await writeFile(path.join(sourceDir, texName(abs)), await readFile(abs));
        }
      }
    }
  } catch (err) {
    await rm(sourceDir, { recursive: true, force: true });
    throw err;
  } finally {
    if (scratch) await rm(scratch, { recursive: true, force: true });
  }

  if (inputKind === "zip" || inputKind === "tar" || inputKind === "tar.gz") {
    await flattenSingleTopLevelDir(sourceDir);
  }
  await assertNoEscapes(sourceDir);

  const mainFile = await detectMainFile(sourceDir, main);
  const sha256 = await hashSourceTree(sourceDir);
  return { sourceDir: path.resolve(sourceDir), mainFile, sha256, inputKind, ...(note ? { note } : {}) };
};
