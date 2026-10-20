// `prepareSource` is the only thing standing between an untrusted paper bundle and the
// run directory, so every case here is either "the user's input shape is recognised" or
// "a hostile archive is refused before it can write outside `source/`".
//
// Input shapes are decided by MAGIC BYTES because arXiv's download has no extension at
// all: the same URL yields a bare gzipped `.tex` for a one-file paper and a gzipped tar
// for a multi-file one. The malicious zip is written by hand because `zip` refuses to
// produce a `../` member.

import { describe, it, expect, beforeEach } from "vitest";
import { execFileSync } from "node:child_process";
import { mkdir, mkdtemp, readFile, readdir, symlink, writeFile } from "node:fs/promises";
import { FILE_SYMLINKS } from "../platform.js";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { gzipSync } from "node:zlib";
import { GUNZIP_LIMITS, SIBLING_DIR_LIMITS, prepareSource } from "../../src/verify/source_bundle.js";

function haveTool(tool: string): boolean {
  try {
    // `which` is not universal; probe the binary itself.
    execFileSync(tool, ["--help"], { stdio: "ignore" });
    return true;
  } catch (err) {
    return (err as { code?: string }).code !== "ENOENT";
  }
}

const HAVE_UNZIP = haveTool("unzip");
if (!HAVE_UNZIP) console.warn("[source_bundle.test] `unzip` is not installed — zip case skipped");

const DOC = (body: string): string =>
  `\\documentclass{article}\n\\begin{document}\n${body}\n\\end{document}\n`;

let root: string;
let sourceDir: string;

beforeEach(async () => {
  root = await mkdtemp(path.join(os.tmpdir(), "verify-src-"));
  sourceDir = path.join(root, "run", "source");
});

/** A small multi-file paper tree, returned as its directory. */
async function paperTree(name = "paper"): Promise<string> {
  const dir = path.join(root, name);
  await mkdir(path.join(dir, "sec"), { recursive: true });
  await writeFile(path.join(dir, "main.tex"), DOC("\\input{sec/intro}"));
  await writeFile(path.join(dir, "sec", "intro.tex"), "Hello.\n");
  await writeFile(path.join(dir, "refs.bib"), "@book{a, title={A}}\n");
  return dir;
}

// --- a minimal stored-zip writer, for members `zip` will not create -------------

function crc32(buf: Buffer): number {
  let c = ~0;
  for (const byte of buf) {
    c ^= byte;
    for (let k = 0; k < 8; k += 1) c = (c >>> 1) ^ (0xedb88320 & -(c & 1));
  }
  return ~c >>> 0;
}

function storedZip(entries: Array<{ name: string; data: Buffer; externalAttrs?: number }>): Buffer {
  const locals: Buffer[] = [];
  const centrals: Buffer[] = [];
  let offset = 0;
  for (const entry of entries) {
    const name = Buffer.from(entry.name, "utf8");
    const crc = crc32(entry.data);
    const local = Buffer.alloc(30);
    local.writeUInt32LE(0x04034b50, 0);
    local.writeUInt16LE(20, 4);
    local.writeUInt16LE(0, 8); // stored
    local.writeUInt32LE(crc, 14);
    local.writeUInt32LE(entry.data.length, 18);
    local.writeUInt32LE(entry.data.length, 22);
    local.writeUInt16LE(name.length, 26);
    locals.push(local, name, entry.data);
    const central = Buffer.alloc(46);
    central.writeUInt32LE(0x02014b50, 0);
    central.writeUInt16LE(3 << 8 | 20, 4); // made by unix
    central.writeUInt16LE(20, 6);
    central.writeUInt16LE(0, 10);
    central.writeUInt32LE(crc, 16);
    central.writeUInt32LE(entry.data.length, 20);
    central.writeUInt32LE(entry.data.length, 24);
    central.writeUInt16LE(name.length, 28);
    central.writeUInt32LE((entry.externalAttrs ?? ((0o100644 << 16) >>> 0)) >>> 0, 38);
    central.writeUInt32LE(offset, 42);
    centrals.push(central, name);
    offset += 30 + name.length + entry.data.length;
  }
  const centralBuf = Buffer.concat(centrals);
  const end = Buffer.alloc(22);
  end.writeUInt32LE(0x06054b50, 0);
  end.writeUInt16LE(entries.length, 8);
  end.writeUInt16LE(entries.length, 10);
  end.writeUInt32LE(centralBuf.length, 12);
  end.writeUInt32LE(offset, 16);
  return Buffer.concat([...locals, centralBuf, end]);
}

// --- input shapes --------------------------------------------------------------

describe("prepareSource input shapes", () => {
  it.each([
    {
      shape: "a single .tex file",
      make: async () => { const p = path.join(root, "solo.tex"); await writeFile(p, DOC("Solo.")); return p; },
      kind: "tex", main: "solo.tex", present: "solo.tex", text: "Solo.",
    },
    {
      shape: "a directory tree",
      make: () => paperTree(),
      kind: "dir", main: "main.tex", present: "sec/intro.tex", text: "Hello.",
    },
    {
      shape: "a bare extensionless gzip stream holding one .tex (arXiv single-file source)",
      make: async () => { const p = path.join(root, "arxivsource"); await writeFile(p, gzipSync(Buffer.from(DOC("From arXiv.")))); return p; },
      kind: "gz", main: "arxivsource.tex", present: "arxivsource.tex", text: "From arXiv.",
    },
  ])("recognises $shape", async ({ make, kind, main, present, text }) => {
    const out = await prepareSource({ input: await make(), sourceDir });
    expect(out.inputKind).toBe(kind);
    expect(out.mainFile).toBe(main);
    expect(await readFile(path.join(out.sourceDir, present), "utf8")).toContain(text);
  });
});

// --- a bare .tex and the files beside it ---------------------------------------

describe("prepareSource on a bare .tex that includes files", () => {
  const paper = async (body: string, files: Record<string, string> = {}): Promise<string> => {
    const dir = path.join(root, "paper");
    await mkdir(path.join(dir, "sec"), { recursive: true });
    await writeFile(path.join(dir, "draft.tex"), DOC(body));
    for (const [rel, text] of Object.entries(files)) await writeFile(path.join(dir, rel), text);
    return path.join(dir, "draft.tex");
  };

  it("takes its directory as the source, the given file as the main one, and says so", async () => {
    const input = await paper("\\input{sec/intro}\n\\bibliography{refs}", { "sec/intro.tex": "Hello.", "refs.bib": "@book{a}", "other.tex": DOC("Another paper.") });
    const out = await prepareSource({ input, sourceDir });
    expect(out).toMatchObject({ inputKind: "dir", mainFile: "draft.tex" });
    expect(out.note).toMatch(/draft\.tex includes files beside it: its directory .*paper is the source, draft\.tex the main file/);
    expect(await readFile(path.join(out.sourceDir, "sec/intro.tex"), "utf8")).toBe("Hello.");
    expect(existsSync(path.join(out.sourceDir, "refs.bib"))).toBe(true);
  });

  it.each([
    { what: "a bibliography", body: "\\bibliography{refs}", file: "refs.bib" },
    { what: "a figure named without its extension", body: "\\includegraphics[width=2cm]{sec/fig}", file: "sec/fig.pdf" },
  ])("is taken with its directory for $what alone", async ({ body, file }) => {
    const out = await prepareSource({ input: await paper(body, { [file]: "x" }), sourceDir });
    expect(out.inputKind).toBe("dir");
    expect(existsSync(path.join(out.sourceDir, file))).toBe(true);
  });

  it("stays a single-file source when nothing it names is beside it", async () => {
    const out = await prepareSource({ input: await paper("% \\input{gone}\n\\bibliography{refs}\n\\newcommand{\\sec}[1]{\\input{#1}}", { "unrelated.tex": "x" }), sourceDir });
    expect(out).toMatchObject({ inputKind: "tex", mainFile: "draft.tex" });
    expect(out.note).toBeUndefined();
    expect(await readdir(out.sourceDir)).toEqual(["draft.tex"]);
  });

  it("refuses at launch, listing them, when .tex files it includes are missing", async () => {
    const lonely = paper("\\input{sec/intro}\n\\include{appendix.tex}\n\\input{fig.tikz}");
    await expect(prepareSource({ input: await lonely, sourceDir })).rejects.toThrow(/includes 2 \.tex file\(s\) that are not beside it: sec\/intro, appendix\.tex\. Pass the paper's directory \(with --main draft\.tex\) or an archive/);
    expect(existsSync(sourceDir)).toBe(false);
    // … also when some are there: the directory was inferred, not given
    const partial = paper("\\input{sec/intro}\n\\input{macros}", { "sec/intro.tex": "Hello." });
    await expect(prepareSource({ input: await partial, sourceDir })).rejects.toThrow(/not beside it: macros\./);
    // the directory itself, given by the user, keeps the parser's warning
    expect((await prepareSource({ input: path.join(root, "paper"), sourceDir, mainHint: "draft.tex" })).inputKind).toBe("dir");
  });

  it("refuses a directory that is no paper's: too many files, or one holding the run", async () => {
    const input = await paper("\\input{sec/intro}", { "sec/intro.tex": "Hello.", "a.txt": "1", "b.txt": "2" });
    const kept = { ...SIBLING_DIR_LIMITS };
    try {
      SIBLING_DIR_LIMITS.maxFiles = 3;
      await expect(prepareSource({ input, sourceDir })).rejects.toThrow(/holds more than 3 files or 256 MiB: it is not taken as the paper's source\. Pass the paper's own directory \(with --main draft\.tex\) or an archive/);
      Object.assign(SIBLING_DIR_LIMITS, kept, { maxBytes: 20 });
      await expect(prepareSource({ input, sourceDir })).rejects.toThrow(/holds more than/);
    } finally {
      Object.assign(SIBLING_DIR_LIMITS, kept);
    }
    await expect(prepareSource({ input, sourceDir: path.join(root, "paper", "runs", "x", "source") })).rejects.toThrow(/holds the run itself/);
  });
});

// --- security ------------------------------------------------------------------

describe("prepareSource refuses escaping archives", () => {
  it.skipIf(!HAVE_UNZIP)("rejects a zip member named ../evil.tex before extracting", async () => {
    const archive = path.join(root, "evil.zip");
    await writeFile(
      archive,
      storedZip([
        { name: "main.tex", data: Buffer.from(DOC("Fine.")) },
        { name: "../evil.tex", data: Buffer.from("owned") },
      ]),
    );
    await expect(prepareSource({ input: archive, sourceDir })).rejects.toThrow(
      /escapes the destination directory/,
    );
    expect(existsSync(path.join(root, "run", "evil.tex"))).toBe(false);
    expect(existsSync(sourceDir)).toBe(false);
  });

  it.skipIf(!FILE_SYMLINKS)("rejects a directory input containing a symlink", async () => {
    const dir = await paperTree();
    await symlink("/etc/passwd", path.join(dir, "leak.tex"));
    await expect(prepareSource({ input: dir, sourceDir })).rejects.toThrow(/symbolic link/);
    expect(existsSync(sourceDir)).toBe(false);
  });
});

// --- main-file detection --------------------------------------------------------

describe("prepareSource main-file detection", () => {
  async function twoCandidates(a: string, b: string, aBody = "", bBody = ""): Promise<string> {
    const dir = path.join(root, "multi");
    await mkdir(dir, { recursive: true });
    await writeFile(path.join(dir, a), DOC(aBody));
    await writeFile(path.join(dir, b), DOC(bBody));
    return dir;
  }

  it.each([
    { rule: "a preferred name (paper.tex) beats another candidate", files: ["paper.tex", "zsupplement.tex", "", ""], main: "paper.tex" },
    { rule: "else the candidate with the most \\input commands", files: ["alpha.tex", "beta.tex", "\\input{one}\n\\include{two}", "no inclusions"], main: "alpha.tex" },
    { rule: "a file another file includes is never the main, even named paper.tex", files: ["paper.tex", "wrapper.tex", "Body.", "\\input{paper}"], main: "wrapper.tex" },
  ])("$rule", async ({ files, main }) => {
    const [a, b, aBody, bBody] = files as [string, string, string, string];
    const dir = await twoCandidates(a, b, aBody, bBody);
    expect((await prepareSource({ input: dir, sourceDir })).mainFile).toBe(main);
  });

  it("a commented-out \\documentclass or \\input is none", async () => {
    const dir = path.join(root, "commented");
    await mkdir(dir, { recursive: true });
    // a section file that keeps a commented-out standalone header, and names the main file in a comment
    await writeFile(path.join(dir, "paper.tex"), "%\\documentclass{article}\n%\\begin{document}\n% \\input{wrapper}\nA section.\n%\\end{document}\n");
    await writeFile(path.join(dir, "wrapper.tex"), DOC("\\input{paper}"));
    expect((await prepareSource({ input: dir, sourceDir })).mainFile).toBe("wrapper.tex");
  });

  it("refuses to guess between equal candidates and points at --main", async () => {
    const dir = await twoCandidates("alpha.tex", "beta.tex");
    await expect(prepareSource({ input: dir, sourceDir })).rejects.toThrow(
      /ambiguous main file: alpha\.tex, beta\.tex\. Pass --main/,
    );
  });

  it.each([
    { hint: "zsupplement.tex", main: "zsupplement.tex", error: null },
    { hint: "nope.tex", main: null, error: /--main nope\.tex does not exist/ },
    { hint: "sec", main: null, error: /--main sec is a directory, not a \.tex file/ },
  ])("--main $hint: wins over every rule when valid, refused otherwise", async ({ hint, main, error }) => {
    const dir = await twoCandidates("paper.tex", "zsupplement.tex");
    await mkdir(path.join(dir, "sec"), { recursive: true });
    await writeFile(path.join(dir, "sec", "intro.tex"), "Hello.\n");
    const run = prepareSource({ input: dir, sourceDir, mainHint: hint });
    if (error) await expect(run).rejects.toThrow(error);
    else expect((await run).mainFile).toBe(main);
  });
});

// --- decompression limits --------------------------------------------------------

describe("prepareSource gzip limits", () => {
  it("refuses a gzip input that expands past the cap, with an actionable message", async () => {
    const input = path.join(root, "bomb"); // extensionless, as arXiv serves
    await writeFile(input, gzipSync(Buffer.alloc(4 * 1024 * 1024, 0x41)));
    const saved = GUNZIP_LIMITS.maxOutputBytes;
    GUNZIP_LIMITS.maxOutputBytes = 64 * 1024;
    try {
      await expect(prepareSource({ input, sourceDir })).rejects.toThrow(
        /bomb expands to more than 65536 bytes of data; refusing to unpack it/,
      );
    } finally {
      GUNZIP_LIMITS.maxOutputBytes = saved;
    }
    expect(existsSync(sourceDir)).toBe(false);
  });
});

// --- hashing --------------------------------------------------------------------

describe("prepareSource sha256", () => {
  it("is stable across runs and covers every file in the tree, not just the main one", async () => {
    const dir = await paperTree();
    const before = await prepareSource({ input: dir, sourceDir });
    const again = await prepareSource({ input: dir, sourceDir: path.join(root, "run2", "source") });
    expect(again.sha256).toBe(before.sha256);
    expect(before.sha256).toMatch(/^[0-9a-f]{64}$/);
    await writeFile(path.join(dir, "refs.bib"), "@book{a, title={B}}\n");
    const after = await prepareSource({ input: dir, sourceDir: path.join(root, "run4", "source") });
    expect(after.sha256).not.toBe(before.sha256);
    expect(await readdir(after.sourceDir)).toContain("refs.bib");
  });
});
