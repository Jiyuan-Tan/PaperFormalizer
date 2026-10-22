#!/usr/bin/env node
// Copies the read-only paper viewer into the registry of shared papers:
//   node tools/scripts/sync_viewer.mjs <registry-dir>
// writes <registry-dir>/site/viewer/ afresh: the local UI's app.js and app.css (app.js draws a
// shared paper in its snapshot mode), the page template snapshot.html as page.html, DOMPurify,
// KaTeX (its stylesheet, script and web fonts) and pdf.js (its module and worker), each with its
// license file (their licenses require the notice in every copy), with VERSION naming the
// PaperFormalizer commit they come from. The registry's site build reads them; they are
// never edited there.
import { execFileSync } from "node:child_process";
import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import path from "node:path";
import { fileURLToPath } from "node:url";

const TOOLS = path.join(path.dirname(fileURLToPath(import.meta.url)), "..");
const STATIC = path.join(TOOLS, "src", "ui", "static");
const require = createRequire(path.join(TOOLS, "package.json"));

const registry = process.argv[2];
if (!registry || !existsSync(path.join(registry, "site", "build.mjs"))) {
  console.error("usage: node tools/scripts/sync_viewer.mjs <registry-dir>   (the folder holding site/build.mjs)");
  process.exit(2);
}
const out = path.join(path.resolve(registry), "site", "viewer");
const katex = path.dirname(require.resolve("katex/dist/katex.min.css"));
const pdfjs = path.dirname(require.resolve("pdfjs-dist/build/pdf.min.mjs"));
const version = (pkg) => JSON.parse(readFileSync(require.resolve(`${pkg}/package.json`), "utf8")).version;

rmSync(out, { recursive: true, force: true });
mkdirSync(path.join(out, "katex", "fonts"), { recursive: true });
mkdirSync(path.join(out, "pdfjs"), { recursive: true });
const copy = (from, to) => cpSync(from, path.join(out, to));
copy(path.join(STATIC, "app.js"), "app.js");
copy(path.join(STATIC, "app.css"), "app.css");
cpSync(path.join(STATIC, "fonts"), path.join(out, "fonts"), { recursive: true }); // the serif app.css names, with its license
copy(path.join(STATIC, "snapshot.html"), "page.html");
copy(path.join(STATIC, "vendor", "purify.min.js"), "purify.min.js");
copy(path.join(STATIC, "vendor", "purify.LICENSE"), "purify.LICENSE");
copy(path.join(path.dirname(require.resolve("katex/package.json")), "LICENSE"), "katex/LICENSE");
copy(path.join(path.dirname(require.resolve("pdfjs-dist/package.json")), "LICENSE"), "pdfjs/LICENSE");
copy(path.join(katex, "katex.min.css"), "katex/katex.min.css");
copy(path.join(katex, "katex.min.js"), "katex/katex.min.js");
// the fonts a current browser takes (the stylesheet names woff2 first, then woff and ttf)
for (const f of readdirSync(path.join(katex, "fonts"))) if (/\.woff2?$/u.test(f)) copy(path.join(katex, "fonts", f), `katex/fonts/${f}`);
copy(path.join(pdfjs, "pdf.min.mjs"), "pdfjs/pdf.min.mjs");
copy(path.join(pdfjs, "pdf.worker.min.mjs"), "pdfjs/pdf.worker.min.mjs");

const git = (...args) => { try { return execFileSync("git", args, { cwd: TOOLS, encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim(); } catch { return ""; } };
const commit = git("rev-parse", "HEAD") || "unknown";
const dirty = git("status", "--porcelain", "--", "src/ui/static") ? " (with uncommitted changes to src/ui/static)" : "";
const purify = /DOMPurify (\d+\.\d+\.\d+)/u.exec(readFileSync(path.join(STATIC, "vendor", "purify.min.js"), "utf8"))?.[1] ?? "unknown";
writeFileSync(path.join(out, "VERSION"), [
  `PaperFormalizer ${commit}${dirty}`,
  `katex ${version("katex")}`,
  `pdfjs-dist ${version("pdfjs-dist")}`,
  `dompurify ${purify}`,
  "",
  "Copied by tools/scripts/sync_viewer.mjs of PaperFormalizer: do not edit these files here.",
  "",
].join("\n"));
console.log(`viewer copied into ${out} (PaperFormalizer ${commit.slice(0, 12)}${dirty})`);
