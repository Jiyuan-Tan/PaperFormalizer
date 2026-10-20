// A browser cannot draw TikZ: the paper's pictures are typeset apart, once, under the paper's own
// preamble (the `preview` package crops each to a page of one PDF), and the page draws them from it.
// The compile runs beside the request that first asks for it; that request, and any before it ends,
// name the pictures as left out.
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";

export const TIKZ_DIR = path.join("logs", "ui_tikz");
const TIMEOUT_MS = 180_000;
const running = new Set<string>();

/** The PDF holding `pictures` (bodies of `tikzpicture` environments) one to a page, by name under
 *  `<runDir>/logs/ui_tikz/`, or null while it is being typeset, when that failed, or with no pdflatex.
 *  `base`: the paper's directory, read from only; `mainText`: its main file (for the preamble). */
/** Why the paper's pictures are not drawn, when their compile failed: the reason and the log's first error
 *  line; null when nothing failed (no pictures, drawn, or still being typeset). */
export function tikzFailure(runDir: string, base: string, mainText: string, pictures: string[], setup = ""): string | null {
  const name = tikzName(mainText, pictures, setup);
  if (!name) return null;
  const dir = path.join(runDir, TIKZ_DIR);
  let why: string;
  try { why = readFileSync(path.join(dir, `${name}.failed`), "utf8").trim(); } catch { return null; }
  let first = "";
  try { first = readFileSync(path.join(dir, `${name}.log`), "latin1").split("\n").find((l) => l.startsWith("! ")) ?? ""; } catch { /* no log */ }
  return first ? `${why}: ${first}` : why;
}

const tikzDoc = (mainText: string, pictures: string[], setup: string): string | null => {
  const head = mainText.indexOf("\\begin{document}");
  if (head < 0 || !pictures.length) return null;
  return `${mainText.slice(0, head)}\n\\usepackage[active,tightpage]{preview}\\PreviewEnvironment{tikzpicture}\\setlength\\PreviewBorder{2pt}\n\\begin{document}\n${setup ? `\\makeatletter\n${setup}\n\\makeatother\n` : ""}${pictures.map((b) => `\\begin{tikzpicture}${b}\\end{tikzpicture}`).join("\n\n")}\n\\end{document}\n`;
};
const tikzName = (mainText: string, pictures: string[], setup: string): string | null => {
  const tex = tikzDoc(mainText, pictures, setup);
  return tex ? createHash("sha1").update(tex).digest("hex").slice(0, 16) : null;
};

export function tikzPdf(runDir: string, base: string, mainText: string, pictures: string[], setup = ""): string | null {
  const tex = tikzDoc(mainText, pictures, setup);
  if (!tex) return null;
  const name = tikzName(mainText, pictures, setup)!;
  const dir = path.join(runDir, TIKZ_DIR);
  const pdf = path.join(dir, `${name}.pdf`), failed = path.join(dir, `${name}.failed`);
  if (existsSync(pdf)) return `${name}.pdf`;
  if (existsSync(failed) || running.has(pdf)) return null;
  running.add(pdf);
  try {
    mkdirSync(dir, { recursive: true });
    writeFileSync(path.join(dir, `${name}.tex`), tex);
    const child = spawn("pdflatex", ["-interaction=nonstopmode", "-halt-on-error", `-output-directory=${dir}`, `-jobname=${name}`, path.join(dir, `${name}.tex`)], { cwd: base, stdio: "ignore" });
    const timer = setTimeout(() => child.kill("SIGKILL"), TIMEOUT_MS);
    const done = (why: string) => { clearTimeout(timer); running.delete(pdf); if (!existsSync(pdf)) { try { writeFileSync(failed, `${why}; the log is ${name}.log\n`); } catch { /* best effort */ } } };
    child.on("error", (e) => done(`pdflatex did not start (${e.message})`));
    child.on("exit", (code) => done(`pdflatex exited ${code}`));
  } catch { running.delete(pdf); }
  return null;
}
