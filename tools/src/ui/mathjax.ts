// The page's second math renderer: MathJax (SVG, self-contained), for the formulas KaTeX refuses.
// It reads far more of LaTeX than KaTeX but is slower and its output larger, so it only sees the
// rest. A formula neither can read throws — the caller records it for the orchestrating agent.
import { mathjax } from "mathjax-full/js/mathjax.js";
import { TeX } from "mathjax-full/js/input/tex.js";
import { SVG } from "mathjax-full/js/output/svg.js";
import { liteAdaptor } from "mathjax-full/js/adaptors/liteAdaptor.js";
import { RegisterHTMLHandler } from "mathjax-full/js/handlers/html.js";
import { AllPackages } from "mathjax-full/js/input/tex/AllPackages.js";

const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
// Without noundefined/noerrors an unknown command or a parse error is thrown, not drawn in red.
// A paper's TeX is untrusted (an arXiv source): no package that writes links, styles, classes or
// ids into the page (html: \href \style \class \cssId; bbox: any CSS; action: interactive toggles).
const LEFT_OUT = new Set(["noundefined", "noerrors", "html", "bbox", "action"]);
const PACKAGES = (AllPackages as string[]).filter((p) => !LEFT_OUT.has(p));

/** A renderer for one paper's macros (KaTeX form: `\name` → body with `#n`). Throws when it cannot read a formula. */
export function mathjaxRenderer(macros: Record<string, string>): (tex: string, display: boolean) => string {
  const defs: Record<string, [string, number]> = {};
  for (const [k, body] of Object.entries(macros)) {
    if (!/^\\[A-Za-z]+$/.test(k)) continue;
    const n = Math.max(0, ...[...body.matchAll(/#(\d)/g)].map((m) => Number(m[1])));
    defs[k.slice(1)] = [body, n];
  }
  const tex = new TeX({ packages: PACKAGES, macros: defs, formatError: (_jax: unknown, err: Error) => { throw err; } });
  const doc = mathjax.document("", { InputJax: tex, OutputJax: new SVG({ fontCache: "none" }) });
  return (s, display) => adaptor.outerHTML(doc.convert(s, { display, em: 16, ex: 8, containerWidth: 1280 }));
}
