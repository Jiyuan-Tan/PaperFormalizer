// A paper's formulas set apart from its HTML, for the page: KaTeX's markup is most of a rendered paper
// (thousands of formulas, megabytes), and the page draws a formula only as its part of the paper nears
// the window. Each outermost `<span class="katex">…</span>` becomes `<span class="kx" data-k="i"></span>`
// and its markup the i-th entry of `math` (app.js: `drawMath`). The site's build does the same in a
// browser (PaperFormalizerPapers site/sanitize.mjs); here the renderer's own output is read as text.

const OPEN = '<span class="katex">';

/** `html` with each outermost KaTeX formula replaced by a placeholder, its markup appended to `math`.
 *  A formula whose spans do not close (never KaTeX's output) is left in place. Pure but for `math`. */
export function formulasOf(html: string, math: string[]): string {
  let out = "", at = 0;
  for (let i = html.indexOf(OPEN); i >= 0; i = html.indexOf(OPEN, at)) {
    // the formula ends where its spans balance
    let depth = 0, j = i, end = -1;
    while (j < html.length) {
      const o = html.indexOf("<span", j), c = html.indexOf("</span>", j);
      if (c < 0) break;
      if (o >= 0 && o < c) { depth++; j = o + 5; continue; }
      depth--; j = c + 7;
      if (depth === 0) { end = j; break; }
    }
    if (end < 0) break;
    out += html.slice(at, i) + `<span class="kx" data-k="${math.length}"></span>`;
    math.push(html.slice(i, end));
    at = end;
  }
  return out + html.slice(at);
}

/** The paper view with the formulas of its body and its comments set apart in `math`. Pure. */
export function formulasApart<T extends { html: string; comments?: Array<{ html: string }> }>(view: T): T & { math: string[] } {
  const math: string[] = [];
  const html = formulasOf(view.html, math);
  const comments = view.comments?.map((c) => ({ ...c, html: formulasOf(c.html, math) }));
  return { ...view, html, ...(comments ? { comments } : {}), math };
}
