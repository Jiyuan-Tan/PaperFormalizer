import { describe, expect, it } from "vitest";
import { formulasApart, formulasOf } from "../../src/ui/formulas_apart.js";

const K = (inner: string) => `<span class="katex"><span class="katex-mathml">${inner}</span><span class="katex-html"><span>${inner}</span></span></span>`;
const back = (html: string, math: string[]) => html.replace(/<span class="kx" data-k="(\d+)"><\/span>/g, (_m, k: string) => math[Number(k)]);

describe("formulas set apart", () => {
  it("replaces each outermost formula by a placeholder and round-trips", () => {
    const html = `<p>a ${K("x")} b <span>c</span> ${K(`y ${K("z")}`)}</p>`;
    const math: string[] = [];
    const out = formulasOf(html, math);
    expect(math).toHaveLength(2);
    expect(out).toBe(`<p>a <span class="kx" data-k="0"></span> b <span>c</span> <span class="kx" data-k="1"></span></p>`);
    expect(back(out, math)).toBe(html);
  });

  it("leaves a formula whose spans never close in place", () => {
    const html = `<p>${K("x")} <span class="katex"><span>open</p>`;
    const math: string[] = [];
    const out = formulasOf(html, math);
    expect(math).toHaveLength(1);
    expect(back(out, math)).toBe(html);
  });

  it("numbers the comments' formulas after the body's, in one table", () => {
    const v = formulasApart({ html: `<p>${K("a")}</p>`, comments: [{ html: K("b"), id: "c1" }] });
    expect(v.math).toHaveLength(2);
    expect(v.comments![0]).toEqual({ html: `<span class="kx" data-k="1"></span>`, id: "c1" });
    expect(back(v.html, v.math)).toBe(`<p>${K("a")}</p>`);
  });
});
