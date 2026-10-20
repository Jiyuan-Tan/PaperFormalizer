// The page's script (static/app.js: one file, no framework, no build step), tested three ways without
// a browser: its pure choices sliced out of the source and run as written; its selectors and the
// stylesheet's checked against what the page and the server emit; and the whole script run against a
// stub DOM on the payloads a real server gives for a run — every part must draw, from the records as
// the pipeline writes them.
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import katex from "katex";
import { describe, expect, it, vi } from "vitest";
import { startUiServer } from "../../src/ui/server.js";
import { readingText, repairKey } from "../../src/ui/run_model.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";
import type { V15NodeVerdict } from "../../src/verify/types.js";

const UI = path.join(__dirname, "..", "..", "src", "ui");
const js = readFileSync(path.join(UI, "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
const css = readFileSync(path.join(UI, "static", "app.css"), "utf8");
const index = readFileSync(path.join(UI, "static", "index.html"), "utf8");

/** A top-level declaration of app.js by name: a function (to its closing brace at column 0) or a one-line const. */
function decl(name: string): string {
  const f = js.indexOf(`\nfunction ${name}(`);
  if (f >= 0) return js.slice(f, js.indexOf("\n}\n", f) + 2);
  const c = js.indexOf(`\nconst ${name} = `);
  if (c < 0) throw new Error(`app.js has no ${name}`);
  return js.slice(c, js.indexOf("\n", c + 1));
}
const load = <T>(names: string[], ret: string): T => new Function(`${names.map(decl).join("\n")}\nreturn ${ret};`)() as T;

describe("page: the choices it makes, as written", () => {
  it("the fallback renderer names clever references and leaves plain references numeric", () => {
    const texText = new Function("P", `${["esc", "subsup", "refNumber", "texText"].map(decl).join("\n")}\nreturn texText;`)({ paper: { labels: { a: "3.7", b: "3.8" }, envs: [{ label: "a", heading: "Theorem 3.7" }, { label: "b", heading: "Corollary 3.8" }] } }) as (t: string) => string;
    expect(texText(String.raw`\cref{a}; \Cref{b}; \autoref{a}; Theorem~\ref{a}`)).toBe("Theorem 3.7; Corollary 3.8; Theorem 3.7; Theorem&nbsp;3.7");
  });
  it("a citation invoked inside a proof is a button on a line of its own", () => {
    const resBadge = new Function(`const esc = (s) => String(s); const envOf = () => null; const proseHeading = (r) => r.id; const badge = () => "";\n${decl("resBadge")}\nreturn resBadge;`)() as (r: Record<string, unknown>) => string;
    expect(resBadge({ id: "lem:a" })).toBe('<button type="button" class="res-badge" data-res="lem:a">lem:a </button>');
    expect(resBadge({ id: "lem:c", citedIn: "lem:a" })).toBe('<button type="button" class="res-badge cited-site" data-res="lem:c">lem:c </button>');
    // with a Lean proposition on file for it, the label opens the drawer that shows it
    expect(resBadge({ id: "lem:c", citedIn: "lem:a", citedLean: "CitedClt" })).toContain('data-res="lem:c"');
  });

  it("a Unicode statement's indices are set as sub- and superscripts; a name with underscores is left", () => {
    const subsup = load<(s: string) => string>(["esc", "subsup"], "subsup");
    expect(subsup("𝔼[V_t] = 0 and lim_{T→∞} (1/T)·∑_{i=1}^{T} x")).toBe("𝔼[V<sub>t</sub>] = 0 and lim<sub>T→∞</sub> (1/T)·∑<sub>i=1</sub><sup>T</sup> x");
    expect(subsup("α_m^{2(1/r − 1/p)} < ∞, S_T^{1+2q}/T, V_{t,i}, x^2")).toBe("α<sub>m</sub><sup>2(1/r − 1/p)</sup> &lt; ∞, S<sub>T</sub><sup>1+2q</sup>/T, V<sub>t,i</sub>, x<sup>2</sup>");
    expect(subsup("uses fixedCount_prob_pair and a_{b_{c}}")).toBe("uses fixedCount_prob_pair and a<sub>b<sub>c</sub></sub>");
    // an index of any alphabet; an exponent in parentheses keeps them (`n^(k)` is not `nᵏ`)
    expect(subsup("d_α(i,j)^r, 𝔼_σ, σ²_a, a_i^2, V_jᵀ, Z_j², n^(−1/2), (∫ |f|^q dP)^(1/(2q))")).toBe("d<sub>α</sub>(i,j)<sup>r</sup>, 𝔼<sub>σ</sub>, σ²<sub>a</sub>, a<sub>i</sub><sup>2</sup>, V<sub>j</sub>ᵀ, Z<sub>j</sub>², n<sup>(−1/2)</sup>, (∫ |f|<sup>q</sup> dP)<sup>(1/(2q))</sup>");
    // what is no index: a name that ends in one character, a longer index with no braces, an operator set apart, a link's address
    for (const kept of ["Var_sampleMean_n and h_indep", "ρ_αβ, F_min(y), x_i_j", "a ^ b and _x", "see https://a.org/page_8.htm?q=x_1"]) expect(subsup(kept)).toBe(kept);
    expect(subsup(`<img src=x onerror="a">_{<b>}`)).toBe("&lt;img src=x onerror=&quot;a&quot;&gt;<sub>&lt;b&gt;</sub>");
  });

  it("a text that may write its mathematics either way: TeX between dollars is typeset, the rest keeps its Unicode indices, code stays code", () => {
    const mixed = new Function("window", `${["esc", "subsup", "KATEX_GAPS", "typeset", "mixed"].map(decl).join("\n")}\nreturn mixed;`)({ katex }) as (s: unknown, macros?: Record<string, string>) => string;
    const out = mixed("If ∑_{i=1}^{T} x_i ≤ $\\R^{d}$ then `h_n : x_i < 1` holds for \\(a_b\\) <i>", { "\\R": "\\mathbb{R}" });
    expect(out.startsWith('If ∑<sub>i=1</sub><sup>T</sup> x<sub>i</sub> ≤ <span class="katex">')).toBe(true);
    expect(out).toContain('</span> then <code>h_n : x_i &lt; 1</code> holds for <span class="katex">');
    expect(out.endsWith("</span> &lt;i&gt;")).toBe(true);
    expect(out).toContain("mathbb");
    // a text with no formula is its escaped self; one dollar alone opens none; nothing is no text
    expect(mixed("costs $5 & <b>")).toBe("costs $5 &amp; &lt;b&gt;");
    expect(mixed(undefined)).toBe("");
    // a formula cannot bring markup of its own
    expect(mixed("$\\href{javascript:x}{y}$ $\\text{<script>}$")).not.toMatch(/<script|href="javascript/);
  });

  it("TeX the page sets itself: an index outside a formula is Unicode mathematics; a label is a name", () => {
    const texText = new Function("P", `${["esc", "subsup", "refNumber", "texText"].map(decl).join("\n")}\nreturn texText;`)({ paper: { labels: { "eq:a_b": "3" } } }) as (t: string) => string;
    expect(texText("with ℓ_h ≤ C and x_{i,j} in \\emph{V_t}, by~\\eqref{eq:a_b} and \\ref{lem:c_d}")).toBe('with ℓ<sub>h</sub> ≤ C and x<sub>i,j</sub> in <em>V<sub>t</sub></em>, by&nbsp;(3) and <span class="cite">lem:c_d</span>');
  });

  it("a link within the page is one to an id — never the route", () => {
    const inPageId = load<(href?: string | null) => string | null>(["inPageId"], "inPageId");
    expect(inPageId("#lbl-thm-a")).toBe("lbl-thm-a");
    expect(["#/", "#/paper/p1", "#/library", "#", "https://example.org/#x", "", null, undefined].map(inPageId)).toEqual(Array(8).fill(null));
  });

  it("a note sits at its environment when its mark is in it or just below its end; else at its own paragraph", () => {
    const sitsAtEnv = load<(inside: boolean, below: number) => boolean>(["NOTE_REACH", "sitsAtEnv"], "sitsAtEnv");
    expect(sitsAtEnv(true, -400)).toBe(true); // the mark closes the statement's text
    expect(sitsAtEnv(false, 0)).toBe(true); // right under it
    expect(sitsAtEnv(false, 2599)).toBe(true); // after its proof and its other notes
    expect(sitsAtEnv(false, 2600)).toBe(false); // further on: running text
    expect(sitsAtEnv(false, -300)).toBe(false); // before it
  });

  it("the open card sits at its place and the others give way, in order; with no room above all start from the top", () => {
    const cardTops = load<(cards: Array<{ want: number | null; h: number }>, k: number, gap: number) => number[]>(["cardTops"], "cardTops");
    const c = (want: number | null, h = 40) => ({ want, h });
    expect(cardTops([c(0), c(10), c(500)], -1, 10)).toEqual([0, 50, 500]);
    expect(cardTops([c(290), c(300), c(310)], 1, 10)).toEqual([250, 300, 350]);
    expect(cardTops([c(0), c(5)], 1, 10)).toEqual([0, 50]);
    // a card the paper gives no place comes after the others
    expect(cardTops([c(0, 10), c(null, 10)], -1, 10)).toEqual([0, 20]);
    expect(cardTops([], -1, 10)).toEqual([]);
  });

  // The finding this guards: a phrase was searched in the one corrected block only, so every phrase
  // the repair left alone — most of a repaired statement — was never found.
  it("a phrase is looked for in the corrected text first, then in the whole statement — after the last hit, else anywhere", () => {
    type Scope = { str: string; from: number };
    const xlAt = load<(scopes: Scope[], want: string) => [Scope, number] | null>(["xlAt"], "xlAt");
    const scopes = () => [{ str: "theratehalves", from: 0 }, { str: "Supposexholds.Thentheratehalves.Thenyholds", from: 0 }];
    const s = scopes();
    // the corrected block has it: found there, and the block's place moves on
    expect(xlAt(s, "therate")).toEqual([s[0], 0]);
    expect(s[0]!.from).toBe(7);
    // a phrase of the unchanged part: not in the corrected block, found in the whole statement
    expect(xlAt(s, "Supposexholds.")).toEqual([s[1], 0]);
    // the same words twice: the one after the last hit; with none after it, the first
    expect(xlAt(s, "Then")![1]).toBe(14);
    expect(xlAt(s, "Then")![1]).toBe(32);
    expect(xlAt(s, "Then")![1]).toBe(14);
    expect(xlAt(scopes(), "absent")).toBeNull();
    // a phrase of one character stands in too many places to be found
    expect(xlAt(scopes(), "x")).toBeNull();
  });

  it("the run's detail is the page's part with the drawers' once it has come: what the page's part says of a result stands", () => {
    type Part = Record<string, unknown>;
    const withDrawers = load<(page: Part, w: Part | null) => { results: Part[]; leanDefs: Part; places: Part; texHtml: Part }>(["withDrawers"], "withDrawers");
    const page = { summary: { slug: "p" }, texHtml: { a: "A" }, results: [{ id: "t1", state: "ok", review: { correctness: "ok" } }, { id: "t2", state: "error", review: null }, { id: "t3", state: "ok", review: null }] };
    // before it has come: every result as the page draws it, no declaration, no place
    expect(withDrawers(page, null)).toEqual({ ...page, leanDefs: {}, places: {} });
    const w = { leanDefs: { d: 1 }, places: { n: 2 }, texHtml: { a: "old", b: "B" }, results: { t1: { state: "stale", rows: [1], review: { correctness: "error", detail: "why" } }, t2: { rows: null, review: { detail: "gone" } } } };
    expect(withDrawers(page, w)).toEqual({
      summary: { slug: "p" }, leanDefs: { d: 1 }, places: { n: 2 }, texHtml: { a: "A", b: "B" },
      results: [{ id: "t1", state: "ok", rows: [1], review: { correctness: "ok", detail: "why" } }, { id: "t2", state: "error", rows: null, review: null }, { id: "t3", state: "ok", review: null }],
    });
  });

  it("an error's statement with no corrected text says where its repair is — and nothing when it shows one", () => {
    const note = load<(r: { repair: string | null }, live: boolean, corrected: boolean) => { text: string; unrepaired: boolean } | null>(["proofOnlyNote"], "proofOnlyNote");
    expect(note({ repair: "proof" }, false, false)).toMatchObject({ unrepaired: false, text: expect.stringContaining("The repair is in its proof") });
    expect(note({ repair: "none" }, false, false)).toMatchObject({ unrepaired: true, text: expect.stringContaining("no repair of it is on file") });
    expect(note({ repair: "none" }, true, false)).toMatchObject({ unrepaired: true, text: expect.stringContaining("Its repair is being written") });
    expect([note({ repair: "none" }, false, true), note({ repair: "proof" }, true, true), note({ repair: "statement" }, false, false), note({ repair: null }, false, false)]).toEqual([null, null, null, null]);
  });

  it("a ruling entered on a proposed repair is none on the next proposal for the same result", () => {
    const { repairChoice, sentKey } = load<{ repairChoice: (entered: Record<string, unknown>, r: { node: string; proposed: string }) => { kind?: string; text?: string }; sentKey: (rs: Array<{ node: string; proposed: string }>) => string }>(["repairChoice", "sentKey"], "{ repairChoice, sentKey }");
    const first = { node: "thm:a", proposed: "the rate is $n^{-1/2}$" }, second = { ...first, proposed: "the rate is $n^{-1/3}$" };
    const entered = { "thm:a": { kind: "redo", text: "keep the rate", of: first.proposed } };
    expect(repairChoice(entered, first)).toEqual(entered["thm:a"]);
    expect(repairChoice(entered, second)).toEqual({});
    expect(repairChoice({}, first)).toEqual({});
    // … and the rulings sent wait on those proposals: a new one is a new wait
    expect(sentKey([first])).not.toBe(sentKey([second]));
    expect(sentKey([first])).toBe(sentKey([{ ...first }]));
  });

  it("rulings sent are taken up once the run works on them; a run seen at rest with the same repairs did not take them", () => {
    const { sentState, sentKey } = load<{ sentState: (sent: { key: string; seen: number }, repairs: Array<{ node: string; proposed: string }>, live: boolean) => string; sentKey: (rs: unknown[]) => string }>(["sentKey", "sentState"], "{ sentState, sentKey }");
    const waiting = [{ node: "thm:a", proposed: "p" }], key = sentKey(waiting);
    expect(sentState({ key, seen: 1 }, [], true)).toBe("taken"); // at work: no repair is the owner's to rule on
    expect(sentState({ key, seen: 9 }, [{ node: "thm:a", proposed: "another" }], false)).toBe("taken"); // halted again, with a new proposal
    expect([1, 2].map((seen) => sentState({ key, seen }, waiting, false))).toEqual(["waiting", "waiting"]); // the start is on its way
    expect(sentState({ key, seen: 3 }, waiting, false)).toBe("dropped");
  });

  it("the page is live only while its connection is known to stand; a lost one outranks a page that is merely outdated", () => {
    const { connState } = load<{ connState: (c: { open: boolean | null; failed: boolean; outdated: boolean }) => string }>(["connState"], "{ connState }");
    expect(connState({ open: null, failed: false, outdated: false })).toBe("live"); // connecting: the views were just fetched
    expect(connState({ open: true, failed: false, outdated: false })).toBe("live");
    expect(connState({ open: false, failed: false, outdated: false })).toBe("lost"); // the event stream dropped
    expect(connState({ open: true, failed: true, outdated: false })).toBe("lost"); // a fetch did not get through
    expect(connState({ open: true, failed: false, outdated: true })).toBe("outdated");
    expect(connState({ open: false, failed: false, outdated: true })).toBe("lost");
  });

  it("a view's answers apply in the order they were asked: a late answer to an earlier request does not put the older state back; a 304 is the view held", async () => {
    type Res = { status: number; ok: boolean; statusText: string; headers: { get: () => string }; json: () => Promise<unknown> };
    const waiting: Array<{ sent: string | undefined; answer: (status: number, data?: unknown, etag?: string) => void }> = [];
    const fetch = (_url: string, init: { headers: Record<string, string> }) => new Promise<Res>((resolve) => waiting.push({
      sent: init.headers["If-None-Match"],
      answer: (status, data, etag = "") => resolve({ status, ok: status === 200, statusText: "", headers: { get: () => etag }, json: async () => data }),
    }));
    const at = js.indexOf("\nasync function api(");
    const api = new Function("fetch", `const SNAP = null;\n${decl("etags")}\n${decl("asked")}\n${js.slice(at, js.indexOf("\n}\n", at) + 2)}\nreturn api;`)(fetch) as (url: string) => Promise<{ data: unknown; changed: boolean }>;
    const first = api("/v"), second = api("/v");
    waiting[1]!.answer(200, { status: "halted" }, "t2");
    expect(await second).toEqual({ data: { status: "halted" }, changed: true });
    waiting[0]!.answer(200, { status: "running" }, "t1"); // asked first, answered last: stale
    expect(await first).toEqual({ data: { status: "halted" }, changed: false });
    // the next request names the newer view; "not modified" answers with it
    const third = api("/v");
    expect(waiting[2]!.sent).toBe("t2");
    waiting[2]!.answer(304);
    expect(await third).toEqual({ data: { status: "halted" }, changed: false });
    // an error the server answered with is told apart from one where it did not answer
    const bad = api("/gone");
    waiting[3]!.answer(404, { error: "no run" });
    await expect(bad).rejects.toMatchObject({ message: "no run", answered: true });
  });

  it("a label's number from the paper is text, not markup", () => {
    const texText = new Function("P", "esc", `${decl("subsup")}${js.slice(js.indexOf("/** The number the paper prints for a label"), js.indexOf("\n}\n", js.indexOf("function texText(t)")) + 2)}; return texText;`)(
      { paper: { labels: { "eq:1": "<img src=x onerror=alert(1)>" } } }, (x: string) => String(x).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;"),
    ) as (t: string) => string;
    expect(texText("see \\eqref{eq:1}")).toBe("see (&lt;img src=x onerror=alert(1)&gt;)");
  });
});

describe("page: a paper's macros cannot run the renderer away", () => {
  it("a self-referencing \\newcommand stops at the expansion budget and the page still renders", async () => {
    const { renderPaper } = await import("../../src/ui/tex_html.js");
    const tex = String.raw`\documentclass{article}\newcommand{\foo}{\foo\foo\foo\foo}\begin{document}Before \foo after.\end{document}`;
    const t0 = Date.now();
    const html = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" }).html;
    expect(Date.now() - t0).toBeLessThan(5_000);
    expect(html).toContain("Before");
    expect(html).toContain("after.");
  });
});

describe("page: every class it looks for, and every class styled, is one something emits", () => {
  // what emits: the page's own templates and class changes, index.html, the server's renderers
  const selectorCall = /(?:\$\$?|querySelector(?:All)?|closest|matches\??\.?)\(\s*[`"]([^`"]+)[`"]/g;
  const selectors = [...js.matchAll(selectorCall)].map((m) => m[1]!.replace(/\$\{[^}]*\}/g, "X"));
  const emitters = [js.replace(selectorCall, " "), index, ...["tex_html.ts", "algorithms.ts", "mathjax.ts"].map((f) => readFileSync(path.join(UI, f), "utf8"))].join("\n");
  // classes built from a value (`k-${kind}`, `b-${status}`, `l${level}`, a Lean declaration's kind …)
  // and the math renderers' own
  const built = /^(k-|st-|m-|b-|ds-row-|ds-chip-|rv-|l\d$|katex|mjx|(def|abbrev|structure|class|instance|theorem)$)/;
  const emitted = (c: string): boolean => built.test(c) || new RegExp(`(?<![\\w-])${c}(?![\\w-])`).test(emitters);

  it("app.js queries no class that nothing emits", () => {
    const queried = new Set(selectors.flatMap((s) => [...s.matchAll(/\.([A-Za-z][\w-]*)/g)].map((m) => m[1]!)));
    expect(queried.size).toBeGreaterThan(40);
    expect([...queried].filter((c) => !emitted(c))).toEqual([]);
  });

  it("app.js queries no data attribute that nothing sets", () => {
    const attrs = new Set(selectors.flatMap((s) => [...s.matchAll(/\[(data-[a-z-]+)/g)].map((m) => m[1]!)));
    const camel = (a: string) => a.slice(5).replace(/-([a-z])/g, (_, c: string) => c.toUpperCase());
    expect([...attrs].filter((a) => !new RegExp(`${a}(?![a-z-])`).test(emitters) && !emitters.includes(`dataset.${camel(a)} =`))).toEqual([]);
  });

  it("app.css styles no class that nothing emits", () => {
    const rules = css.replace(/\/\*[\s\S]*?\*\//g, "").replace(/url\([^)]*\)/g, "").replace(/\{[^{}]*\}/g, "{}");
    const styled = new Set([...rules.matchAll(/\.([A-Za-z][\w-]*)/g)].map((m) => m[1]!));
    expect(styled.size).toBeGreaterThan(200);
    expect([...styled].filter((c) => !emitted(c))).toEqual([]);
  });
});

// ── the whole script on a stub DOM ───────────────────────────────────────────

interface Stub { name: string; html: string; text: string; cls: Set<string> }
/**
 * Run app.js with a DOM that holds no tree: an element is its selector, with the HTML written to it.
 * `document.getElementById` knows the ids of index.html and of the HTML written so far; lists
 * (`querySelectorAll`) are empty unless a test fills one (`lists`, by selector), so what walks the
 * tree (the margin layout, the badges) does no work — what is tested is that every part draws from
 * its payload. An element replaced (`outerHTML`) is a write to `<its name> outerHTML`. `payloads` is what the server
 * answers per URL; a changed one is seen at the next `showPaper`.
 */
function runPage(slug: string, payloads: Record<string, unknown>, more: Record<string, unknown> = {}, snapshot: { src: string; Element: unknown } | null = null): { page: Record<string, (...a: unknown[]) => unknown>; writes: Array<[string, string]>; posts: Array<[string, unknown]>; at: (sel: string) => Stub & Record<string, unknown>; location: { hash: string; reloads: number }; lists: Map<string, unknown[]>; sources: Array<{ closed: boolean; readyState: number; onerror: (() => void) | null; say: (event: string, data: unknown) => void }> } {
  const lists = new Map<string, unknown[]>();
  const stubs = new Map<string, Stub & Record<string, unknown>>();
  const writes: Array<[string, string]> = [];
  // what the page POSTs (each answered as a started action is)
  const posts: Array<[string, unknown]> = [];
  const mk = (name: string): Stub & Record<string, unknown> => {
    const hit = stubs.get(name);
    if (hit) return hit;
    const cls = new Set<string>();
    const st: Stub & Record<string, unknown> = {
      name, html: "", text: "", cls, dataset: {}, style: {}, hidden: false, value: "", listeners: new Map(), offsetHeight: 40, scrollHeight: 0, clientHeight: 0, scrollTop: 0, firstChild: null,
      classList: { add: (...c: string[]) => c.forEach((x) => cls.add(x)), remove: (...c: string[]) => c.forEach((x) => cls.delete(x)), toggle: (c: string, on?: boolean) => ((on ?? !cls.has(c)) ? cls.add(c) : cls.delete(c)), contains: (c: string) => cls.has(c) },
      get innerHTML() { return st.html; }, set innerHTML(v: string) { st.html = String(v); writes.push([name, st.html]); },
      get textContent() { return st.text; }, set textContent(v: string) { st.text = String(v); },
      set outerHTML(v: string) { writes.push([`${name} outerHTML`, String(v)]); },
      insertAdjacentHTML: (_where: string, h: string) => { st.html += h; writes.push([name, String(h)]); },
      // the statement of a result shows no corrected text here: its note is drawn
      querySelector: (s: string) => (s === ".rv.ins" ? null : mk(`${name} ${s}`)), querySelectorAll: (s: string) => lists.get(`${name} ${s}`) ?? [], closest: () => null, contains: () => false, matches: () => true,
      addEventListener: (event: string, f: unknown) => { (st.listeners as Map<string, unknown>).set(event, f); }, setAttribute: () => {}, removeAttribute: () => {}, getAttribute: () => null, focus: () => {}, scrollIntoView: () => {}, append: () => {}, prepend: () => {}, remove: () => {}, replaceWith: () => {},
      getBoundingClientRect: () => ({ top: 0, bottom: 0, left: 0, right: 0, width: 600, height: 20 }),
    };
    stubs.set(name, st);
    return st;
  };
  const known = (id: string) => index.includes(`id="${id}"`) || [...stubs.values()].some((s) => s.html.includes(`id="${id}"`));
  const document = {
    body: mk("body"), activeElement: null, scrollingElement: mk("html"), documentElement: mk("html"),
    querySelector: (s: string) => { const id = /^#([\w-]+)$/.exec(s)?.[1]; return id && !known(id) ? null : mk(s); },
    querySelectorAll: (s: string) => lists.get(s) ?? [], getElementById: (id: string) => (known(id) ? mk(`#${id}`) : null),
    createElement: (t: string) => mk(`<${t}> ${stubs.size}`), addEventListener: () => {}, contains: () => false,
    // (the page of a shared paper: app.js loaded with `data-snapshot`)
    currentScript: snapshot ? { dataset: { snapshot: snapshot.src }, src: "https://site.example/r/viewer/app.js" } : null,
  };
  // the event stream: each one the page opens, with what it listens for (a test speaks as the server)
  const sources: Array<{ closed: boolean; readyState: number; onerror: (() => void) | null; say: (event: string, data: unknown) => void }> = [];
  class EventSource {
    closed = false; readyState = 1; onerror: (() => void) | null = null;
    private on = new Map<string, (e: { data: string }) => void>();
    constructor() { sources.push(this); }
    addEventListener(event: string, f: (e: { data: string }) => void) { this.on.set(event, f); }
    close() { this.closed = true; this.readyState = 2; }
    say(event: string, data: unknown) { this.on.get(event)?.({ data: JSON.stringify(data) }); }
  }
  // (`more`: what a test adds to the window — the browser's notifications, its storage)
  const window = { katex, EventSource, addEventListener: () => {}, scrollTo: () => {}, scrollBy: () => {}, scrollY: 0, matchMedia: () => ({ matches: true }), focus: () => {}, ...more };
  const fetch = async (url: string, init?: { method?: string; body?: string; headers?: Record<string, string> }) => {
    // (a POST is answered as a started action is, unless `payloads["POST <url>"]` says otherwise)
    if (init?.method === "POST") { posts.push([url, JSON.parse(init.body ?? "{}")]); const reply = payloads[`POST ${url}`] ?? { command: "leansmith verify …", log: "ui.log" }; return { status: 200, ok: true, statusText: "", headers: { get: () => "" }, json: async () => reply }; }
    const data = payloads[url], etag = JSON.stringify(data).length + ":" + JSON.stringify(data).slice(-40);
    if (init?.headers?.["If-None-Match"] === etag) return { status: 304, ok: false, headers: { get: () => etag }, json: async () => ({}) };
    return { status: data === undefined ? 404 : 200, ok: data !== undefined, statusText: "", headers: { get: () => etag }, json: async () => data ?? { error: `no ${url}` } };
  };
  const exposed = "SNAP, snapLoad, P, S, C, LS, drawLib, drawPaperBody, connect, route, refreshInbox, showPaper, openDrawer, closeDrawer, drawCards, drawStatus, drawMap, selectNode, jumpTo, activate, repairClick, acceptRepairRecs, promoClick, reportHTML";
  expect(js).toContain("/* ── boot ");
  const body = js.replace(/\/\* ── boot [\s\S]*$/, `return { ${exposed} };\n})();`).replace(/^\(\(\) => \{$/m, "return (() => {");
  const names = ["EventSource", "window", "document", "location", "fetch", "navigator", "CSS", "performance", "requestAnimationFrame", "setInterval", "setTimeout", "clearTimeout", "NodeFilter", "Element"];
  const location = { hash: `#/paper/${slug}`, reloads: 0, reload: () => { location.reloads++; } };
  const page = new Function(...names, body)(
    EventSource, window, document, location, fetch, {}, { escape: (s: string) => s }, { now: () => 0 }, (f: () => void) => f(), () => 0, () => 0, () => {}, { SHOW_TEXT: 4 }, snapshot?.Element ?? class {},
  ) as Record<string, (...a: unknown[]) => unknown>;
  // (`title`: the tab's title as the page set it)
  return { page: Object.assign(page, { title: () => (document as { title?: string }).title }), writes, posts, at: (sel) => mk(sel), location, lists, sources };
}

describe("page: a shared paper's report, typeset", () => {
  it("headings, paragraphs, lists (an item's lines joined), bold, code and formulas; a \\label is dropped; the text is escaped", () => {
    const { page } = runPage("p", {});
    const md = "# Correctness report — p\n\n**Verdict: ERRORS FOUND**\n\n## What was wrong\n\n### Theorem 3 — repaired\n\n- **As printed.** \\label{thm:a} For all $a$,\n  \\[ a \\ge 0 . \\]\n- **Lean.** `Papers.T3` <b>x</b>\n\nA closing line.";
    const html = page.reportHTML!(md) as string;
    expect(html).toContain('<h3 class="rh">Correctness report — p</h3><p><strong>Verdict: ERRORS FOUND</strong></p><h4 class="rh">What was wrong</h4><h5 class="rh">Theorem 3 — repaired</h5><ul><li><strong>As printed.</strong> For all ');
    expect(html).toContain('<li><strong>Lean.</strong> <code>Papers.T3</code> &lt;b&gt;x&lt;/b&gt;</li></ul><p>A closing line.</p>');
    expect(html).not.toContain("label");
    expect(html.match(/class="katex/g)?.length).toBeGreaterThanOrEqual(2);
  });
});

describe("page: paper search", () => {
  it.each(["input", "search"])("clearing with %s restores every paper and returning to the page retains the visible query", async (event) => {
    const runs = Array.from({ length: 10 }, (_, i) => ({ slug: `p${i}`, title: `Paper ${i}`, authors: "", status: "done", stageIndex: 10 }));
    const p = runPage("p", { "/api/toolkit": { toolkit: { name: "tk", repo: "/r", root: "/r", owner: "O", lean: "lean4:v4", base: [] }, runs } });
    p.location.hash = "#/";
    await p.page.route!();
    const input = p.at("#runs-q");
    const search = (value: string, type: string) => {
      input.value = value;
      (input.listeners as Map<string, (e: unknown) => void>).get(type)!({ target: input });
    };
    search("Paper 9", "input");
    expect(p.at("#runs-body").html).toContain('data-slug="p9"');
    expect(p.at("#runs-body").html).not.toContain('data-slug="p0"');
    // Navigation rebuilds the input; its visible value must agree with the retained filter.
    input.value = "";
    (p.page.S as unknown as { view: string }).view = "paper";
    await p.page.route!();
    expect(input.value).toBe("Paper 9");
    search("", event);
    expect(p.at("#runs-body").html).toContain('data-slug="p0"');
    expect(p.at("#runs-pager").html).toContain("1–8 of 10");
    expect(p.location.reloads).toBe(0);
  });
});

describe("page: what waits for the owner is counted in the tab's title and, when asked for, notified once", () => {
  const paper = (over: Record<string, unknown>) => ({ slug: "p1", title: "A Paper", status: "running", headline: "V1 · working", pending: { weakening: 0, promotion: null }, requests: [], unread: 0, ...over });
  const shown: Array<{ title: string; body: string; onclick?: () => void }> = [];
  class Notification {
    static permission = "granted";
    static requestPermission = async () => "granted";
    onclick?: () => void;
    constructor(public title: string, o: { body: string }) { shown.push(Object.assign(this, { body: o.body })); }
    body = ""; close() {}
  }
  const store = (on: boolean) => ({ getItem: () => (on ? "1" : "0"), setItem: () => {} });
  it("the title counts the papers; nothing standing at the page's load is notified; each new thing once, and its click opens the paper", async () => {
    const payloads: Record<string, unknown> = { "/api/toolkit": { runs: [paper({ slug: "p0", status: "needs-you", requests: [{ id: "q1" }] }), paper({})] } };
    const { page, location } = runPage("p1", payloads, { Notification, isSecureContext: true, localStorage: store(true) });
    const title = () => page.title!();
    await page.refreshInbox!();
    expect(title()).toBe("(1) LeanSmith");
    expect(shown).toEqual([]);
    // the same picture again: nothing new
    payloads["/api/toolkit"] = { runs: [paper({ slug: "p0", status: "needs-you", requests: [{ id: "q1" }] }), paper({ headline: "V1.5 · working" })] };
    await page.refreshInbox!();
    expect(shown).toEqual([]);
    // a repair to decide on p1, and a second request on p0: one notification each
    payloads["/api/toolkit"] = { runs: [paper({ slug: "p0", title: "Other", status: "needs-you", requests: [{ id: "q1" }, { id: "q2" }] }), paper({ status: "needs-you", pending: { weakening: 1, promotion: null } })] };
    await page.refreshInbox!();
    expect(title()).toBe("(2) LeanSmith");
    expect(shown.map((n) => [n.title, n.body])).toEqual([["Other", "The agent asks you something."], ["A Paper", "A repair that would weaken a result waits for your decision."]]);
    await page.refreshInbox!();
    expect(shown).toHaveLength(2);
    // the agent writes; a promotion round waits
    payloads["/api/toolkit"] = { runs: [paper({ status: "needs-you", pending: { weakening: 0, promotion: "A" }, unread: 1 })] };
    await page.refreshInbox!();
    expect(title()).toBe("(1) LeanSmith");
    expect(shown.slice(2).map((n) => [n.title, n.body])).toEqual([["A Paper", "Results proposed for your toolkit wait for your decision."], ["LeanSmith", "The agent replied on A Paper"]]);
    // an answer of the agent's alone is announced as a message, and counted nowhere: not in the title, not in the inbox
    payloads["/api/toolkit"] = { runs: [paper({ unread: 2 })] };
    await page.refreshInbox!();
    expect(title()).toBe("LeanSmith");
    expect(shown.at(-1)).toMatchObject({ title: "LeanSmith", body: "The agent replied on A Paper" });
    expect(shown).toHaveLength(5);
    location.hash = "#/";
    shown[2]!.onclick!();
    expect(location.hash).toBe("#/paper/p1");
    // nothing waits: the bare title
    payloads["/api/toolkit"] = { runs: [paper({})] };
    await page.refreshInbox!();
    expect(title()).toBe("LeanSmith");
  });
  it("turned off, or with no notifications in the browser: the title's count alone", async () => {
    shown.length = 0;
    for (const more of [{ Notification, isSecureContext: true, localStorage: store(false) }, {}]) {
      const payloads: Record<string, unknown> = { "/api/toolkit": { runs: [paper({})] } };
      const { page } = runPage("p1", payloads, more);
      await page.refreshInbox!();
      payloads["/api/toolkit"] = { runs: [paper({ status: "needs-you", requests: [{ id: "q1" }] })] };
      await page.refreshInbox!();
      expect(page.title!()).toBe("(1) LeanSmith");
    }
    expect(shown).toEqual([]);
  });
  it("on unless turned off: nothing kept in the browser, or no storage at all, still notifies; the permission is asked for as the page opens", async () => {
    for (const localStorage of [{ getItem: () => null, setItem: () => {} }, { getItem: () => { throw new Error("blocked"); } }]) {
      shown.length = 0;
      let asked = 0;
      class Undecided extends Notification {
        static permission = "default";
        static requestPermission = async () => { asked += 1; Undecided.permission = "granted"; return "granted"; };
      }
      const payloads: Record<string, unknown> = { "/api/toolkit": { runs: [paper({})] } };
      const { page } = runPage("p1", payloads, { Notification: Undecided, isSecureContext: true, localStorage });
      await page.refreshInbox!();
      expect(asked).toBe(1);
      payloads["/api/toolkit"] = { runs: [paper({ unread: 1 })] };
      await page.refreshInbox!();
      expect(shown).toHaveLength(1);
    }
  });
});

describe("page: the list's Share column", () => {
  const base = { stageIndex: 10, live: false, headline: "done", updatedAt: 0, tokens: null, unread: 0, authors: "" };
  const run = (slug: string, status: string, share: Record<string, unknown> | null) => ({ ...base, slug, title: `Paper ${slug}`, status, share });
  it("a finished paper offers Share, a share shows where it stands, an unfinished one shows nothing", async () => {
    const runs = [
      run("u1", "running", null),
      run("d1", "done", null),
      run("p1", "done", { status: "published", url: "https://site.example/papers/p1/", started_at: "2026-10-12T00:00:00Z" }),
      run("r1", "done", { status: "review", pr_url: "https://github.com/o/r/pull/3", started_at: "2026-10-12" }),
      run("x1", "done", { status: "refused", problems: ["a <bad> file"], started_at: "2026-10-12" }),
      run("e1", "done", { status: "expired", started_at: "2026-10-12" }),
      run("w1", "done", { status: "awaiting_sign_in", claim_url: "https://svc.example/claim/w1", check_code: "AB2C", started_at: "2026-10-12" }),
      run("c1", "done", { status: "submitted", started_at: "2026-10-12" }),
    ];
    const tk = { toolkit: { name: "tk", repo: "/r", root: "/r", owner: "O", lean: "leanprover/lean4:v4", base: [] }, runs };
    const p = runPage("p", { "/api/toolkit": tk });
    p.location.hash = "#/";
    (p.page.S as unknown as { view: string }).view = "toolkit";
    await p.page.route!();
    const html = p.at("#runs-body").html;
    const cell = (slug: string) => { const i = html.indexOf(`data-slug="${slug}"`); const row = html.slice(i, html.indexOf("</tr>", i)); return row.slice(row.indexOf('<td class="sh">')); };
    expect(cell("u1")).toBe('<td class="sh"></td>');
    expect(cell("d1")).toBe(`<td class="sh"><button class="sh-act" type="button" data-share="d1">Share</button></td>`);
    expect(cell("p1")).toContain(`<a href="https://site.example/papers/p1/" target="_blank" rel="noopener">published ↗</a>`);
    expect(cell("r1")).toContain(`<a href="https://github.com/o/r/pull/3" target="_blank" rel="noopener">in review ↗</a>`);
    expect(cell("x1")).toContain(`title="a &lt;bad&gt; file">refused</span><button class="sh-act" type="button" data-share="x1">Share again</button>`);
    expect(cell("e1")).toContain(`expired</span><button class="sh-act" type="button" data-share="e1">Share again</button>`);
    expect(cell("w1")).toContain(`<a href="https://svc.example/claim/w1" target="_blank" rel="noopener">sign in ↗</a>`);
    expect(cell("c1")).toContain("checking…");
    expect(html.match(/<td class="sh">/g)?.length).toBe(8);
  });
  it("a bundle that cannot be shared shows why, and no button", async () => {
    const runs = [
      { ...run("n1", "done", null), shareable: { ok: false, reason: "3 blocking items in corrected_paper/TODO.md" } },
      { ...run("n2", "done", { status: "refused", problems: [], started_at: "2026-10-12" }), shareable: { ok: false, reason: "its bundle has no seal" } },
      { ...run("k1", "done", null), shareable: { ok: true } },
    ];
    const p = runPage("p", { "/api/toolkit": { toolkit: { name: "tk", repo: "/r", root: "/r", owner: "O", lean: "leanprover/lean4:v4", base: [] }, runs } });
    p.location.hash = "#/";
    (p.page.S as unknown as { view: string }).view = "toolkit";
    await p.page.route!();
    const html = p.at("#runs-body").html;
    const cell = (slug: string) => { const i = html.indexOf(`data-slug="${slug}"`); const row = html.slice(i, html.indexOf("</tr>", i)); return row.slice(row.indexOf('<td class="sh">')); };
    expect(cell("n1")).toBe(`<td class="sh"><span class="pill b-neutral" title="3 blocking items in corrected_paper/TODO.md">not ready</span></td>`);
    expect(cell("n2")).toContain(`refused</span><span class="pill b-neutral" title="its bundle has no seal">not ready</span>`);
    expect(cell("n2")).not.toContain("data-share");
    expect(cell("k1")).toContain(`data-share="k1"`);
  });
  it("asks after a share in progress until it is final, gives up on a check past half an hour, and says when the service is down", async () => {
    vi.useFakeTimers();
    try {
      const answers: Array<Record<string, unknown>> = [];
      let draws = 0;
      const api = async () => ({ data: answers.shift() ?? { status: "submitted" } });
      const make = new Function("api", "S", "shareRedraw", `${decl("SHARE_FINAL")}\nconst SHARE_POLL = new Map();\n${decl("SHARE_PATIENCE")}\nconst SHARE_SINCE = new Map(), SHARE_STALE = new Set(), SHARE_DOWN = new Map();\n${decl("sharePoll")}\nreturn { sharePoll, SHARE_POLL, SHARE_STALE, SHARE_DOWN };`);
      const m = make(api, { view: "toolkit" }, () => { draws++; }) as { sharePoll: (s: string) => void; SHARE_POLL: Map<string, unknown>; SHARE_STALE: Set<string>; SHARE_DOWN: Map<string, string> };
      answers.push({ status: "submitted", unreachable: "the share service at https://svc could not be reached (down)" });
      m.sharePoll("a");
      await vi.advanceTimersByTimeAsync(4000);
      expect(m.SHARE_DOWN.get("a")).toContain("could not be reached");
      await vi.advanceTimersByTimeAsync(4000);
      expect(m.SHARE_DOWN.has("a")).toBe(false);
      await vi.advanceTimersByTimeAsync(31 * 60 * 1000);
      expect(m.SHARE_STALE.has("a")).toBe(true);
      expect(m.SHARE_POLL.size).toBe(0);
      const n = draws;
      await vi.advanceTimersByTimeAsync(60_000);
      expect(draws).toBe(n);
      // a final share: asked no more
      answers.push({ status: "published" });
      m.sharePoll("b");
      await vi.advanceTimersByTimeAsync(4000);
      expect(m.SHARE_POLL.size).toBe(0);
    } finally {
      vi.useRealTimers();
    }
  });
  it("its button opens the share dialog of that row's paper, whatever paper was open before", async () => {
    const asked: string[] = [], titles: string[] = [];
    const shareRun = new Function("api", "confirmRun", "S", `const esc = (s) => String(s); const $ = () => ({}); const window = {};\n${decl("shareRedraw")}\n${js.slice(js.indexOf("\nasync function shareRun("), js.indexOf("\n}\n", js.indexOf("\nasync function shareRun(")) + 2)}\nreturn shareRun;`)(
      async (url: string) => { asked.push(url); return { data: { title: "T", slug: "d1", files: 3, size: "1 kB", url: "u", parts: [], signIn: "", warning: "" } }; },
      async (title: string) => { titles.push(title); return false; },
      { view: "toolkit", slug: "other" },
    ) as (slug?: string) => Promise<void>;
    await shareRun("d1");
    expect([asked, titles]).toEqual([["/api/runs/d1/share"], ["Share this paper publicly"]]);
  });
});

describe("page: a shared paper's page, drawn read-only from its bundle's snapshot", () => {
  it("cuts a finished run's views from page.json, sanitizes what it inserts, draws the paper and its files, and posts nothing", async () => {
    const snap = {
      schema: 1, slug: "p9", title: "A Paper", authors: "A. Author", verdict: "repaired", buckets: { repaired: 1 }, tokens: null, main: "main.tex", leanDir: "lean/Papers/P9",
      results: [{
        id: "thm:a", kind: "theorem", label: "thm:a", key: true, state: "error", bucket: "repaired", repair: "statement", proved: true, deps: [], lean: { file: "A.lean", decl: "P9.a", line: 3 },
        review: { correctness: "error", faithfulness: "ok", ambiguity: "ok", detail: "It fails." }, paperError: { detail: "It fails.", witness: null }, axioms: ["propext"], conditions: [], rows: null, segments: [], uncovered: [],
      }],
      leanDefs: {}, places: {}, texHtml: { "It fails.": "It fails." },
      // the bundle's HTML names the page's own ids and names, and carries its copy button: the stricter pass drops them
      paper: { title: "A Paper", authors: "A. Author", html: '<p id="d-body" name="SNAP">Body</p><button data-copy="evil">x</button><span id="lbl-thm-a">a</span>', toc: [{ html: '<a id="modal-ok">1 Intro</a>' }], comments: [{ html: '<b data-copy="x">n</b>', label: '<i id="pv">L</i>' }], envs: [], anchors: {}, readings: {}, marks: 0, pages: {}, labels: {}, ownerReadings: {}, anchorHeadings: {}, pdf: "corrected_paper/main.pdf", macros: {} },
    };
    // the sanitizer the page loads (DOMPurify), as a stand-in that drops scripts, runs the page's
    // attribute hook on each attribute, and says what it saw
    const seen: string[] = [];
    const hooks: Array<(n: unknown, d: { attrName: string; attrValue: string; keepAttr: boolean }) => void> = [];
    const DOMPurify = {
      addHook: (_on: string, f: (typeof hooks)[number]) => { hooks.push(f); },
      sanitize: (h: string) => {
        seen.push(h);
        return h.replace(/<script>[^<]*<\/script>/g, "").replace(/\s([\w-]+)="([^"]*)"/g, (_m, attrName: string, attrValue: string) => {
          const d = { attrName, attrValue, keepAttr: true };
          for (const f of hooks) f(null, d);
          return d.keepAttr ? ` ${attrName}="${d.attrValue}"` : "";
        });
      },
    };
    class Element { h = ""; get innerHTML() { return this.h; } set innerHTML(v: string) { this.h = v; } get outerHTML() { return this.h; } set outerHTML(v: string) { this.h = v; } insertAdjacentHTML(_w: string, v: string) { this.h += v; } }
    const { page, posts, at, sources } = runPage("p9", { "page/page.json": snap, "share.json": { shared_by: "alice", shared_at: "2026-10-12T00:00:00Z" } }, { DOMPurify }, { src: "page/page.json", Element });
    // every HTML string written into the page passes the sanitizer first
    const el = new Element();
    el.innerHTML = "<b>x</b><script>alert(1)</script>";
    el.insertAdjacentHTML("beforeend", "<script>alert(2)</script>y");
    el.outerHTML = "<i>z</i><script>alert(3)</script>";
    expect([el.innerHTML, seen]).toEqual(["<i>z</i>", ["<b>x</b><script>alert(1)</script>", "<script>alert(2)</script>y", "<i>z</i><script>alert(3)</script>"]]);
    type Views = { page: { summary: Record<string, unknown>; results: Array<Record<string, unknown>> }; drawers: { results: Record<string, Record<string, unknown>> } };
    const SNAP = page.SNAP as unknown as { views: Promise<Views>; slug: string; viewer: string; leanDir: string };
    expect(SNAP.viewer).toBe("https://site.example/r/viewer/");
    SNAP.views = (page.snapLoad as () => Promise<Views>)();
    const v = await SNAP.views;
    SNAP.slug = v.page.summary.slug as string;
    // the views a server gives a finished run: nothing live, nothing waiting, the drawers apart
    expect(v.page.summary).toMatchObject({ slug: "p9", status: "done", live: false, orch: null, requests: [], reviews: [] });
    expect(v.page.results[0]!.review).toEqual({ correctness: "error" });
    expect(v.page.results[0]).not.toHaveProperty("paperError");
    expect(v.drawers.results["thm:a"]).toMatchObject({ paperError: { detail: "It fails." }, axioms: ["propext"] });
    await page.route!();
    expect(at("#paper-body").html).toBe('<p>Body</p><button>x</button><span id="lbl-thm-a">a</span>');
    const paper = (v as unknown as { paper: { toc: Array<{ html: string }>; comments: Array<{ html: string; label: string }> } }).paper;
    expect([paper.toc[0]!.html, paper.comments[0]!.html, paper.comments[0]!.label]).toEqual(["<a>1 Intro</a>", "<b>n</b>", "<i>L</i>"]);
    // the status: the verdict, who shared it, the bundle's files — no Share, no conversation, no run to follow
    const status = at("#status").html;
    for (const s of ["repaired", '<a href="https://github.com/alice" target="_blank" rel="noopener">@alice</a> on 2026-10-12', '<button class="btn" type="button" data-report>Full report</button>', 'href="corrected_paper/main.pdf"', 'href="lean/"']) expect(status).toContain(s);
    // the report opens typeset in the drawer, not as a raw file; the result-by-Lean list is not offered
    expect(status).not.toContain("MATCH.md");
    expect(status).not.toContain('href="REPORT.md"');
    expect(status).not.toMatch(/share-run|data-msg|Message the agent|orch/);
    // the drawer links the result's Lean file in the bundle
    page.openDrawer!("thm:a");
    expect(at("#d-body").html).toContain('<a href="lean/Papers/P9/A.lean" target="_blank" rel="noopener"><code>A.lean:3</code></a>');
    expect([posts, sources.length]).toEqual([[], 0]);
  });
});

describe("page: the whole script draws a run from what the server sends", () => {
  it("says when its picture is no longer the server's: a lost connection, a page updated on disk; a server started anew reloads it", () => {
    const { page, at, location, sources } = runPage("p", {});
    const conn = at("#conn"), body = at("body");
    (page.connect as () => void)();
    const es = sources[0]!;
    es.say("hello", { boot: "b1", assets: "a1" });
    expect([conn.text, body.cls.has("stale")]).toEqual(["● live", false]);
    // the stream drops: the last state received is shown as that, not as the run's
    es.onerror!();
    expect(conn.text).toContain("connection lost");
    expect(body.cls.has("stale")).toBe(true);
    // the browser reconnects to the same server: live again
    es.say("hello", { boot: "b1", assets: "a1" });
    expect([conn.text, body.cls.has("stale")]).toEqual(["● live", false]);
    // a ping that names other page files: this tab runs an older page, and offers the new one
    es.say("ping", { assets: "a1" });
    expect(conn.text).toBe("● live");
    es.say("ping", { assets: "a2" });
    expect(conn.text).toContain("click to reload");
    expect(location.reloads).toBe(0);
    (conn.onclick as () => void)();
    expect(location.reloads).toBe(1);
    // a server started anew: the page loads its code
    es.say("hello", { boot: "b2", assets: "a2" });
    expect(location.reloads).toBe(2);
    // opening the stream again closes the one before
    (page.connect as () => void)();
    expect([es.closed, sources.length]).toEqual([true, 2]);
  });
  const root = mkdtempSync(path.join(tmpdir(), "tc-ui-page-"));
  const run = path.join(root, "runs", "p1");
  const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
  const TEX = [
    String.raw`\documentclass{article}\newtheorem{theorem}{Theorem}\newtheorem{lemma}{Lemma}`,
    String.raw`\begin{document}`,
    String.raw`\section{Results}`,
    String.raw`\begin{theorem}\label{thm:a}`,
    String.raw`The rate is $n^{-1}$.\vsOriginal{The rate is $n^{-1}$.}\vsProposed{The rate is $n^{-1/2}$.}\vsNote{The bound fails at $n = 1$; see Lemma~\ref{lem:b}.}\vsReadingOwner{Convergence is in probability.}`,
    String.raw`\end{theorem}`,
    String.raw`\vsProposedCorollary{thm:cor-fix-0a1b2c3d}{Theorem~\ref{thm:a}}{If the errors are Gaussian the rate is $n^{-1}$.\vsLine\textit{Proof.} Immediate.}`,
    String.raw`\begin{lemma}\label{lem:b}`,
    String.raw`A lemma whose proof is repaired.`,
    String.raw`\end{lemma}`,
    String.raw`\textbf{Proposition 3.} Every bounded sequence has a convergent subsequence.`,
    "",
    String.raw`Some running text.\vsNote{A note on running text.}`,
    String.raw`\end{document}`,
  ].join("\n");
  // the referee's verdict as the pipeline types it: a pinned reading comes with its evidence
  const verdict: Pick<V15NodeVerdict, "id" | "faithfulness" | "ambiguity" | "correctness" | "detail" | "reading"> = {
    id: "thm:a", faithfulness: "ok", ambiguity: "pinned", correctness: "error", detail: "It fails: (a) at $n = 1$; (b) at $n = 2$.",
    reading: { reading: "The rate is in $L^2$.", evidence: "the proof bounds a second moment", of: null },
  };
  const item = { node: "thm:a", printed: "The rate is $n^{-1}$.", proposed: "The rate is $n^{-1/2}$.", given_up: "the faster rate", detail: "the bound fails", witness: "take $n = 1$", corollaries: [{ title: "the Gaussian case", statement: "If the errors are Gaussian the rate is $n^{-1}$." }] };
  mkdirSync(path.join(run, "source"), { recursive: true });
  mkdirSync(path.join(run, "discovery"), { recursive: true });
  writeFileSync(path.join(run, "source", "main.tex"), TEX);
  writeFileSync(path.join(run, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: {
    phase: "review", source: { input: "/papers/main.tex", main_file: "main.tex" },
    paper_errors: { "thm:a": { detail: "the bound fails", witness: "take $n = 1$" }, "lem:b": { detail: "a step of the proof fails", witness: null } },
    weakening_repair: { status: "pending", items: [item], at: "x" },
  } }));
  writeFileSync(path.join(run, "discovery", "core.json"), JSON.stringify({
    statements: [
      { id: "thm:a", kind: "theorem", depends_on: ["lem:b"], tex_locator: { file: "main.tex", from: 4, label: "thm:a" } },
      { id: "thm:cor-fix-0a1b2c3d", kind: "theorem", depends_on: ["thm:a"], split_from: "thm:a", proof_tex: "By Theorem~\\ref{thm:a}." },
      { id: "lem:b", kind: "lemma", depends_on: [], tex_locator: { file: "main.tex", from: 8, label: "lem:b" } },
      { id: "prop:p3", kind: "proposition", depends_on: ["lem:b"], tex_locator: { file: "main.tex", from: 11 } },
    ],
    assumptions: [{ id: "ass:pin-owner-1", condition: "Convergence is in probability.", used_by: ["thm:a"] }],
  }));
  writeFileSync(path.join(run, "discovery", "v1_5_review.json"), JSON.stringify({ nodes: [verdict] }));
  writeFileSync(path.join(run, "discovery", "patches.json"), JSON.stringify({
    patches: [{ node: "lem:b", ops: [{ op: "replace", unit: "lem:b/proof/1/1", text: "x" }] }], unfixable: [], key_results: ["thm:a"],
    owner_readings: [{ id: "ass:pin-owner-1", node: "thm:a", reading: "Convergence is in probability.", withdraws: [] }],
  }));
  writeFileSync(path.join(run, "repair_recommendations.json"), JSON.stringify({ "thm:a": { kind: "redo", why: "the printed rate is false", guidance: "state the rate for n > 1", of: repairKey(item) } }));
  writeFileSync(path.join(run, "orch_decisions.json"), JSON.stringify([{ id: "d1", node: "lem:b", at: "2026-10-01T00:00:00Z", text: "kept the lemma for $n \\ge 1$" }]));
  writeFileSync(path.join(run, "orch_requests.json"), JSON.stringify([{ id: "q1", at: "x", text: "which <account>?" }]));
  writeFileSync(path.join(run, "orch_messages.json"), JSON.stringify([
    { id: "m1", from: "user", text: "the <script>alert(1)</script> one, $\\href{javascript:x}{y}$\nline two", at: "2026-10-01T00:00:00Z", re: "q1", handled: true },
    { id: "m2", from: "agent", text: "Taken: $n \\ge 1$ <script>alert(2)</script>", at: "2026-10-01T00:01:00Z", re: "m1" },
    { id: "m3", from: "user", text: "Here is the book.", at: "2026-10-01T00:02:00Z", files: [{ name: "book.pdf", bytes: 2048, sha256: "0".repeat(64), path: "uploads/m3/book.pdf" }] },
  ]));

  it("a pinned reading is its text, however the review holds it", () => {
    expect(readingText(verdict.reading)).toBe("The rate is in $L^2$.");
    expect([readingText("as a bare string"), readingText(null), readingText(undefined), readingText({})]).toEqual(["as a bare string", null, null, null]);
  });

  it("status, margin cards, proof map and every result's drawer — and again as the run moves", async () => {
    const ui = await startUiServer(cfg, { port: 0 });
    type Detail = { summary: { live: boolean; status: string }; results: Array<Record<string, unknown> & { id: string; repair: string | null; review: Record<string, unknown> | null }>; repairs: Array<{ node: string; proposed: string }>; texHtml: Record<string, string> };
    type Drawers = { results: Record<string, { review: Record<string, unknown> | null }>; leanDefs: object; places: object; texHtml: Record<string, string> };
    let detail: Detail, drawers: Drawers, paper: { html: string; comments: Array<{ id: string; key: string; kind: string }>; ownerReadings: Record<string, unknown[]> }, toolkit: unknown;
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = async (p: string) => (await fetch(`${base}${p}`, { headers: { Cookie } })).json();
      detail = (await get("/api/runs/p1")) as Detail; drawers = (await get("/api/runs/p1/drawers")) as Drawers; paper = (await get("/api/runs/p1/paper")) as typeof paper; toolkit = await get("/api/toolkit");
    } finally {
      await ui.close();
    }
    // what the server sent: the repair waits on the owner; the reading is text; the corollary has its block
    expect(detail.summary).toMatchObject({ status: "needs-you", live: false });
    expect(detail.results.map((r) => [r.id, r.repair])).toEqual([["thm:a", "none"], ["thm:cor-fix-0a1b2c3d", null], ["lem:b", "proof"], ["prop:p3", null]]);
    // the page's detail holds nothing only a drawer shows — of a review, the grade a badge shows; the drawers' part has the rest
    expect(detail.results[0]!.review).toEqual({ correctness: "error" });
    expect(Object.keys(detail.results[0]!).filter((k) => ["rows", "leanView", "segments", "conditions", "paperError"].includes(k))).toEqual([]);
    expect(detail).not.toHaveProperty("leanDefs");
    expect(detail.texHtml["the faster rate"]).toBeDefined();
    expect(detail.texHtml["The rate is in $L^2$."]).toBeUndefined();
    expect(drawers.results["thm:a"]!.review!.reading).toBe("The rate is in $L^2$.");
    expect(drawers.texHtml["The rate is in $L^2$."]).toContain("katex");
    expect(paper.html).toContain(`<div class="rv ins cor pending formal k-corollary" tabindex="0" data-res="thm:cor-fix-0a1b2c3d"`);
    const ownCard = Object.keys(paper.ownerReadings)[0]!;
    expect(paper.comments.find((c) => c.id === ownCard)).toMatchObject({ kind: "reading-owner" });

    const payloads: Record<string, unknown> = { "/api/toolkit": toolkit, "/api/runs/p1": detail, "/api/runs/p1/drawers": drawers, "/api/runs/p1/paper": paper };
    const { page, writes, posts, at, location } = runPage("p1", payloads);
    await page.route!();
    // the run's state stands before the paper's text is in
    expect(writes.findIndex(([w]) => w === "#status")).toBeLessThan(writes.findIndex(([w]) => w === "#paper-body"));
    const last = (sel: string) => writes.filter(([w]) => w === sel).at(-1)?.[1] ?? "";
    const count = (sel: string) => writes.filter(([w]) => w === sel).length;
    expect(writes.map(([, h]) => h).join("\n")).not.toContain("Could not load this view");
    expect(last("#paper-body")).toBe(paper.html);

    // the status box: the pointer to the decision, the agent's question (escaped), its ruling to review
    const status = at("#status").html;
    expect(status).toContain("A repair would make a result of the paper weaker.");
    expect(status).toContain(`data-goto="thm:a">Theorem 1</button> (the agent recommends: redo with guidance)`);
    expect(status).toContain("<b>The agent asks you:</b> which &lt;account&gt;?");
    // … with what was said on it under it — the owner's words as text, a formula of theirs typeset; the agent's typeset —
    // and Reply beside Dismiss; the rest of the conversation under the status, with a way to write
    expect(status).not.toContain("answer in its session");
    expect(status).toMatch(/<div class="msg-b">the &lt;script&gt;alert\(1\)&lt;\/script&gt; one, <span class="katex">.*?<\/span><br>line two<\/div>/);
    expect(status).toMatch(/<div class="msg agent unseen">.*<span class="msg-new">new<\/span>.*Taken: <span class="katex">/);
    expect(status).not.toMatch(/<script|href="javascript/);
    expect(status).toContain(`data-msg="open" data-re="q1">Reply</button><button class="btn" type="button" data-dismiss="q1"`);
    expect(status).not.toContain("Mark as read");
    // shown, the agent's message is read — marked so on the server with no click, and "new" while the page stays open
    expect(posts.filter(([u]) => u === "/api/runs/p1/message-seen")).toHaveLength(1);
    expect(status).toContain(`Ask the agent <span class="msg-new">1 new</span><span class="thread-tools"><button class="linkbtn" type="button" data-msg="clear"`);
    // the block can be folded away; shown, it offers that
    expect(status).toContain(`data-msg="hide"`);
    // the thread ends with the box to write on in, with no button to find first
    expect(status.slice(status.indexOf(`<section class="thread">`))).toMatch(/<div class="thread-list">.*<\/div><div class="compose" data-compose><textarea data-msg-text/s);
    expect(status.indexOf("Taken:")).toBeLessThan(status.indexOf(`<section class="thread">`));
    expect(status.slice(status.indexOf(`<section class="thread">`))).toMatch(/Here is the book\..*<li>book\.pdf · 2 kB<\/li>/);
    expect(status).toContain("not delivered — waiting for the agent: nobody sees it until an agent session is attached");
    expect(at("#status .status .actions").html).toContain(`data-msg="open">Message the agent</button>`);
    // the box: what a message is, and that it changes nothing
    (page.P as unknown as { msg: unknown }).msg = { re: null, text: "<b>hi", files: [{ name: "a<b>.pdf", size: 3 }], error: "", sending: false };
    page.drawStatus!();
    expect(at("#status").html).toContain(`>&lt;b&gt;hi</textarea>`);
    expect(at("#status").html).toContain("a&lt;b&gt;.pdf · 3 B");
    expect(at("#status").html).toContain("nobody sees this until one is");
    expect(at("#status").html).toContain("it changes nothing by itself.");
    // a reply being written to a request the agent cleared meanwhile: its words are kept, under the thread
    (page.P as unknown as { msg: unknown }).msg = { re: "q7", text: "half a reply", files: [], error: "", sending: false };
    page.drawStatus!();
    expect(at("#status").html.slice(at("#status").html.lastIndexOf(`<section class="thread">`))).toContain(`aria-label="Your reply" placeholder="Your reply (or drop a file here)">half a reply</textarea>`);
    // replying on the request above: the box is there, and the thread offers to bring it back
    (page.P as unknown as { msg: unknown }).msg = { re: "q1", text: "on the request", files: [], error: "", sending: false };
    page.drawStatus!();
    const replying = at("#status").html.slice(at("#status").html.lastIndexOf(`<div class="ask-banner">`));
    expect(replying.slice(0, replying.indexOf(`<section class="thread">`))).toContain(`>on the request</textarea>`);
    expect(replying.slice(replying.indexOf(`<section class="thread">`))).toContain(`data-msg="open">Write to the agent here</button>`);
    (page.P as unknown as { msg: unknown }).msg = { re: null, text: "", files: [], error: "", sending: false };
    // the thread scrolls in its own height: the newest entry in view on open and when one arrives, else where it was left
    const list = at("#status .thread-list");
    list.scrollHeight = 900;
    (page.P as unknown as { threadN: number }).threadN = -1;
    page.drawStatus!();
    expect(list.scrollTop).toBe(900);
    list.scrollTop = 120;
    page.drawStatus!();
    expect(list.scrollTop).toBe(120);
    const longer = { ...detail, messages: [...(detail as unknown as { messages: unknown[] }).messages, ...Array.from({ length: 9 }, (_, k) => ({ id: `m${k + 10}`, from: "agent", at: "2026-10-01T00:03:00Z", text: `entry ${k}` }))] };
    payloads["/api/runs/p1"] = longer;
    await page.showPaper!("p1", false);
    expect(list.scrollTop).toBe(900);
    const thread = at("#status").html.slice(at("#status").html.lastIndexOf(`<section class="thread">`));
    for (let k = 0; k < 9; k++) expect(thread).toContain(`entry ${k}`);
    expect(thread).not.toContain("earlier");
    // the conversation cleared (a refusal is shown with "Clear anyway"): the thread is its box alone
    (page.P as unknown as { clearAsk: string | null }).clearAsk = "The agent has not acted yet on 1 message(s) of yours";
    page.drawStatus!();
    expect(at("#status").html).toContain(`The agent has not acted yet on 1 message(s) of yours <button class="linkbtn" type="button" data-msg="clear-anyway">Clear anyway</button>`);
    (page.P as unknown as { clearAsk: string | null }).clearAsk = null;
    payloads["/api/runs/p1"] = { ...detail, messages: [] };
    await page.showPaper!("p1", false);
    const empty = at("#status").html.slice(at("#status").html.lastIndexOf(`<section class="thread">`));
    expect(empty).toContain(`<h3>Ask the agent<span class="thread-tools"><button class="linkbtn" type="button" data-msg="hide"`);
    expect(empty).toContain(`</h3><div class="compose" data-compose>`);
    payloads["/api/runs/p1"] = detail;
    await page.showPaper!("p1", false);
    expect(status).toMatch(/<b>The agent decided<\/b> on Lemma 1 .*class="review-b">kept the lemma for <span class="katex">/);
    // the margin: the decision card first, beside its statement; then the notes, the owner's reading editable at rest
    const cards = last("#rail-cards");
    expect(cards.indexOf(`data-card="repair:thm:a"`)).toBeGreaterThan(-1);
    expect(cards.indexOf(`data-card="repair:thm:a"`)).toBeLessThan(cards.indexOf(`data-card="c1"`));
    expect(cards).toContain(`data-anchor="lbl-thm-a" data-repair="thm:a"`);
    expect(cards).toContain("With split-off result 1 — the Gaussian case");
    expect(cards).toContain(`<span class="cname">The agent recommends</span><span class="ctag">redo with guidance</span>`);
    expect(cards).toContain("0 of 1 decided");
    expect(cards).toContain(`data-reading="edit">Edit</button>`);
    expect(cards).toMatch(/data-card="c3"[^>]*>\s*<div class="cbyline">.*A note on running text\./s);
    // a comment that asks no decision offers, at its foot, to report an issue with it; the decision card does not
    const cardOf = (html: string, id: string) => html.split(`<div class="card`).find((c) => c.includes(`data-card="${id}"`)) ?? "";
    for (const c of paper.comments) expect(cardOf(cards, c.id)).toContain(`<button class="linkbtn" type="button" data-flag="open">Report an issue</button>`);
    expect(cardOf(cards, "repair:thm:a")).not.toContain("data-flag");
    expect(status).not.toContain("data-flag");
    // the proof map: the weakened theorem needs the owner; its corollary is named after it; the prose result by its line
    const map = last("#pm-marks");
    expect(map).toMatch(/class="pm-node st-error pm-top needs " data-pm="thm:a"/);
    expect(map).toContain(`data-pm="thm:cor-fix-0a1b2c3d" tabindex="0" role="button"><title>Corollary 1.1</title>`);
    expect(map).toContain(">Prop 3</text>");
    // under an error's statement with no corrected text: the repair is in the proof
    expect(at(`.formal[data-label="lem:b"]`).html).toContain(`<div class="rv-proofonly">The statement stands as printed. The repair is in its proof`);

    // every result's drawer draws; the referee's pinned reading and its enumerated detail among them
    for (const r of detail.results) {
      page.openDrawer!(r.id);
      expect((page.P as unknown as { drawer: string }).drawer).toBe(r.id);
      expect(last("#d-body")).toContain("<h4>Verdict</h4>");
    }
    page.openDrawer!("thm:a");
    expect(last("#d-body")).toMatch(/<b>Pinned reading:<\/b> The rate is in <span class="katex">/);
    expect(last("#d-body")).toContain(`<ol class="enum"><li><span class="ek">(a)</span>`);
    expect(at("#d-title").text).toBe("Theorem 1");
    page.openDrawer!("thm:cor-fix-0a1b2c3d");
    expect(at("#d-title").text).toBe("Corollary 1.1");

    // a result whose stored links are not this statement's: the statement as it stands, unlinked, one line saying so
    const shown = (page.P as unknown as { detail: { results: Array<Record<string, unknown>> } }).detail.results[0]!;
    const asSent = { ...shown };
    const leanView = { sharedHyps: [{ id: "r1", chip: "decl", code: "(P : Law)" }], conclusions: [{ id: "r2", hyps: [], code: "Good P" }] };
    Object.assign(shown, { lean: { decl: "X.a", file: "T.lean", line: 1 }, rows: [{ id: "r1", kind: "binder", names: "P", lean: "Law", segments: [], unstated: false }], leanView, linksStale: "changed", segments: null });
    page.openDrawer!("thm:a");
    // the notice says how links return: F5 again, or `relink` for this result
    expect(last("#d-body")).toContain(`<p class="stmt-note">The links on file were written for an earlier version of this statement, so none is shown. They return when F5 runs again, or with <code>leansmith relink p1 --toolkit &lt;toolkit&gt; --only thm:a</code>.</p>`);
    expect(last("#d-body")).toContain(`<div class="srow ds-concl" data-binder=""><span class="ds-chip ds-chip-concl" title="what the result concludes">then</span><div class="ds-code">Good P</div></div>`);
    expect(last("#d-body")).not.toMatch(/rtag|F5 links these rows/);
    // … and says which refusal it is: links against the statement cut short, or for another cut of it
    Object.assign(shown, { linksStale: "truncated" });
    page.openDrawer!("thm:a");
    expect(last("#d-body")).toContain("The links on file were written against this statement cut short (an older reader stopped before its end), so none is shown.");
    Object.assign(shown, { linksStale: "recut" });
    page.openDrawer!("thm:a");
    expect(last("#d-body")).toContain("written by an earlier link step for rows that are not this statement's rows now");
    // a result no call answered; a declaration the file no longer holds
    Object.assign(shown, { linksStale: undefined, linksUnanswered: true, segments: [{ id: "s1", text: "The rate." }] });
    page.openDrawer!("thm:a");
    expect(last("#d-body")).toContain("F5 asked these rows, but no answer came back: none is linked. <code>leansmith relink p1 --toolkit &lt;toolkit&gt; --only thm:a</code> asks again.");
    Object.assign(shown, { linksUnanswered: undefined, rows: null, leanView: null, leanMissing: true, segments: null });
    page.openDrawer!("thm:a");
    expect(last("#d-body")).toContain("The file no longer holds this declaration");
    Object.assign(shown, { leanMissing: undefined, rows: [{ id: "r1", kind: "binder", names: "P", lean: "Law", segments: [], unstated: false }], leanView });
    // linked, on a page that cannot say where its phrases stand: the rows are drawn with their phrases, and none is blamed
    Object.assign(shown, { linksStale: undefined, segments: [{ id: "s1", text: "The rate is $n^{-1}$." }], leanView: { ...leanView, conclusions: [{ id: "r2", hyps: [], code: "Good P", xl: "s1" }] } });
    page.openDrawer!("thm:a");
    expect(last("#d-body")).toContain("The paper's phrases for these rows could not be located on this page.");
    expect(last("#d-body")).toContain(`<div class="srow ds-concl" data-binder="s1">`);
    expect(last("#d-body")).toContain(`<div class="ds-code">(P : Law)</div><span class="rtag">not linked yet</span>`);
    expect(last("#d-body")).not.toContain("phrase not found on this page");
    for (const k of Object.keys(shown)) delete shown[k];
    Object.assign(shown, asSent);
    page.openDrawer!("thm:cor-fix-0a1b2c3d");
    page.openDrawer!("prop:p3");
    expect(at("#d-title").text).toBe("Proposition 3");
    for (const r of detail.results) { page.selectNode!(r.id); page.jumpTo!(r.id); }
    expect(at("#pm-card").html).toContain("go to statement");

    // a ruling entered, then the same payloads again: nothing is drawn twice
    const P = page.P as unknown as { repair: Record<string, unknown>; sent: { key: string; seen: number } | null; drawer: string | null };
    P.repair["thm:a"] = { kind: "redo", text: "keep the rate", of: item.proposed };
    page.drawCards!();
    expect(last("#rail-cards")).toContain("1 of 1 decided");
    expect(last("#rail-cards")).toContain(`aria-pressed="true">Redo with guidance</button>`);
    let before = { cards: count("#rail-cards"), map: count("#pm-marks"), drawer: count("#d-body") };
    await page.showPaper!("p1", false);
    expect({ cards: count("#rail-cards"), map: count("#pm-marks"), drawer: count("#d-body") }).toEqual(before);

    // the ruling is sent: the card and the status box say so — and, the run seen at rest with the same
    // repair three times since, that it was not taken up: the card asks again, the ruling kept
    P.sent = { key: JSON.stringify([["thm:a", item.proposed]]), seen: 0 };
    page.drawCards!(); page.drawStatus!();
    expect(last("#rail-cards")).toContain("<b>Your decision was sent</b> (Redo with guidance)");
    expect(last("#rail-cards")).not.toContain("data-repairs-send");
    expect(at("#status").html).toContain("Your decisions on the repairs were sent");
    await page.showPaper!("p1", false); await page.showPaper!("p1", false);
    expect(P.sent).toMatchObject({ seen: 2 });
    await page.showPaper!("p1", false);
    expect(P.sent).toBeNull();
    expect(at(".toast").text).toContain("did not take up your decisions");
    expect(last("#rail-cards")).toContain(`aria-pressed="true">Redo with guidance</button>`);
    expect(last("#rail-cards")).toContain("data-repairs-send");
    expect(at("#status").html).toContain("A repair would make a result of the paper weaker.");
    before = { cards: count("#rail-cards"), map: count("#pm-marks"), drawer: count("#d-body") };

    // the run is started: live, the repair is no longer the owner's to rule on (the server sends none)
    payloads["/api/runs/p1"] = { ...detail, summary: { ...detail.summary, live: true, status: "running" }, repairs: [] };
    await page.showPaper!("p1", false);
    expect(at("#status").html).toContain(`id="stop-run"`);
    expect(at("#status .status .actions").html).toContain("Message the agent");
    expect(last("#rail-cards")).not.toContain(`data-card="repair:thm:a"`);
    expect(last("#rail-cards")).toContain("once the run is at rest"); // … and the reading is not editable meanwhile
    expect(last("#rail-cards")).not.toContain(`data-reading="edit"`);
    expect(count("#pm-marks")).toBe(before.map); // the results did not change: the map stands
    expect(count("#d-body")).toBe(before.drawer); // … and so does the open drawer
    // with an agent session attached (the run's orch.json), the owner's message reads delivered
    expect(at("#status").html).toContain("not delivered — waiting for the agent");
    // … only while its watcher is armed; between two watches it is read when the agent next checks
    payloads["/api/runs/p1"] = { ...detail, summary: { ...detail.summary, live: true, status: "running", orch: { agent: "Claude Code", since: "x", watching: false } }, repairs: [] };
    await page.showPaper!("p1", false);
    expect(at("#status").html).toContain("waiting for the agent — it will read it when it next checks");
    expect(at("#status").html).not.toContain("delivered");
    payloads["/api/runs/p1"] = { ...detail, summary: { ...detail.summary, live: true, status: "running", orch: { agent: "Claude Code", since: "x", watching: true } }, repairs: [] };
    await page.showPaper!("p1", false);
    expect(at("#status").html).toContain("delivered to the attached agent — waiting for the agent");
    expect(at("#status").html).not.toContain("not delivered");

    // the run ended without a halt: "needs you" comes with a control — Resume, and how to attach an agent
    payloads["/api/runs/p1"] = { ...detail, summary: { ...detail.summary, live: false, status: "needs-you", headline: "ended without a halt (crashed or killed) during V1.5 — resume the run", toResume: true, orch: null }, repairs: [], halt: null, pending: null };
    await page.showPaper!("p1", false);
    expect(at("#status").html).toContain(`id="resume-plain">Resume the run</button>`);
    expect(at("#status").html).toContain("No agent session is attached");

    // it halts with a NEW proposal for the same theorem: the earlier ruling is not carried over to it
    const next = { ...item, proposed: "The rate is $n^{-1/3}$." };
    payloads["/api/runs/p1"] = { ...detail, repairs: [{ ...detail.repairs[0]!, proposed: next.proposed }] };
    await page.showPaper!("p1", false);
    expect(last("#rail-cards")).toContain("0 of 1 decided");
    expect(last("#rail-cards")).not.toContain(`aria-pressed="true"`);

    // the open result changes (the referee re-graded it): its drawer follows, the others' parts too
    payloads["/api/runs/p1"] = { ...detail, results: detail.results.map((r) => (r.id === "prop:p3" ? { ...r, review: { correctness: "ok" } } : r)) };
    payloads["/api/runs/p1/drawers"] = { ...drawers, results: { ...drawers.results, "prop:p3": { ...drawers.results["prop:p3"], review: { correctness: "ok", detail: "Now it holds." } } } };
    await page.showPaper!("p1", false);
    expect(P.drawer).toBe("prop:p3");
    expect(count("#d-body")).toBe(before.drawer + 1);
    expect(last("#d-body")).toContain("Now it holds.");
    expect(count("#pm-marks")).toBe(before.map + 1);

    // an issue the owner reported on a note: shown at its foot (escaped) with Edit / Withdraw, the other
    // cards as before, and nothing more waits on the owner; once the agent acted on it, it says so
    payloads["/api/runs/p1"] = detail; payloads["/api/runs/p1/drawers"] = drawers;
    await page.showPaper!("p1", false);
    const statusWas = at("#status").html;
    const note = paper.comments.find((c) => c.kind === "note")!;
    const issue = { id: "obj-1", comment: note.key, node: "thm:a", kind: "note", excerpt: "The bound fails", text: "it holds for <n> = 1", at: "x" };
    payloads["/api/runs/p1"] = { ...detail, objections: [issue] };
    await page.showPaper!("p1", false);
    expect(cardOf(last("#rail-cards"), note.id)).toContain(`<p class="cfine">Issue reported: it holds for &lt;n&gt; = 1</p>`);
    expect(cardOf(last("#rail-cards"), note.id)).toMatch(/data-flag="edit">Edit<\/button>.*data-flag="withdraw">Withdraw<\/button>/);
    expect(cardOf(last("#rail-cards"), note.id)).not.toContain("Report an issue");
    expect(cardOf(last("#rail-cards"), ownCard)).toContain("Report an issue");
    expect(at("#status").html).toBe(statusWas);
    payloads["/api/runs/p1"] = { ...detail, objections: [{ ...issue, handled: true }] };
    await page.showPaper!("p1", false);
    expect(cardOf(last("#rail-cards"), note.id)).toContain(`<p class="cfine">Issue reported — addressed</p>`);
    expect(cardOf(last("#rail-cards"), note.id)).not.toMatch(/data-flag="(edit|withdraw)"/);
    // the text being written: a textarea in the card, Send / Cancel
    (page.P as unknown as { flag: unknown }).flag = { card: ownCard, text: "a <draft>" };
    page.drawCards!();
    expect(cardOf(last("#rail-cards"), ownCard)).toContain(`placeholder="Describe the issue">a &lt;draft&gt;</textarea>`);
    expect(cardOf(last("#rail-cards"), ownCard)).toMatch(/data-flag="send">Send<\/button>.*data-flag="cancel">Cancel<\/button>/);
    (page.P as unknown as { flag: unknown }).flag = null;

    // the reader goes to the list and returns: the paper's text, unchanged, is put back as it stood — not written again
    const bodies = count("#paper-body"), maps = count("#pm-marks");
    location.hash = "#/"; await page.route!();
    location.hash = "#/paper/p1"; await page.route!();
    expect(count("#paper-body")).toBe(bodies);
    expect(count("#pm-marks")).toBe(maps + 1); // … with the page around it drawn afresh
    // … and written anew when it changed meanwhile
    location.hash = "#/"; await page.route!();
    payloads["/api/runs/p1/paper"] = { ...paper, html: `${paper.html}<p>more</p>` };
    location.hash = "#/paper/p1"; await page.route!();
    expect(count("#paper-body")).toBe(bodies + 1);
    expect(last("#paper-body")).toContain("<p>more</p>");

    // nothing the page wrote holds a value it could not print
    for (const [where, html] of writes) if (where !== "#paper-body") expect(html).not.toMatch(/\[object Object\]|>undefined<|>null<|NaN/);
  });

  /** The page on this run with `over` laid over the run's detail; `confirm` answers its dialog and gives what it asked. */
  const served = async (over: Record<string, unknown>, more: Record<string, unknown> = {}) => {
    const ui = await startUiServer(cfg, { port: 0 });
    let payloads: Record<string, unknown>;
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = async (p: string) => (await fetch(`${base}${p}`, { headers: { Cookie } })).json();
      payloads = { "/api/toolkit": await get("/api/toolkit"), "/api/runs/p1": { ...(await get("/api/runs/p1") as object), messages: [], ...over }, "/api/runs/p1/drawers": await get("/api/runs/p1/drawers"), "/api/runs/p1/paper": await get("/api/runs/p1/paper"), ...more };
    } finally { await ui.close(); }
    const p = runPage("p1", payloads);
    await p.page.route!();
    const confirm = async (ok: boolean) => {
      const button = () => p.at(ok ? "#modal-ok" : "#modal-cancel") as unknown as { onclick?: () => void };
      for (let k = 0; k < 200 && typeof button().onclick !== "function"; k++) await new Promise((r) => setTimeout(r, 5));
      const asked = p.at("#modal-body").html;
      button().onclick!();
      return asked;
    };
    return { ...p, payloads, confirm, detail: payloads["/api/runs/p1"] as { repairs: Array<Record<string, unknown>> } };
  };
  // The finding this guards: a push that changed one card (an issue reported on it) drew all of them
  // again — a few hundred formulas on a long paper.
  it("a push that changes one margin card draws that card again, not all of them; another set of cards is drawn whole", async () => {
    const { page, writes, at, lists, payloads } = await served({});
    const paper = payloads["/api/runs/p1/paper"] as { comments: Array<{ id: string; key: string; kind: string }> };
    const count = (sel: string) => writes.filter(([w]) => w === sel).length, outer = () => writes.filter(([w]) => w.endsWith(" outerHTML"));
    // the cards as the page drew them, standing in the rail
    const ids = [...writes.filter(([w]) => w === "#rail-cards").at(-1)![1].matchAll(/<div class="card[^>]* data-card="([^"]+)"/g)].map((m) => m[1]!);
    expect(ids).toEqual(["repair:thm:a", ...paper.comments.map((c) => c.id)]);
    lists.set("#rail-cards .card", ids.map((id) => Object.assign(at(`#rail-cards [data-card="${id}"]`), { dataset: { card: id } })));
    const drawn = count("#rail-cards");
    const note = paper.comments.find((c) => c.kind === "note")!;
    payloads["/api/runs/p1"] = { ...(payloads["/api/runs/p1"] as object), objections: [{ id: "obj-1", comment: note.key, node: "thm:a", kind: "note", excerpt: "x", text: "it holds", at: "x" }] };
    await page.showPaper!("p1", false);
    expect(count("#rail-cards")).toBe(drawn);
    expect(outer().map(([w]) => w)).toEqual([`#rail-cards [data-card="${note.id}"] outerHTML`]);
    expect(outer()[0]![1]).toContain("Issue reported: it holds");
    // the same again: nothing is drawn
    page.drawCards!();
    expect([count("#rail-cards"), outer().length]).toEqual([drawn, 1]);
    // the decision is gone (the run took it up): other cards stand in the rail, drawn whole
    payloads["/api/runs/p1"] = { ...(payloads["/api/runs/p1"] as object), repairs: [] };
    await page.showPaper!("p1", false);
    expect([count("#rail-cards"), outer().length]).toEqual([drawn + 1, 1]);
  });

  const actions = (posts: Array<[string, unknown]>) => posts.map(([url, body]) => [url.split("/").at(-1), body]);

  it("a sent decision says where it went: a started run names its log; the demo's stand-in run, which writes none, says it was sent", async () => {
    const repairs = [{ ...item, recommendation: { kind: "accept", why: "true and enough" } }];
    for (const [reply, said] of [[undefined, "Started — log: ui.log"], [{ pid: 0, command: "leansmith verify …", demo: true }, "Sent to the demo run"]] as const) {
      const p = await served({ repairs }, reply ? { "POST /api/runs/p1/action": reply } : {});
      const sent = p.page.acceptRepairRecs!() as Promise<boolean>;
      await p.confirm(true);
      expect(await sent).toBe(true);
      expect(p.at(".toast").text).toBe(said);
    }
  });

  it("“Accept all recommendations” on the repairs: only with a recommendation on every undecided one; it sends exactly those, a choice made by hand kept", async () => {
    const proposed = item.proposed, guidance = "state the rate for n > 1";
    const three = (third: unknown) => [
      { ...item, recommendation: { kind: "redo", why: "the printed rate is false", guidance } },
      { ...item, node: "lem:b", recommendation: { kind: "accept", why: "true and enough" } },
      { ...item, node: "prop:p3", recommendation: third },
    ];
    // nothing waits: no button
    expect((await served({ repairs: [] })).at("#status").html).not.toContain("repair-recs");
    // one has no recommendation — or a redo with no guidance to give: disabled, naming it, and nothing is sent
    for (const third of [null, { kind: "redo", why: "try again" }]) {
      const off = await served({ repairs: three(third) });
      expect(off.at("#status").html).toContain(`<button class="btn" type="button" id="repair-recs" disabled title="No recommendation yet for: Proposition 3">Accept all recommendations</button>`);
      expect(off.page.acceptRepairRecs!()).toBe(false);
      expect(off.posts).toEqual([]);
    }
    // every one has: each takes its recommendation — the redo its guidance, the decline its reason — after one confirmation
    const all = await served({ repairs: three({ kind: "decline", why: "the claim is false" }) });
    expect(all.at("#status").html).toContain(`<button class="btn" type="button" id="repair-recs" >Accept all recommendations</button>`);
    let sent = all.page.acceptRepairRecs!() as Promise<boolean>;
    expect(await all.confirm(true)).toContain("<p>Send 3 decisions as recommended: accept 1, redo 1 (with the suggested guidance), decline 1?</p>");
    expect(await sent).toBe(true);
    const action = { kind: "rule-repairs", accept: ["lem:b"], decline: { nodes: ["prop:p3"], reason: "the claim is false" }, redo: [{ node: "thm:a", guidance }] };
    expect(actions(all.posts)).toEqual([["preview", { action }], ["action", { action }]]);
    expect(all.at("#rail-cards").html).toContain("<b>Your decision was sent</b>");
    // a choice made by hand stands, and the confirmation counts what goes out; cancelled, nothing is sent
    const mixed = await served({ repairs: three({ kind: "decline", why: "the claim is false" }) });
    const P = mixed.page.P as unknown as { repair: Record<string, unknown> };
    P.repair["lem:b"] = { kind: "decline", text: "my own reason", of: proposed };
    sent = mixed.page.acceptRepairRecs!() as Promise<boolean>;
    expect(await mixed.confirm(false)).toContain("<p>Send 3 decisions — 2 as recommended, 1 as you set it: accept 0, redo 1 (with the suggested guidance), decline 2?</p>");
    expect(await sent).toBe(false);
    expect(actions(mixed.posts).map(([k]) => k)).toEqual(["preview"]);
    expect(P.repair["lem:b"]).toMatchObject({ kind: "decline", text: "my own reason" });
    expect(actions(mixed.posts)[0]![1]).toEqual({ action: { kind: "rule-repairs", accept: [], decline: { nodes: ["lem:b", "prop:p3"], reason: "my own reason; the claim is false" }, redo: [{ node: "thm:a", guidance }] } });
    // every repair decided by hand: nothing is left for the button
    P.repair["thm:a"] = { kind: "accept", of: proposed }; P.repair["prop:p3"] = { kind: "accept", of: proposed };
    mixed.page.drawStatus!();
    expect(mixed.at("#status").html).not.toContain("repair-recs");
  });

  it("“Accept all recommendations” on a promotion round: the same rule over its entries and new topics, sent as “Apply” sends them", async () => {
    const entry = (id: string, kind: string | null) => ({ id, title: `Result ${id}`, content: "c", reference: "r", path: "", division: "Foundations", target_module: `Toolkit/Foundations/${id}.lean`, proposed_name: `Toolkit.${id}`, reuse_evidence: "e", relation_to_paper: "", lean_type: "", is_paper_result: false, checker: "", recommendation: kind ? { kind, why: "w" } : null });
    const round = (topicRec: unknown, decisions: Record<string, unknown> = {}, waiting = true) => ({ repairs: [], promotion: {
      round: "B", waiting, applied: false, checklist: "", skipped: 0, error: null, decisions,
      topics: [{ key: "topic:Foundations/New", path: "Foundations/New", scope: "s", for: ["one"], recommendation: topicRec }],
      proposals: [entry("one", "accept"), entry("two", "defer"), entry("three", "accept_with_edits")],
    } });
    const click = (p: { page: Record<string, (...a: unknown[]) => unknown> }) => p.page.promoClick!({ target: { id: "promo-accept-recs", closest: () => null } }) as Promise<void>;
    // the new topic has no recommendation (one an entry could take is none for it): disabled, naming it; nothing is written
    for (const topicRec of [null, { kind: "defer", why: "w" }]) {
      const off = await served(round(topicRec));
      expect(off.at("#promo").html).toContain(`<button class="btn" type="button" id="promo-accept-recs" disabled title="No recommendation yet for: Foundations/New">Accept all recommendations</button>`);
      await click(off);
      expect(off.posts).toEqual([]);
    }
    // every item has one: confirmed, the decisions are written into the checklist and the round applied
    const all = await served(round({ kind: "accept", why: "nothing else holds it" }));
    expect(all.at("#promo").html).toContain(`id="promo-accept-recs" >Accept all recommendations</button>`);
    expect(all.at("#promo").html).toContain("<b>The agent recommends: accept</b> — nothing else holds it");
    let done = click(all);
    expect(await all.confirm(true)).toContain("<p>Apply round B with 4 decisions as recommended: accept 2, accept with edits 1, generalize first 0, defer 1, decline 0?</p>");
    await done;
    const apply = { action: { kind: "apply-promotion", round: "B" } };
    expect(actions(all.posts)).toEqual([["preview", apply], ["promotion", { round: "B", decisions: {
      "topic:Foundations/New": { kind: "accept" }, one: { kind: "accept" }, two: { kind: "defer" }, three: { kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/three.lean" } },
    } }], ["action", apply]]);
    // an entry set by hand (here, or in the checklist) stands; cancelled, nothing is written
    const mixed = await served(round({ kind: "accept", why: "w" }, { one: { kind: "decline" } }));
    const P = mixed.page.P as unknown as { promo: Record<string, unknown> };
    P.promo.two = { kind: "accept" };
    done = click(mixed);
    expect(await mixed.confirm(false)).toContain("<p>Apply round B with 4 decisions — 2 as recommended, 2 as you set them: accept 2, accept with edits 1, generalize first 0, defer 0, decline 1?</p>");
    await done;
    expect(actions(mixed.posts)).toEqual([["preview", apply]]);
    expect(P.promo).toEqual({ two: { kind: "accept" }, "topic:Foundations/New": { kind: "accept" }, three: { kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/three.lean" } } });
    // nothing undecided, or a round not waiting on the owner: no button
    const decided = { "topic:Foundations/New": { kind: "accept" }, one: { kind: "accept" }, two: { kind: "defer" }, three: { kind: "decline" } };
    expect((await served(round({ kind: "accept", why: "w" }, decided))).at("#promo").html).not.toContain("promo-accept-recs");
    expect((await served(round({ kind: "accept", why: "w" }, {}, false))).at("#promo").html).not.toContain("promo-accept-recs");
  });

  // The finding this guards: a promotion entry's statement, then every other text beside it, was
  // shown as its source — `∑_{i=1}^{T}`, `$…$` — wherever the page escaped a text and did no more.
  it("a formula is drawn wherever a text is shown: a promotion round, the owner's message, a headline, the contents, the library", async () => {
    const entry = { id: "one", title: "A family bounded in L^q", content: "∑_{i=1}^{T} x_i ≤ $\\alpha^2$ <b>", reference: "r", path: "", division: "Foundations", target_module: "Toolkit/Foundations/One.lean", proposed_name: "Toolkit.one_x", reuse_evidence: "uses `sum_le_x` and S_T", relation_to_paper: "the paper's V_{t,i}", lean_type: "∀ x_i : ℝ, 0 ≤ x_i ^ 2", is_paper_result: false, checker: "agrees — the rate is n^(−1/2)", recommendation: null };
    const p = await served({ repairs: [], messages: [{ id: "m1", from: "user", at: "2026-10-01T00:00:00Z", words: "is x_{i} below $\\beta$?\nyes <b>" }], promotion: {
      round: "B", waiting: true, applied: false, checklist: "", skipped: 0, error: null, decisions: {},
      topics: [{ key: "topic:Foundations/New", path: "Foundations/New", scope: "sums ∑_i a_i", for: ["one"], recommendation: null }], proposals: [entry],
    } });
    const promo = p.at("#promo").html;
    expect(promo).toContain(`<p class="pstmt">sums ∑<sub>i</sub> a<sub>i</sub></p>`);
    expect(promo).toContain("Needed by: A family bounded in L<sup>q</sup>.");
    expect(promo).toMatch(/<h3>A family bounded in L<sup>q<\/sup><\/h3><p class="pstmt">∑<sub>i=1<\/sub><sup>T<\/sup> x<sub>i<\/sub> ≤ <span class="katex">.*<\/span> &lt;b&gt;<\/p>/);
    expect(promo).toContain(`<p class="meta">the paper's V<sub>t,i</sub></p>`);
    expect(promo).toContain("<p>uses <code>sum_le_x</code> and S<sub>T</sub></p><p>agrees — the rate is n<sup>(−1/2)</sup></p>");
    // Lean stays code, as written
    expect(promo).toContain(`<code>Toolkit.one_x</code>`);
    expect(promo).toContain(`<pre class="st">∀ x_i : ℝ, 0 ≤ x_i ^ 2</pre>`);
    // the owner's own words: their formula typeset, their line breaks kept, never markup
    expect(p.at("#status").html).toMatch(/<div class="msg-b">is x<sub>i<\/sub> below <span class="katex">.*<\/span>\?<br>yes &lt;b&gt;<\/div>/);
    // a headline that quotes the agent's question
    const P = p.page.P as unknown as { detail: { summary: { headline: string } }; paper: { toc: unknown[] } };
    P.detail.summary.headline = "the agent asks you: is $n \\ge 1$ <meant>?";
    p.page.drawStatus!();
    expect(p.at("#status").html).toMatch(/<h2>the agent asks you: is <span class="katex">.*<\/span> &lt;meant&gt;\?<\/h2>/);
    // the contents: a heading as the paper draws it
    P.paper.toc = [{ id: "sec-1", text: "1 A 24 design", html: `1 A <span class="katex">2⁴</span> design`, level: 1 }];
    p.page.drawPaperBody!();
    expect(p.at("#toc").html).toBe(`<li class="l1"><a href="#sec-1" data-sec="sec-1">1 A <span class="katex">2⁴</span> design</a></li>`);

    // the list of papers and the inbox
    const tk = p.payloads["/api/toolkit"] as { runs: Array<Record<string, unknown>> };
    p.payloads["/api/toolkit"] = { ...tk, runs: [{ ...tk.runs[0]!, status: "needs-you", headline: "the agent asks you: is $n \\ge 1$ <meant>?" }] };
    p.location.hash = "#/";
    await p.page.route!();
    await p.page.refreshInbox!();
    for (const where of ["#waiting", "#runs-body", "#inbox-list"]) expect(p.at(where).html).toMatch(/the agent asks you: is <span class="katex">.*<\/span> &lt;meant&gt;\?/);
    // (a tooltip is plain text: the headline as written, beside the drawn one)
    expect(p.at("#runs-body").html).toContain(`<small title="the agent asks you: is $n \\ge 1$ &lt;meant&gt;?">`);

    // the library: a module's title and summary, a docstring with its linked phrases and its code, the phrases under their rows
    const decl = { leaf: "sum_sq", name: "Toolkit.sum_sq", kind: "theorem", sig: "(a : ℕ → ℝ) (hT_pos : 0 < T) : 0 ≤ a 0", doc: "For [a family a_i with T^{2} terms](hyp:hT_pos), [the sum ∑_{i} a_i^2 is ≥ $0$](goal) by `sq_nonneg_x` <b>.", uses: [], usedBy: [], papers: [] };
    p.payloads["/api/library"] = { modules: [{ path: "Foundations/Sums", module: "Toolkit.Foundations.Sums", title: "Sums ∑_{i} a_i", summary: "For reals `a_i`, bounds on x^2.", decls: [decl] }], papers: [], linked: 1, generic: 0 };
    p.location.hash = "#/library";
    await p.page.route!();
    expect(p.at("#lib-main").html).toContain("<td>Sums ∑<sub>i</sub> a<sub>i</sub><small>Toolkit.Foundations.Sums</small></td>");
    (p.page.LS as unknown as { mod: string }).mod = "Foundations/Sums";
    p.page.drawLib!();
    const lib = p.at("#lib-main").html;
    expect(lib).toContain(`<h1 class="mod-title">Sums ∑<sub>i</sub> a<sub>i</sub></h1><p class="mod-sum">For reals <code>a_i</code>, bounds on x<sup>2</sup>.</p>`);
    expect(lib).toMatch(/<div class="ddoc">For <span class="xl" data-xl="hT_pos">a family a<sub>i<\/sub> with T<sup>2<\/sup> terms<\/span>, <span class="xl" data-xl="⊢">the sum ∑<sub>i<\/sub> a<sub>i<\/sub><sup>2<\/sup> is ≥ <span class="katex">.*<\/span><\/span> by <code>sq_nonneg_x<\/code> &lt;b&gt;\.<\/div>/);
    expect(lib).toContain(`<div class="sdoc">a family a<sub>i</sub> with T<sup>2</sup> terms</div>`);
    // the Lean statement is code
    expect(lib).toContain(`<span class="sn">hT_pos</span><span class="sc">:</span><span class="st">0 &lt; T</span>`);
  });
});
