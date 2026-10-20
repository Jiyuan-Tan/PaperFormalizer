/**
 * Authors' note macros (`note_macros.ts`): the wrappers co-authors put around edited passages and the
 * comments they leave are read away when the paper is flattened — by deterministic rules on their
 * definitions — so no unit is cut inside one; the line map stays; the annotated paper keeps the
 * author's wrappers and the corrected paper is written as the paper was read. What the rules do not
 * cover is left as written and handed to the orchestrator in one parser warning per macro.
 */
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { alignToOriginal, braceProblem } from "../../src/verify/annotate_tex.js";
import { applyEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import {
  AUTHOR_NOTES_FILE,
  NOTE_MACRO_HANDOFF,
  NOTE_MACROS_VERSION,
  SOURCE_FILLER,
  applyEditsKeepingNotes,
  applyNoteEdits,
  classifyBody,
  detectNoteMacros,
  parseMacroDefinitions,
  readNotes,
  scanNotes,
  scanTextOf,
  unwrapSource,
  withoutFillerLines,
  type AuthorNotes,
  type NoteMacroTable,
} from "../../src/verify/note_macros.js";
import { sourcePlaces, warningsSection } from "../../src/verify/stage_v1_5.js";
import { buildEnvsJson, flattenTex, recordedNoteMacros, writeEnvsArtifacts } from "../../src/verify/tex_envs.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { PaperUnits, flatLineStart } from "../../src/verify/units.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

async function sourceTree(files: Record<string, string>): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "note-macros-"));
  tmpDirs.push(dir);
  for (const [f, t] of Object.entries(files)) {
    await mkdir(path.dirname(path.join(dir, f)), { recursive: true });
    await writeFile(path.join(dir, f), t, "utf8");
  }
  return dir;
}

/** `body` read with the macros `preamble` defines (one text, as the flattener hands it over). */
function read(preamble: string, body: string): { text: string; notes: AuthorNotes; warnings: string[]; table: NoteMacroTable } {
  const flat = `${preamble}\n\\begin{document}\n${body}\n\\end{document}`;
  const r = readNotes(flat, flat.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })));
  expect(r.text.split("\n").length).toBe(flat.split("\n").length);
  const from = r.text.indexOf("\\begin{document}\n") + "\\begin{document}\n".length;
  return { text: r.text.slice(from, r.text.lastIndexOf("\n\\end{document}")), notes: r.notes, warnings: r.warnings, table: r.table };
}
const R = String.raw;

describe("a definition's class", () => {
  const table: Array<[string, string]> = [
    // keep: exactly the argument, under colour, highlight or grouping
    ["{\\color{black} #1}", "keep"],
    ["\\textcolor{red}{#1}", "keep"],
    ["\\textcolor[rgb]{1,0,0}{#1}", "keep"],
    ["{\\color{blue}#1}", "keep"],
    ["{#1}", "keep"],
    ["#1", "keep"],
    ["\\hl{#1}", "keep"],
    ["\\leavevmode{\\color{red} #1}\\normalcolor", "keep"],
    // hide: an empty body
    ["", "hide"],
    ["{}", "hide"],
    ["{{}}", "hide"],
    // comment: the argument handed to a note command
    ["\\marginpar{#1}", "comment"],
    ["\\todo{#1}", "comment"],
    ["\\todo[inline,color=red]{#1}", "comment"],
    ["{\\color{red}\\fxnote{#1}}", "comment"],
    // leave: the body prints anything else — no class is guessed from a tag, a font or a strike
    ["[RJ: #1]", "leave"],
    ["\\textbf{LP:} #1", "leave"],
    ["{\\color{red}[TODO: #1]}", "leave"],
    ["\\textcolor{red}{H1: #1}", "leave"],
    ["\\textbf{Note:} #1", "leave"],
    ["#1 -- QED", "leave"],
    ["\\todo[inline]{RJ: #1}", "leave"],
    ["\\textcolor{red}{#1}\\marginpar{changed}", "leave"],
    ["\\textcolor{red}{\\sout{#1}}", "leave"],
    ["\\textbf{#1}", "leave"],
    ["{\\it #1}", "leave"],
    ["\\mathbf{#1}", "leave"],
    ["E[#1]", "leave"],
    ["(#1)", "leave"],
    ["\\footnote{#1}", "leave"],
    ["#1 and #1", "leave"],
    ["\\color{#1}", "leave"],
    ["\\ifdraft #1\\fi", "leave"],
    ["\\textcolor{red}{[deleted]}", "leave"],
    // a text-mode box; what TeX does with the space around the argument; text set in white (hidden)
    ["\\colorbox{yellow}{#1}", "leave"],
    ["#1\\xspace", "leave"],
    ["\\unskip #1", "leave"],
    ["\\ignorespaces", "leave"],
    ["\\textcolor{white}{#1}", "leave"],
    ["{\\color{white}#1}", "leave"],
    ["\\textcolor{#1}{x}", "leave"],
  ];
  it.each(table)("%s → %s", (body, cls) => {
    expect(classifyBody(body).class).toBe(cls);
  });

  it("a one-argument definition is read in each of its forms; any other definition of a name is seen and not parsed", () => {
    const pre = [
      "\\newcommand{\\a}[1]{{\\color{black} #1}}",
      "\\newcommand*\\b[1]{\\textcolor{red}{#1}}",
      "\\def\\c#1{}",
      "\\long\\def\\d#1{{#1}}",
      "\\DeclareRobustCommand{\\e}[1]{#1}",
      "\\NewDocumentCommand{\\f}{m}{\\todo{#1}}",
      "\\newcommand{\\opt}[2][]{\\todo[#1]{#2}}",
      "\\newcommand{\\two}[2]{\\sout{#1}\\textcolor{red}{#2}}",
      "\\def\\delim#1.{#1}",
      "\\newcommand{\\zero}{}",
      "\\DeclareMathOperator{\\op}{op}",
      "\\edef\\ex{x}",
      "\\let\\copied\\textbf",
    ].join("\n");
    const t = detectNoteMacros(pre);
    expect(Object.fromEntries(t.macros.filter((m) => m.from === "definition").map((m) => [m.name, m.class]))).toEqual({ a: "keep", b: "keep", c: "hide", d: "keep", e: "keep", f: "comment" });
    const defs = parseMacroDefinitions(pre);
    expect(defs.map((d) => `${d.name}:${d.body === null ? "-" : "1"}`)).toEqual(["a:1", "b:1", "c:1", "d:1", "e:1", "f:1", "opt:-", "two:-", "delim:-", "zero:-", "op:-", "ex:-", "copied:-"]);
    // a definition this module does not parse is spanned whole: nothing in it is ever edited
    expect(pre.slice(defs[7]!.start, defs[7]!.end)).toBe("\\newcommand{\\two}[2]{\\sout{#1}\\textcolor{red}{#2}}");
  });

  it("a commented-out definition is none: the active one of two decides", async () => {
    const dir = await sourceTree({
      "main.tex": "\\documentclass{article}\n\\input{macros}\n\\begin{document}\nA \\rj{kept} B \\lp{gone} C.\n\\end{document}\n",
      "macros.tex": ["\\newcommand{\\rj}[1]{{\\color{black} #1}}", "%\\newcommand{\\rj}[1]{}", "%\\newcommand{\\lp}[1]{\\textcolor{red}{#1}}", "\\newcommand{\\lp}[1]{}", ""].join("\n"),
    });
    const flat = await flattenTex(dir, "main.tex");
    expect(flat.text).toContain("A {kept} B  C.");
    expect(flat.notes!.table.macros.filter((m) => m.from === "definition").map((m) => `${m.name}:${m.class}`).sort()).toEqual(["lp:hide", "rj:keep"]);
    // the definitions themselves are never touched
    expect(flat.text).toContain("\\newcommand{\\rj}[1]{{\\color{black} #1}}");
  });

  it("a macro is read only when all its definitions agree, outside any conditional or group and before \\begin{document}", () => {
    const body = "A \\lp{x} B.";
    const left = (pre: string, doc = body): string => {
      const r = read(pre, doc);
      expect(r.table.macros.some((m) => m.name === "lp")).toBe(false);
      return r.text;
    };
    // a later definition of another class (the earlier use printed as mathematics)
    expect(left("\\newcommand{\\lp}[1]{\\mathbf{#1}}", "$\\lp{x}$\n\\renewcommand{\\lp}[1]{}\nA \\lp{y}.")).toContain("$\\lp{x}$");
    expect(left("\\newcommand{\\lp}[1]{{\\color{red}#1}}\n\\renewcommand{\\lp}[1]{}")).toBe(body);
    expect(left("\\newcommand{\\lp}[1]{{\\color{red}#1}}\n\\providecommand{\\lp}[1]{}")).toBe(body);
    // a single definition under a conditional, in a group, inside another definition, after \begin{document}
    expect(left("\\ifdefined\\x\\else\\newcommand{\\lp}[1]{}\\fi")).toBe(body);
    expect(left("\\newif\\ifdraft\n\\ifdraft\\newcommand{\\lp}[1]{\\textcolor{red}{#1}}\\else\\newcommand{\\lp}[1]{}\\fi")).toBe(body);
    expect(left("{\\newcommand{\\lp}[1]{}}")).toBe(body);
    expect(left("\\begingroup \\newcommand{\\lp}[1]{} \\endgroup")).toBe(body);
    expect(left("\\newcommand{\\draft}{\\newcommand{\\lp}[1]{}}")).toBe(body);
    expect(left("\\AtBeginDocument{\\renewcommand{\\lp}[1]{}}\n\\newcommand{\\lp}[1]{{#1}}")).toBe(body);
    expect(left("", "\\newcommand{\\lp}[1]{}\nA \\lp{x} B.")).toContain("A \\lp{x} B.");
    // a definition this reader does not parse beside one it does
    expect(left("\\newcommand{\\lp}[1]{}\n\\let\\lp\\textbf")).toBe(body);
    expect(left("\\newcommand{\\lp}[1]{}\n\\edef\\lp{x}")).toBe(body);
    // an etoolbox test taking arguments is no conditional: the definition after it is read
    expect(read("\\ifdef{\\x}{}{}\n\\newcommand{\\lp}[1]{}", body).text).toBe("A  B.");
  });

  it("a shipped package's definition counts with the paper's; a class's macros are the publisher's", async () => {
    const tree = (sty: string, pre = ""): Promise<string> =>
      sourceTree({ "main.tex": `\\documentclass{house}\n\\usepackage{mynotes}\n${pre}\n\\begin{document}\nA \\ed{b} C \\meta{d} E.\n\\end{document}\n`, "mynotes.sty": sty, "house.cls": "\\LoadClass{article}\n\\def\\meta#1{}\n" });
    expect((await flattenTex(await tree("\\newcommand{\\ed}[1]{{\\color{blue}#1}} % \\newcommand{\\ed}[1]{}\n"), "main.tex")).text).toContain("A {b} C \\meta{d} E.");
    // the package redefines what the paper defined: they differ, the uses stay
    expect((await flattenTex(await tree("\\renewcommand{\\ed}[1]{\\widehat{#1}}\n", "\\newcommand{\\ed}[1]{}"), "main.tex")).text).toContain("A \\ed{b} C");
  });
});

describe("package commands", () => {
  const body = "A \\added[id=RJ]{new} \\deleted{old} \\replaced[id=LP]{this}{that} \\todo[inline]{fix} \\hl{h} \\sout{s}\\marginpar{m} Z.";
  it("are read only when the paper loads their package", () => {
    expect(read("", body).text).toBe(body.replace("\\marginpar{m}", ""));
    const r = read("\\usepackage[final]{changes}\n\\usepackage{todonotes,soul}\n\\usepackage[normalem]{ulem}", body);
    expect(r.text).toBe("A {new}  {this}  {h}  Z.");
    // what a kept use drops is recorded too, whole
    expect(r.notes.dropped).toEqual([
      { macro: "\\added", file: "main.tex", line: 5, text: "[id=RJ]" },
      { macro: "\\replaced", file: "main.tex", line: 5, text: "[id=LP] {that}" },
    ]);
    expect(r.notes.removed.map((x) => `${x.macro} ${x.class} ${x.text}`)).toEqual(["\\deleted hide old", "\\todo comment fix", "\\sout hide s", "\\marginpar comment m"]);
  });

  it("yield to ANY definition of their name in the paper or a file it ships, in any form", async () => {
    const st = "$\\min f(x) \\sout {x \\in C}$ and \\hl{y} and \\todo{z}.";
    for (const def of [
      "\\DeclareMathOperator{\\sout}{s.t.}",
      "\\newcommand{\\sout}{\\text{s.t.}}",
      "\\def\\sout{\\mathrm{s.t.}}",
      "\\edef\\sout{s.t.}",
      "\\let\\sout\\relax",
      "\\renewcommand{\\sout}[2]{#1}",
    ]) {
      const r = read(`\\usepackage{ulem}\n${def}`, st);
      expect(r.text, def).toBe(st);
      // the definition line itself is never edited
      expect(readNotes(`\\usepackage{ulem,soul}\n${def}\n\\begin{document}\n\\hl{a}\n`, []).text, def).toContain(`${def}\n`);
    }
    // defined again in a shipped package or class
    for (const file of ["my.sty", "my.cls"]) {
      const dir = await sourceTree({
        "main.tex": `\\documentclass{${file === "my.cls" ? "my" : "article"}}\n\\usepackage{soul,todonotes,my}\n\\begin{document}\n${st}\n\\end{document}\n`,
        [file]: "\\renewcommand{\\hl}[1]{\\widehat{#1}}\n\\renewcommand{\\todo}[1]{\\textbf{#1}}\n",
      });
      expect((await flattenTex(dir, "main.tex")).text, file).toContain(st);
    }
    // also in a form this reader parses, before or after the package is loaded: which one is in force is not its to say
    expect(read("\\usepackage{todonotes}\n\\renewcommand{\\todo}[1]{}", "A \\todo[x]{b} C \\todo{d}.").text).toBe("A \\todo[x]{b} C \\todo{d}.");
    expect(read("\\def\\hl#1{}\n\\usepackage{soul}\n\\def\\added#1{}\n\\usepackage{changes}", "A \\hl{shown} B \\added{shown}.").text).toBe("A \\hl{shown} B \\added{shown}.");
    // without the package the name is the paper's own macro
    expect(read("\\newcommand{\\todo}[1]{}", "A \\todo{d}.").text).toBe("A .");
    // an object's inherited names are no table entries
    expect(read("", "A \\constructor{x} \\toString{y} \\hasOwnProperty{z}.").text).toBe("A \\constructor{x} \\toString{y} \\hasOwnProperty{z}.");
  });
});

describe("uses", () => {
  const PRE = ["\\newcommand{\\lp}[1]{{\\color{black} #1}}", "\\newcommand{\\rj}[1]{\\textcolor{red}{#1}}", "\\newcommand{\\hide}[1]{}", "\\newcommand{\\note}[1]{\\todo[inline]{#1}}"].join("\n");

  it("a kept wrapper leaves its group, which may be what the mathematics is; the braces go only around several sentences", () => {
    expect(read(PRE, R`$\lp{a \over b} + c$, $\rj{n \choose k} x$, $\sqrt\lp{x+y}$, $\lp{\cal A}+B$, $\mathop\lp{ab}$, $x^\rj{ab}$, \emph\lp{word}.`).text).toBe(
      "${a \\over b} + c$, ${n \\choose k} x$, $\\sqrt{x+y}$, ${\\cal A}+B$, $\\mathop{ab}$, $x^{ab}$, \\emph{word}.",
    );
    expect(read(PRE, "A \\lp{b \\rj{c \\lp{d}} e} f. \\lp{One. Two \\rj{three}.} G \\lp{\\bf bold} h.").text).toBe("A {b {c {d}} e} f. One. Two {three}. G {\\bf bold} h.");
    expect(read(PRE, "\\lp{Set $\\{x : x_{i} > 0\\}$. Then\n\\begin{align}\na &= b^{2}\n\\end{align}\nDone \\} here.} Z.").text).toBe("Set $\\{x : x_{i} > 0\\}$. Then\n\\begin{align}\na &= b^{2}\n\\end{align}\nDone \\} here. Z.");
    expect(read(PRE, "\\begin{itemize} \\lp{\\item one \\item two} \\end{itemize}").text).toBe("\\begin{itemize} \\item one \\item two \\end{itemize}");
    // classes nested in one another
    expect(read(PRE, "A \\lp{b \\note{why \\lp{c}?} d \\hide{e \\rj{f}}} g.").text).toBe("A {b  d } g.");
  });

  it("no `[` is exposed to an \\item or a \\\\ before the use", () => {
    expect(read(PRE, "\\begin{itemize} \\item\\hide{x}[0,1] too. \\end{itemize} a \\\\ \\hide{x} *b \\[ a \\\\ \\lp{[b]} \\]").text).toBe("\\begin{itemize} \\item{}[0,1] too. \\end{itemize} a \\\\ {} *b \\[ a \\\\ {[b]} \\]");
  });

  it("a use in a comment or in verbatim is untouched (the source read as the flat text is); \\string\\lp prints the name", () => {
    const src = "A \\lp{b} % was \\lp{c}\n\\begin{verbatim}\n\\lp{d}\n\\end{verbatim}\n\\verb|\\lp{e}| \\texttt{\\string\\hide{z}} \\hide{f}.";
    const table = detectNoteMacros(PRE);
    expect(unwrapSource(src, table, "remove")).toBe("A {b} % was \\lp{c}\n\\begin{verbatim}\n\\lp{d}\n\\end{verbatim}\n\\verb|\\lp{e}| \\texttt{\\string\\hide{z}} .");
    const blank = unwrapSource(src, table, "blank");
    expect(blank.length).toBe(src.length);
    expect(blank).toContain("A    {b} % was \\lp{c}");
  });

  it("a line a removal empties inside a paragraph keeps an empty group; between paragraphs nothing is added", () => {
    expect(read(PRE, "One\n\\note{check}\ntwo.\n\n\\note{again}\n\nThree \\hide{x\n\ny} four.").text).toBe("One\n{}\ntwo.\n\n\n\nThree \n{}\n four.");
    expect(read(PRE, "One\n\\lp{\nTwo. Three.\n}\nfour.").text).toBe("One\n{}\nTwo. Three.\n{}\nfour.");
    // a source file's emptied lines are marked, and dropped from a text written from it
    const table = detectNoteMacros(PRE);
    const src = unwrapSource("One\n\\note{check}\ntwo.\n{}\n", table, "remove", SOURCE_FILLER);
    expect(src).toBe(`One\n${SOURCE_FILLER}\ntwo.\n{}\n`);
    expect(withoutFillerLines(src)).toBe("One\ntwo.\n{}\n");
  });

  it("is idempotent, and keeps every line where it is", () => {
    const flat = `${PRE}\n\\begin{document}\nA \\lp{b\n\nc \\note{d\ne} f} g \\rj{h}\n\\end{document}`;
    const map = flat.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 }));
    const once = readNotes(flat, map);
    const twice = readNotes(once.text, map);
    expect(twice.text).toBe(once.text);
    expect(twice.notes.read_with).toEqual([]);
    expect(once.text.split("\n").length).toBe(flat.split("\n").length);
  });
});

describe("the reader declines what it cannot read exactly", () => {
  const PRE = "\\newcommand{\\hide}[1]{}\n\\newcommand{\\rj}[1]{{\\color{red}#1}}";
  const same = (pre: string, body: string): void => expect(read(pre, body).text, `${pre} | ${body}`).toBe(body);

  it("a \\providecommand defines nothing when the name exists: the name is left", () => {
    same("\\providecommand{\\text}[1]{#1}\n\\providecommand{\\keywords}[1]{}\n\\providecommand{\\emph}[1]{}", "Let $a = b \\text{ if } c$ and \\emph{not} zero. \\keywords{k1, k2}");
    same("\\providecommand{\\rj}[1]{#1}\n\\providecommand{\\rj}[1]{}", "A \\rj{x}.");
    same("\\ProvideDocumentCommand{\\rj}{m}{}", "A \\rj{x}.");
  });

  it("a macro defined through a formatting or note command the paper defines itself", () => {
    const pre = ["\\renewcommand{\\hl}[1]{\\widehat{#1}}", "\\newcommand{\\new}[1]{\\hl{#1}}", "\\renewcommand{\\textcolor}[2]{}", "\\newcommand{\\nn}[1]{\\textcolor{red}{#1}}", "\\newcommand{\\todo}[1]{{\\color{red}#1}}", "\\newcommand{\\jt}[1]{\\todo{#1}}"].join("\n");
    expect(read(pre, "A \\new{a} B \\hl{b} C \\nn{c} D \\todo{shown} E \\jt{shown2}.").text).toBe("A \\new{a} B \\hl{b} C \\nn{c} D {shown} E \\jt{shown2}.");
  });

  it("a name given a meaning through its letters or patched, a \\def whose argument is delimited", () => {
    for (const def of ["\\csdef{rj}#1{#1}", "\\expandafter\\def\\csname rj\\endcsname#1{#1}", "\\makeatletter\\@namedef{rj}#1{#1}\\makeatother", "\\apptocmd{\\rj}{shown}{}{}"]) same(`\\newcommand{\\rj}[1]{}\n${def}`, "A \\rj{shown} B.");
    same("\\def\\rj#1 {}", "A \\rj{x}gone here B.");
  });

  it("several sentences whose braces cannot go: a bracket or a star at the edge, a row break, a command before the use", () => {
    for (const body of [
      "A \\\\\\rj{*One. Two.} C",
      "\\begin{itemize}\n\\item[\\rj{Case A]. It holds. Then B.}] foo\n\\item \\rj{[0,1] is compact. So is $K$.}\n\\item \\rj{One. Two.\\\\}\n[kept] bar\n\\end{itemize}",
      "\\begin{proof}[\\rj{Proof of [1]. Second sentence.}] x \\end{proof}",
      "\\rj{One. Two.}[x] and \\rj{One. Two.}*",
      "\\emph\\rj{One. Two.} \\footnote\\rj{Foot. Note.}",
    ]) {
      const r = read(PRE, body);
      expect(r.text, body).toBe(body);
      expect(r.notes.left.join("\n"), body).toMatch(/^\\rj \(defined: [^)]*\) spans several sentences where its braces cannot be dropped/);
    }
  });

  it("a bracket in the content is no obstacle outside an optional argument", () => {
    expect(read(PRE, "By \\cite[p.~3]{k}, \\rj{we have $E[X] = 0$. Then $x \\in [0,1]$.} Done.").text).toBe("By \\cite[p.~3]{k}, we have $E[X] = 0$. Then $x \\in [0,1]$. Done.");
  });

  it("a removal alone on its lines after a row break; literal text; a control symbol before a word", () => {
    same(PRE, "\\begin{tabular}{c}\na \\\\\n\\hide{note}\n\\hline\nb\n\\end{tabular}");
    const table = detectNoteMacros(PRE);
    const literal = "\\url{http://a.b/\\hide{x}} \\path|\\hide{q}| \\detokenize{\\hide{y}} \\mintinline{tex}|\\hide{q}| \\string \\hide{x}\n\\begin{tcblisting}{}\n\\hide{code}\n\\end{tcblisting}";
    expect(unwrapSource(literal, table, "remove")).toBe(literal);
    same(PRE, literal);
    expect(read(PRE, "A\\\\word\\hide{x}more and \\alpha\\hide{x}b.").text).toBe("A\\\\wordmore and \\alpha b.");
  });
});

describe("what the reader declines is handed to the orchestrator: one warning per macro", () => {
  const PRE = [
    "\\newcommand{\\lp}[1]{{\\color{black} #1}}",
    "\\newcommand{\\cm}[1]{\\textcolor{red}{[RJ: #1]}}",
    "\\newcommand{\\rev}[2][]{\\textcolor{blue}{#2}}",
    "\\newcommand{\\vect}[1]{\\mathbf{#1}}",
    "\\let\\fn\\footnote",
    "\\ifdefined\\final\\newcommand{\\dr}[1]{}\\else\\newcommand{\\dr}[1]{\\textcolor{red}{#1}}\\fi",
  ].join("\n");

  it("a paper's macro it does not read, around several sentences: named with its definition, its first such use and their number", () => {
    const r = read(PRE, "A \\cm{one}. \\cm{Is this right. I doubt it.} B \\cm{Two. Three.}\n\\rev{Changed. Much.} $\\vect{x}$ \\fn{A note. Of two.} \\dr{Draft one. Draft two.} \\dr{d}");
    expect(r.text).toContain("\\cm{Is this right. I doubt it.}");
    expect(r.notes.left).toEqual([
      `\\cm (defined: \\newcommand{\\cm}[1]{\\textcolor{red}{[RJ: #1]}}) is not a macro this reader reads away (its definition prints more than its argument), and its argument spans several sentences: left as written (2 such use(s), first at main.tex:8); a unit cut inside such a use is not balanced TeX, and V1 or a later stage will stop on it. ${NOTE_MACRO_HANDOFF}.`,
      expect.stringMatching(/^\\rev \(defined: \\newcommand\{\\rev\}\[2\]\[\]\{\\textcolor\{blue\}\{#2\}\}\) is not a macro this reader reads away .* \(1 such use\(s\), first at main\.tex:9\)/),
      expect.stringMatching(/^\\dr \(defined: \\newcommand\{\\dr\}\[1\]\{\}\) is defined inside a conditional or a group, and its argument spans several sentences: left as written \(1 such use\(s\), first at main\.tex:9\)/),
    ]);
    expect(NOTE_MACRO_HANDOFF).toMatch(/parser gap.*smallest neutral edit in the run's copy of the source \(source\/\), record the edit in pipeline_issues\.md, and run it from V1/);
    expect(r.warnings.filter((w) => w.startsWith("note macros: \\"))).toHaveLength(3);
    // nothing is said of a macro whose uses stay within a sentence
    expect(read(PRE, "A \\cm{one} $\\vect{x}$ \\dr{d} \\rev{r}.").warnings).toEqual([]);
  });

  it("a use of a macro it reads that it cannot take: no braces, an argument that does not close or holds part of an environment, several sentences inside mathematics", () => {
    const r = read(PRE, "A \\lp b. \\lp c. $\\lp{x. Y}$ \\begin{itemize} \\item \\lp{x \\end{itemize} y} z\n\nC \\lp{d");
    expect(r.text).toBe("A \\lp b. \\lp c. $\\lp{x. Y}$ \\begin{itemize} \\item \\lp{x \\end{itemize} y} z\n\nC \\lp{d");
    expect(r.notes.left.map((l) => l.replace(/\. This is a parser gap.*$/, ""))).toEqual([
      "\\lp (defined: \\newcommand{\\lp}[1]{{\\color{black} #1}}) is used without a braced argument: left as written (2 such use(s), first at main.tex:8)",
      "\\lp (defined: \\newcommand{\\lp}[1]{{\\color{black} #1}}) spans several sentences inside mathematics: left as written (1 such use(s), first at main.tex:8); a unit cut inside such a use is not balanced TeX, and V1 or a later stage will stop on it",
      "\\lp (defined: \\newcommand{\\lp}[1]{{\\color{black} #1}}) has an argument holding part of an environment: left as written (1 such use(s), first at main.tex:8); a unit cut inside such a use is not balanced TeX, and V1 or a later stage will stop on it",
      "\\lp (defined: \\newcommand{\\lp}[1]{{\\color{black} #1}}) has an argument that does not close: left as written (1 such use(s), first at main.tex:10); a unit cut inside such a use is not balanced TeX, and V1 or a later stage will stop on it",
    ]);
  });
});

describe("removed text is recorded whole, and named on the result it was removed from", () => {
  const LONG = "Check the constant in \\eqref{eq:c}; I think it is $2$, see the argument of Section 3 which is much longer than two hundred characters when it is written out in full detail with all of its steps, every one of them, and then some more words to be sure.";
  const files = {
    "main.tex": [
      "\\documentclass{article}", // 1
      "\\usepackage{todonotes}", // 2
      "\\newcommand{\\rj}[1]{\\todo[color=red]{#1}}", // 3
      "\\newcommand{\\old}[1]{}", // 4
      "\\begin{document}", // 5
      "\\section{Results \\rj{rename?}}", // 6
      "\\begin{theorem}\\label{thm:a}", // 7
      "Let $x > 0$ \\rj{do we need this?}. Then $f(x) > 0$ for every such $x$ and every $f$ of the class.", // 8
      `\\todo[inline,color=red]{${LONG}}`, // 9
      "\\end{theorem}", // 10
      "\\begin{lemma}\\label{lem:b}", // 11
      "\\old{For all $n$ the bound holds, and this is the whole statement.}", // 12
      "\\end{lemma}", // 13
      "\\begin{proof}", // 14
      "It holds \\old{by induction on $n$, using the inequality above twice} trivially.", // 15
      "\\end{proof}", // 16
      "\\end{document}",
      "",
    ].join("\n"),
  };

  it("with file and line, in the parse log and the record beside envs.json; every removal inside a statement or proof is a warning naming it", async () => {
    const dir = await sourceTree(files);
    const parsed = await buildEnvsJson(dir, "main.tex");
    expect(parsed.flat.text).toContain("\\section{Results }");
    expect(parsed.flat.text).toContain("Let $x > 0$ . Then $f(x) > 0$ for every such $x$ and every $f$ of the class.\n{}\n\\end{theorem}");
    expect(parsed.flat.lineMap).toEqual((await flattenTex(dir, "main.tex", false)).lineMap);
    const rec = parsed.flat.notes!.record!;
    expect(rec.read_with).toEqual([
      { macro: "\\rj", class: "comment", uses: 2, why: "its definition sets its argument as a side note" },
      { macro: "\\todo", class: "comment", uses: 1, why: "todonotes: a to-do note" },
      { macro: "\\old", class: "hide", uses: 2, why: "its definition is empty" },
    ]);
    expect(rec.removed.map((r) => `${r.macro} ${r.file}:${r.line}`)).toEqual(["\\rj main.tex:6", "\\rj main.tex:8", "\\todo main.tex:9", "\\old main.tex:12", "\\old main.tex:15"]);
    // whole: no text is cut short in the record
    expect(rec.removed[2]!.text).toBe(LONG);
    expect(parsed.warnings[0]).toBe(
      `the paper was read with its authors' note macros read away — H \\old (2) removed; C \\rj (2), \\todo (1) removed (K: wrapper dropped, text kept; H: text the PDF does not print; C: authors' comments, not part of the paper) — every removed text is in ${AUTHOR_NOTES_FILE}`,
    );
    expect(parsed.flat.notes!.log).toContain("removed the author's comments of \\rj (2 use(s)): its definition sets its argument as a side note");
    expect(parsed.warnings.filter((w) => w.startsWith("note macros: removed from the"))).toEqual([
      `note macros: removed from the statement of thm:a (main.tex:7-10): \\rj{…} at line 8 was removed as an author's comment (13 characters: "do we need this?"); the statement lost more than half of its text — check that none of it is the paper's (${AUTHOR_NOTES_FILE})`,
      expect.stringMatching(/^note macros: removed from the statement of thm:a \(main\.tex:7-10\): \\todo\{…\} at line 9 was removed as an author's comment \(\d+ characters: "Check the constant in \\eqref\{eq:c\}; I think it is \$2\$, see the argument of Secti…"\); the statement lost more than half/),
      // a statement left with nothing but its label is said to have NO text left
      `note macros: removed from the statement of lem:b (main.tex:11-13): \\old{…} at line 12 was removed as hidden text (50 characters: "For all $n$ the bound holds, and this is the whole statement."); the statement has NO text left — check that none of it is the paper's (${AUTHOR_NOTES_FILE})`,
      expect.stringMatching(/^note macros: removed from the proof of lem:b \(main\.tex:14-16\): \\old\{…\} at line 15 was removed as hidden text \(\d+ characters: "by induction on \$n\$, using the inequality above twice"\); the proof lost more than half of its text/),
    ]);

    const run = await mkdtemp(path.join(os.tmpdir(), "note-macros-run-"));
    tmpDirs.push(run);
    await writeEnvsArtifacts(run, parsed.envs, parsed.flat);
    expect(JSON.parse(await readFile(path.join(run, AUTHOR_NOTES_FILE), "utf8"))).toEqual(rec);
    // the reading is recorded in the run with its version, and replays to the same text and warnings
    const recorded = await recordedNoteMacros(run);
    expect(recorded).toEqual(parsed.envs.note_macros);
    expect(parsed.envs.note_macros!.version).toBe(NOTE_MACROS_VERSION);
    const again = await buildEnvsJson(dir, "main.tex", recorded, run);
    expect(again.flat.text).toBe(parsed.flat.text);
    expect(again.warnings).toEqual(parsed.warnings);
  });

  it("whoever grades a result is shown what was removed from it: the shard's warnings carry the line", async () => {
    const parsed = await buildEnvsJson(await sourceTree(files), "main.tex");
    const env = parsed.envs.envs.find((e) => e.id === "lem:b")!;
    // a node whose id is not its environment's: it is matched by its place in the source
    const core = { statements: [{ id: "lem:renamed", tex_locator: env.lines }, { id: "thm:other", tex_locator: { file: "main.tex", from: 90, to: 91 } }], assumptions: [], definitions: [] } as never;
    const w = { lint: [], parser: parsed.warnings };
    const shown = (ids: string[]): string => warningsSection(w, { ids, places: sourcePlaces(core, parsed.envs, ids) }).join("\n");
    expect(shown(["lem:renamed"])).toContain("removed from the statement of lem:b (main.tex:11-13): \\old{…} at line 12 was removed as hidden text");
    expect(shown(["lem:renamed"])).toContain("removed from the proof of lem:b (main.tex:14-16)");
    expect(shown(["lem:renamed"])).not.toContain("thm:a");
    expect(shown(["thm:other"])).toBe("");
    // the global pass still reads every parser note
    expect(warningsSection(w, { allIds: new Set(["lem:renamed"]) }).join("\n")).toContain("removed from the statement of thm:a");
  });

  it("a replay that gives another text keeps the flat text on file, and says so", async () => {
    const dir = await sourceTree(files);
    const parsed = await buildEnvsJson(dir, "main.tex");
    const run = await mkdtemp(path.join(os.tmpdir(), "note-macros-run-"));
    tmpDirs.push(run);
    // the run on file was read by an older reader: the same table, another text
    const older = { ...parsed.flat, text: parsed.flat.text.replace("Let $x > 0$ .", "Let $x > 0$.") };
    const table = { ...parsed.envs.note_macros!, version: 1 };
    await writeEnvsArtifacts(run, { ...parsed.envs, note_macros: table }, older);
    const notesOnFile = await readFile(path.join(run, AUTHOR_NOTES_FILE), "utf8");
    const again = await buildEnvsJson(dir, "main.tex", await recordedNoteMacros(run), run);
    expect(again.flat.text).toBe(older.text);
    expect(again.envs.note_macros).toEqual(table);
    expect(again.warnings.filter((w) => w.startsWith("note macros:"))).toEqual([
      `note macros: this run was read under an older (version 1; this reader is version ${NOTE_MACROS_VERSION}) reading of its authors' note macros; its ${VERIFY_FILES.flatTex} on file is kept as it is (the transcription refers to it) — the paper is read again only on a cold extraction`,
    ]);
    await writeEnvsArtifacts(run, again.envs, again.flat);
    expect(await readFile(path.join(run, VERIFY_FILES.flatTex), "utf8")).toBe(older.text);
    expect(await readFile(path.join(run, AUTHOR_NOTES_FILE), "utf8")).toBe(notesOnFile);
  });

  it("a run read as written stays read as written: no table on file, the source flattens as before", async () => {
    const dir = await sourceTree(files);
    const asWritten = await buildEnvsJson(dir, "main.tex", false);
    expect(asWritten.envs.note_macros).toBeUndefined();
    expect(asWritten.flat.text).toContain("\\rj{do we need this?}");
    const run = await mkdtemp(path.join(os.tmpdir(), "note-macros-run-"));
    tmpDirs.push(run);
    await writeEnvsArtifacts(run, asWritten.envs, asWritten.flat);
    expect(existsSync(path.join(run, AUTHOR_NOTES_FILE))).toBe(false);
    expect(await recordedNoteMacros(run)).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// the shape that surfaced the defect: a wrapper opened in a proof's first sentence, closed paragraphs later
// ---------------------------------------------------------------------------

const PAPER = {
  "main.tex": [
    "\\documentclass{article}", // 1
    "\\usepackage{amsthm,xcolor}", // 2
    "\\newtheorem{lemma}{Lemma}", // 3
    "\\newcommand{\\lp}[1]{{\\color{black} #1}}", // 4
    "\\newcommand{\\rj}[1]{{\\color{black} #1}}", // 5
    "\\begin{document}", // 6
    "\\begin{lemma}\\label{lem:a}", // 7
    "The bound \\rj{$a \\le b$} holds.", // 8
    "\\end{lemma}", // 9
    "\\begin{proof}", // 10
    "By \\lp{the triangle inequality, $a \\le c$. Next $c \\le d$ by monotonicity.", // 11
    "", // 12
    "The second paragraph shows \\rj{$d \\le e$} holds.", // 13
    "", // 14
    "Finally $e \\le b$.} This proves the claim.", // 15
    "\\end{proof}", // 16
    "\\end{document}", // 17
    "",
  ].join("\n"),
};

describe("a wrapper opened in a proof's first sentence and closed two paragraphs later", () => {
  it("the proof's units are balanced, and so is the proof with its first unit replaced", async () => {
    const dir = await sourceTree(PAPER);
    const off = await buildEnvsJson(dir, "main.tex", false);
    const cut = (p: Awaited<ReturnType<typeof buildEnvsJson>>): string[] =>
      PaperUnits.parse(p.flat.text, p.envs, flatLineStart(p.flat.text, p.flat.lineMap)).file.units.filter((u) => u.part === "proof").map((u) => p.flat.text.slice(u.start, u.end));
    // as written, the first unit opens a group it does not close
    expect(cut(off).some((u) => braceProblem(u) !== null)).toBe(true);

    const on = await buildEnvsJson(dir, "main.tex");
    const texts = cut(on);
    expect(texts).toEqual([
      "By the triangle inequality, $a \\le c$.",
      "Next $c \\le d$ by monotonicity.",
      "The second paragraph shows {$d \\le e$} holds.",
      "Finally $e \\le b$.",
      "This proves the claim.",
    ]);
    expect(on.flat.lineMap).toEqual(off.flat.lineMap);
    expect(on.flat.text.split("\n").length).toBe(off.flat.text.split("\n").length);
    const units = PaperUnits.parse(on.flat.text, on.envs, flatLineStart(on.flat.text, on.flat.lineMap)).file.units.filter((u) => u.part === "proof");
    const replaced = `${on.flat.text.slice(0, units[0]!.start)}By Cauchy--Schwarz, $a \\le c$.${on.flat.text.slice(units[0]!.end)}`;
    expect(braceProblem(replaced.slice(replaced.indexOf("\\begin{proof}"), replaced.indexOf("\\end{proof}")))).toBeNull();
  });

  async function input(): Promise<{ inp: AnnotationInput; source: string; table: NoteMacroTable }> {
    const dir = await sourceTree(PAPER);
    const parsed = await buildEnvsJson(dir, "main.tex");
    const core = {
      qid: "w",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [{ id: "lem:a", kind: "lemma", statement: "The bound {$a \\le b$} holds.", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 7, to: 9, env: "lemma", label: "lem:a" } }],
      target_estimand: "t",
      bibliography: [],
    } as unknown as Core;
    const inp: AnnotationInput = {
      files: PAPER,
      envs: parsed.envs,
      flatText: parsed.flat.text,
      lineMap: parsed.flat.lineMap,
      refs: null,
      transcribed: core,
      core,
      patches: {
        patches: [{
          node: "lem:a",
          corrected_statement: null,
          proof_note: "the first step",
          ops: [
            { op: "replace", unit: "lem:a/proof/1/1", tex: "By Cauchy--Schwarz, $a \\le c$." },
            { op: "replace", unit: "lem:a/proof/3/2", tex: "This proves the lemma." },
          ] as never,
        }],
        unfixable: [],
      },
      paperErrors: { "lem:a": { detail: "the first step is wrong", witness: null } },
      findings: [],
      review: null,
    };
    return { inp, source: PAPER["main.tex"], table: parsed.envs.note_macros! };
  }

  it("the annotated paper keeps the author's wrappers and stays balanced: a mark inside one closes it and opens it again", async () => {
    const { inp, source, table } = await input();
    const read = unwrapSource(source, table, "blank");
    expect(read.length).toBe(source.length);
    const plan = planAnnotations({ ...inp, files: { "main.tex": read } });
    expect(plan.unlocated).toEqual([]);
    const out = applyEditsKeepingNotes(source, plan.edits["main.tex"] ?? [], table);
    expect(out).toContain("\\vsStep{By \\lp{the triangle inequality, $a \\le c$.}} \\vsCorrectedStep{By Cauchy--Schwarz, $a \\le c$.}\\lp{ Next $c \\le d$ by monotonicity.");
    expect(out).toContain("Finally $e \\le b$.} \\vsStep{This proves the claim.} \\vsCorrectedStep{This proves the lemma.}");
    // the rest of the source is the author's, wrappers and all
    expect(out).toContain("The second paragraph shows \\rj{$d \\le e$} holds.");
    expect(out).toContain("The bound \\rj{$a \\le b$} holds.");
    expect(braceProblem(scanTextOf(out))).toBeNull();
    // without the reading, the mark around the first step is widened over the whole wrapper
    const asWritten = applyEdits(source, planAnnotations({ ...inp, envs: (await buildEnvsJson(await sourceTree(PAPER), "main.tex", false)).envs, files: PAPER }).edits["main.tex"] ?? []);
    expect(asWritten).not.toContain("\\vsStep{By \\lp{the triangle inequality, $a \\le c$.}}");
  });

  it("the corrected paper is written from the paper as it was read: no half of a wrapper is left", async () => {
    const { inp, source, table } = await input();
    const read = unwrapSource(source, table, "remove");
    const plan = planAnnotations({ ...inp, files: { "main.tex": read }, pending: null, correctedView: true });
    const out = correctedTex(applyEdits(read, plan.edits["main.tex"] ?? []), { proofEnv: true }).tex;
    expect(out).toContain("By Cauchy--Schwarz, $a \\le c$. Next $c \\le d$ by monotonicity.\n\nThe second paragraph shows {$d \\le e$} holds.\n\nFinally $e \\le b$. This proves the lemma.");
    expect(out).not.toMatch(/\\(?:lp|rj)\{[^#]/);
    expect(out).toContain("\\newcommand{\\lp}[1]{{\\color{black} #1}}");
    expect(braceProblem(out)).toBeNull();
  });
});

describe("edits written into a source that keeps its wrappers", () => {
  const table = detectNoteMacros("\\usepackage{changes}\n\\newcommand{\\lp}[1]{{\\color{black} #1}}\n\\newcommand{\\note}[1]{\\todo{#1}}");
  const at = (src: string, needle: string): number => src.indexOf(needle);
  const edit = (a: number, rank: number, text: string, seq = 0) => ({ at: a, rank, text, seq });

  it("a pair of marks is balanced wherever it falls against the wrappers", () => {
    const src = "A \\lp{B. C \\lp{D. E} F. G} h \\replaced[id=X]{New. One}{old} z";
    for (const [from, to] of [["B", "C"], ["C", "D"], ["E", "h"], ["A", "D"], ["One", "z"], ["New", "One"], ["D", "E"], ["F", "G"]] as const) {
      const out = applyEditsKeepingNotes(src, [edit(at(src, from), 2, "\\vsStep{"), edit(at(src, to) + to.length, 0, "}", 1)], table);
      expect(braceProblem(out), `${from}…${to}: ${out}`).toBeNull();
      // the mark closes at its own brace: what it holds is balanced too
      const open = out.indexOf("\\vsStep{") + "\\vsStep{".length;
      let depth = 1;
      let k = open;
      for (; depth > 0; k += 1) depth += out[k] === "{" ? 1 : out[k] === "}" ? -1 : 0;
      const held = out.slice(open, k - 1);
      expect(braceProblem(held), `${from}…${to}: ${out}`).toBeNull();
      expect(held.replace(/\\[A-Za-z]+(?:\[[^\]]*\])?|[{}]/g, "").replace(/\s+/g, " ")).toContain(`${from}`);
    }
    expect(applyEditsKeepingNotes(src, [edit(at(src, "One"), 1, "\\vsNote{n}")], table)).toContain("\\replaced[id=X]{New. }{}\\vsNote{n}\\replaced[id=X]{One}{old}");
  });

  it("a mark never lands inside the tokens the reading removed, nor inside an author's comment", () => {
    const src = "A \\lp{B. C} d \\note{e f} g \\lp{h} i";
    expect(applyEditsKeepingNotes(src, [edit(at(src, "lp"), 1, "X")], table)).toBe("A X\\lp{B. C} d \\note{e f} g \\lp{h} i");
    expect(applyEditsKeepingNotes(src, [edit(at(src, "f}"), 1, "X")], table)).toBe("A \\lp{B. C} d \\note{e f}X g \\lp{h} i");
    expect(applyEditsKeepingNotes(src, [edit(at(src, "B"), 2, "\\vsStep{"), edit(at(src, "C") + 1, 0, "}")], table)).toBe("A \\vsStep{\\lp{B. C}} d \\note{e f} g \\lp{h} i");
    // a wrapper within a sentence keeps its group: a mark at the macro's name moves before it
    expect(applyEditsKeepingNotes(src, [edit(at(src, "p{h"), 1, "X")], table)).toBe("A \\lp{B. C} d \\note{e f} g X\\lp{h} i");
  });

  it("a wrapper is not closed from inside a group or an environment opened in it", () => {
    const src = "\\lp{A. \\begin{itemize} \\item b c \\end{itemize} \\emph{d e} F. G}";
    expect(applyEditsKeepingNotes(src, [edit(at(src, "c"), 1, "X")], table)).toBe("\\lp{A. \\begin{itemize} \\item b Xc \\end{itemize} \\emph{d e} F. G}");
    expect(applyEditsKeepingNotes(src, [edit(at(src, "e} F"), 1, "X")], table)).toBe("\\lp{A. \\begin{itemize} \\item b c \\end{itemize} \\emph{d Xe} F. G}");
    expect(applyEditsKeepingNotes(src, [edit(at(src, "G"), 1, "X")], table)).toBe("\\lp{A. \\begin{itemize} \\item b c \\end{itemize} \\emph{d e} F. }X\\lp{G}");
  });

  it("the text as read aligns onto the source read with its offsets kept, an emptied line's empty group included", () => {
    const src = "One\n\\note{check}\ntw\\lp{o}. % c\nThree.";
    const scan = scanNotes(scanTextOf(src), table);
    const needle = applyNoteEdits(scanTextOf(src), scan.edits, "remove").replace(/ +$/gm, "");
    expect(needle).toBe("One\n{}\ntw{o}.\nThree.");
    const map = alignToOriginal(unwrapSource(src, table, "blank"), 0, src.length, needle);
    expect(map).not.toBeNull();
    expect(src[map![needle.indexOf("o}")]!]).toBe("o");
    expect(map![needle.length]).toBe(src.length);
    // and onto the source written as read (the corrected paper's)
    expect(alignToOriginal(unwrapSource(src, table, "remove"), 0, src.length, "One\ntw{o}.")).not.toBeNull();
  });

  it("blank mode keeps offsets; remove mode and the scan agree with it on what is read away", () => {
    const src = "A \\lp{B. \\note{c} D} e \\lp{f}";
    const scan = scanNotes(scanTextOf(src), table);
    expect(applyNoteEdits(src, scan.edits, "blank")).toBe("A     B.          D  e    {f}");
    expect(applyNoteEdits(src, scan.edits, "remove")).toBe("A B.  D e {f}");
  });
});
