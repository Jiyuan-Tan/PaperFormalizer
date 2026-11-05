import { describe, expect, it } from "vitest";
import { checkDocstringEdit, docstringResidue, lexLeanSegments } from "../../src/formalization/docstring_text_check.js";
import { parseStatementFingerprints, statementChanges } from "../../src/formalization/statement_fingerprints.js";

const kinds = (src: string) => lexLeanSegments(src).filter((s) => s.kind !== "code").map((s) => [s.kind, src.slice(s.start, s.end)]);

describe("lexLeanSegments (comments as Lean's tokenizer reads them)", () => {
  it("nests block comments and tells docstrings from other comments", () => {
    expect(kinds("/-- a /- b -/ c -/ x /- d -/ /-! m -/")).toEqual([
      ["doc", "/-- a /- b -/ c -/"],
      ["comment", "/- d -/"],
      ["comment", "/-! m -/"],
    ]);
  });

  it("inside a comment a quoted -/ still closes it; a line comment hides /-", () => {
    expect(kinds('/-- see "-/" more')).toEqual([["doc", '/-- see "-/']]);
    expect(kinds("x -- not /- a comment\ny")).toEqual([["comment", "-- not /- a comment"]]);
  });

  it("string, character and raw-string literals and «names» hide comment openers; a prime is not a character literal", () => {
    expect(kinds('def s := "/-- no -/" -- yes')).toEqual([["comment", "-- yes"]]);
    expect(kinds("def c := '\"' /- yes -/")).toEqual([["comment", "/- yes -/"]]);
    expect(kinds('def r := r#"a "/-" b"# /- yes -/')).toEqual([["comment", "/- yes -/"]]);
    expect(kinds("theorem «a /- b» : True /- yes -/")).toEqual([["comment", "/- yes -/"]]);
    expect(kinds("theorem h' : x' = y' /-- doc -/")).toEqual([["doc", "/-- doc -/"]]);
  });

  it("an unterminated docstring runs to the end of the file", () => {
    expect(kinds("/-- open\ntheorem foo : True := trivial")).toEqual([["doc", "/-- open\ntheorem foo : True := trivial"]]);
  });
});

describe("docstringResidue", () => {
  it("drops docstrings on lines of their own, the blanks after a docstring, trailing blanks and empty lines", () => {
    const a = "theorem foo : True := trivial\n\ntheorem bar : True := trivial\n";
    const b = "/-- Foo. -/\ntheorem foo : True := trivial  \n\n  /-- Bar,\n  two lines. -/\ntheorem bar : True := trivial\n";
    expect(docstringResidue(b).text).toBe(docstringResidue(a).text);
    expect(docstringResidue(b).docs.map((d) => d.body)).toEqual([" Foo. ", " Bar,\n  two lines. "]);
  });
});

describe("lexLeanSegments: where Lean and a naive scanner part", () => {
  it("`/-/-` opens one level (Lean skips the character after `/-`)", () => {
    expect(kinds('/-/- banner -/ def s := "-/" /-- d -/')).toEqual([["comment", "/-/- banner -/"], ["doc", "/-- d -/"]]);
  });

  it("a number then a character literal; λ before a quote is no identifier", () => {
    expect(kinds("def c := 2'\"' /- yes -/")).toEqual([["comment", "/- yes -/"]]);
    expect(kinds("def f := λ'\"' /- yes -/")).toEqual([["comment", "/- yes -/"]]);
    expect(kinds("def c := '\n' /- yes -/".replace("\\n", "\n"))).toEqual([["comment", "/- yes -/"]]);
  });
});

const BEFORE = [
  "theorem foo (x : Nat) (h : 0 < x) : 0 < x := by",
  "  exact h",
  "",
  "/-- Old doc. -/",
  "-- @node: bar",
  "theorem bar : True := trivial",
  "",
].join("\n");
const DECL_LINES = [1, 4];

describe("checkDocstringEdit", () => {
  it("accepts new and replaced docstrings on declarations and reads each one back by its declaration's line", () => {
    const after = BEFORE
      .replace("theorem foo", "/-- New [foo](goal). -/\ntheorem foo")
      .replace("/-- Old doc. -/", "/-- Replaced. -/");
    const r = checkDocstringEdit(BEFORE, after, DECL_LINES);
    expect(r.status).toBe("ok");
    if (r.status !== "ok") return;
    expect(r.declAt(1)).toEqual({ doc: " New [foo](goal). ", hadDoc: false, line: 2 });
    expect(r.declAt(4)).toEqual({ doc: " Replaced. ", hadDoc: true, line: 7 });
  });

  it("an edit outside docstrings is a code change, a comment included", () => {
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("exact h", "exact h.le"), DECL_LINES)).toEqual({ status: "code-changed", line: 2 });
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("-- @node: bar\n", ""), DECL_LINES).status).toBe("code-changed");
  });

  it("a docstring that swallows code is caught — an unclosed one, or one closed early by a quoted -/", () => {
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("theorem foo", "/-- Unclosed.\ntheorem foo"), DECL_LINES).status).toBe("code-changed");
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("theorem foo", '/-- Ends "-/" early. -/\ntheorem foo'), DECL_LINES).status).toBe("code-changed");
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("theorem bar : True := trivial", "/-- d -/ -/\ntheorem bar : True := trivial"), DECL_LINES).status).toBe("code-changed");
  });

  it("a docstring off the declarations' slots, or two in one, is not vouched for", () => {
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("  exact h", "  /-- d -/\n  exact h"), DECL_LINES)).toEqual({ status: "unplaced", line: 2 });
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("/-- Old doc. -/", "/-- One. -/\n/-- Two. -/"), DECL_LINES).status).toBe("unplaced");
  });

  it("columns: a declaration's head line may shift with an inline docstring; any other column may not", () => {
    // an inline docstring before `theorem`, or an inline one moved onto its own line
    expect(checkDocstringEdit(BEFORE, BEFORE.replace("theorem foo", "/-- d -/ theorem foo"), DECL_LINES).status).toBe("ok");
    expect(checkDocstringEdit(BEFORE.replace("/-- Old doc. -/\n-- @node: bar\n", "-- @node: bar\n/-- Old doc. -/ "), BEFORE, [5]).status).toBe("ok");
    const s = "structure S where\n  x : Nat\n";
    expect(checkDocstringEdit(s, s.replace("  x", "  /-- the x field -/ x"), [1, 2]).status).toBe("ok");
    // a field moved to column 0 changes the text; a column inside a proof moved by a docstring is refused
    const f = "structure S where\n  /-- x -/ x : Nat\n";
    expect(checkDocstringEdit(f, f.replace("  /-- x -/ x", "/-- x -/\nx"), [1]).status).toBe("code-changed");
    const p = "theorem foo : True := by\n  /- c -/ trivial\n";
    expect(checkDocstringEdit(p, p.replace("/- c -/", "/- comment -/"), [1]).status).toBe("code-changed");
  });

  it("a declaration behind a one-line scoping prefix takes its docstring after the prefix, not before", () => {
    const s = "open Real in theorem foo : True := trivial\n";
    expect(checkDocstringEdit(s, `/-- d -/\n${s}`, [1]).status).toBe("unplaced");
    expect(checkDocstringEdit(s, s.replace("in theorem", "in /-- d -/ theorem"), [1]).status).toBe("ok");
  });

  it("only blank lines moved: no change at all", () => {
    const r = checkDocstringEdit(BEFORE, BEFORE.replace("\n\n/--", "\n\n\n/--"), DECL_LINES);
    expect(r.status).toBe("ok");
  });
});

describe("statementChanges (the docstring pass leaves every statement as it was)", () => {
  const scan = (decls: [string, string, string?][]) =>
    parseStatementFingerprints(JSON.stringify({ declarations: decls.map(([name, closure_hash, file]) => ({ name, file: file ?? "Papers/T/A.lean", closure_hash })) }), "Papers/T")!;
  it("names a moved fingerprint, a declaration gone and one new; nothing when all match", () => {
    const before = scan([["Papers.T.foo", "1"], ["Papers.T.bar", "2"]]);
    expect(statementChanges(before, scan([["Papers.T.bar", "2"], ["Papers.T.foo", "1"]]))).toEqual([]);
    expect(statementChanges(before, scan([["Papers.T.foo", "9"], ["Papers.T.baz", "3"]]))).toEqual([
      "Papers.T.foo (Papers/T/A.lean) states something else",
      "Papers.T.bar (Papers/T/A.lean) is gone",
      "Papers.T.baz (Papers/T/A.lean) is new",
    ]);
  });

  it("reads the run's own declarations (its root module included) only: another run's promotion meanwhile is not this pass's change", () => {
    expect(statementChanges(scan([["Papers.T", "1", "Papers/T.lean"]]), scan([["Papers.T", "2", "Papers/T.lean"]]))).toEqual([
      "Papers.T (Papers/T.lean) states something else",
    ]);
    const before = scan([["Papers.T.foo", "1"], ["Toolkit.lemma", "5", "Toolkit/X.lean"]]);
    expect(statementChanges(before, scan([["Papers.T.foo", "1"], ["Toolkit.lemma", "6", "Toolkit/X.lean"], ["Toolkit.new", "7", "Toolkit/Y.lean"]]))).toEqual([]);
  });
});
