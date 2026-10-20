import { describe, expect, it } from "vitest";
import { SegmentsSchema, applySegments, truncationGaps, unwrapEnv } from "../../src/verify/segments.js";
import { anchorMatches } from "../../src/verify/ref_core.js";
import type { EnvsJson, TexEnv } from "../../src/verify/types.js";
import type { FlatTex } from "../../src/verify/tex_envs.js";

const LINES = [
  "\\begin{document}", // 1
  "\\textsc{Theorem 1:} \\textit{If $a = 1$ then}", // 2
  "", // 3
  "\\textit{$b = 2$ and $c = 3$.}", // 4
  "", // 5
  "Prose about the result.", // 6
  "\\textbf{Proof of Theorem 1:} Trivial. $Q.E.D.$", // 7
  "\\end{document}", // 8
];
const flat: FlatTex = {
  text: LINES.join("\n"),
  lineMap: LINES.map((_l, i) => ({ file: "main.tex", line: i + 1 })),
  files: ["main.tex"],
  bibFiles: [],
  warnings: [],
};
const env = (partial: Partial<TexEnv> & Pick<TexEnv, "id" | "kind" | "body">): TexEnv => ({
  envName: partial.kind,
  label: null,
  title: null,
  proof: null,
  proofLines: null,
  lines: { file: "main.tex", from: 2, to: 2, env: "prose:theorem", label: null },
  refs: [],
  ...partial,
});
// the parser ended Theorem 1 at the paragraph break on line 2
const ENVS: EnvsJson = {
  main_file: "main.tex",
  files: ["main.tex"],
  newtheorem: { theorem: "theorem" },
  envs: [env({ id: "theorem-1", kind: "theorem", title: "Theorem 1", body: "\\textit{If $a = 1$ then}" })],
  bibliography: [],
} as unknown as EnvsJson;

describe("segments: extend", () => {
  it("extends a truncated statement to the given lines, keeping its parsed start; rejects a range that does not contain the parsed range or adds nothing", () => {
    const seg = SegmentsSchema.parse({ results: [], bindings: [], extend: [{ env: "theorem-1", lines: [2, 4], note: "continues after the break" }] });
    const { envs, violations, notes } = applySegments(seg, ENVS, flat);
    expect(violations).toEqual([]);
    const t = envs.envs.find((e) => e.id === "theorem-1")!;
    expect(t.body).toBe("\\textit{If $a = 1$ then}\n\n\\textit{$b = 2$ and $c = 3$.}");
    expect(t.lines.to).toBe(4);
    expect(notes).toEqual([expect.stringMatching(/theorem-1 extended to flat line 4/)]);
    // a range that does not contain the parsed range, adds nothing, or names no parsed environment
    const bad = SegmentsSchema.parse({ results: [], bindings: [], extend: [{ env: "theorem-1", lines: [3, 4] }, { env: "theorem-1", lines: [2, 2] }, { env: "nope", lines: [2, 4] }] });
    expect(applySegments(bad, ENVS, flat).violations).toEqual([
      expect.stringMatching(/extend\[0\].*must contain the parsed range \[2, 2\]/),
      expect.stringMatching(/extend\[1\].*adds nothing/),
      expect.stringMatching(/extend\[2\].*not the id of a parsed environment/),
    ]);
  });

  it("unwrapEnv yields the body of a range that is exactly one environment", () => {
    expect(unwrapEnv("\\begin{proof}[Proof of X]\nBody.\n\\end{proof}")).toEqual({ body: "Body.", title: "Proof of X" });
    expect(unwrapEnv("plain text")).toEqual({ body: "plain text", title: null });
  });
});

describe("segments: truncationGaps", () => {
  it("names an environment whose missed anchor occurs just after its end, once", () => {
    const violations = [
      '(ref) ass:theorem-1-a.source: anchor `to` "$c = 3$.}" does not occur after `from` "\\textit{If" in the source text.',
      '(ref) ass:theorem-1-b.source: anchor `from` "$b = 2$" does not occur in the source text.',
      '(ref) ass:elsewhere.source: anchor `from` "zeta" does not occur in the source text.',
    ];
    const envOf = (id: string): string | undefined => (id.startsWith("thm:theorem-1") || id.startsWith("ass:theorem-1") ? "theorem-1" : "other-env");
    const gaps = truncationGaps(violations, envOf, ENVS, flat, anchorMatches);
    expect(gaps).toHaveLength(1);
    expect(gaps[0]).toMatch(/^theorem-1 \(Theorem 1, flat lines 2–2\) appears to end early: the phrase "\$c = 3\$\.\}" .* occurs at flat line 4/);
  });
});
