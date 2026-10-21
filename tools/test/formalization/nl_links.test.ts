import { existsSync, mkdtempSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  batchByRows, checkReply, conjuncts, declSource, flatLeanRows, itemsBlock, leanStatementView, linkItems, linkMetrics, segmentShown, segmentStatement,
  sharedLimit, sharedRows, statementRows, storedResult, viewRows, type LinkItem,
} from "../../src/formalization/nl_links.js";
import { leanScopes } from "../../src/formalization/lean_rows.js";

/** The rows F5 asks of a statement that names no other (`statementRows` with nothing to open). */
const leanRows = (source: string) => { const view = leanStatementView(source); return view ? viewRows(view) : flatLeanRows(source); };

// Li & Ding (2017), Theorem 1, as the graph stores it (label, display, trailing hypotheses note).
const THM1 = String.raw`\label{thm:CLThajek}
Let $\bar{y}_{\text{S}}$ be the average of a simple random sample of size $n$ from a finite population $\Pi_N = \{ y_{N1}, \ldots, y_{NN} \}$.

As $N\rightarrow \infty$, if

\begin{align}
\label{eq:condi_CLThajek}
 \frac{1}{\min(n, N-n)}\cdot\frac{  m_N }{ v_N } \rightarrow 0,
\end{align}
then $(\ybars - \bar{y}_N)/  \sqrt{ \Var(\ybars)  }   \converged \mathcal{N}(0,1)$, recalling that $v_N$ and $m_N$ are defined in \eqref{eq:v_N} and \eqref{eq:m_N}. [Hypotheses: ass:clthajek-regularity]`;

/** The segments of `raw` as shown — after checking that they tile it in order and never cut inline math. */
function shown(raw: string): string[] {
  const segs = segmentStatement(raw);
  for (let k = 1; k < segs.length; k++) expect(segs[k].start, raw).toBe(segs[k - 1].end);
  for (const s of segs) {
    expect(s.text).toBe(raw.slice(s.start, s.end));
    // a segment holds whole inline formulas: its `$` come in pairs
    expect((s.text.replace(/\\[\s\S]/g, "").replace(/\$\$/g, "").match(/\$/g) ?? []).length % 2, s.text).toBe(0);
  }
  expect(segs.map((s) => s.id)).toEqual(segs.map((_, k) => `s${k + 1}`));
  return segs.map((s) => segmentShown(s.text));
}

describe("segmentStatement (paper side, deterministic)", () => {
  // The finding: `$\\$` (a formula of one line break) closed at the next formula's `$`, cutting inside it.
  it("reads `$\\\\$` as one formula", () => {
    const raw = String.raw`\end{equation}
$\\$
where $C = \frac{a}{b}.$ More text here.`;
    expect(shown(raw).length).toBeGreaterThan(0);
  });
  const segs = segmentStatement(THM1);
  it("tiles the statement in order, keeps a display whole (with its 'if'), and cuts at sentences and clause commas", () => {
    expect(segs.map((s) => segmentShown(s.text).slice(0, 12))).toEqual(["Let $\\bar{y}", "As $N\\righta", "if \\begin{al", "then $(\\ybar"]);
    const display = segs[2].text;
    expect(display).toContain("\\begin{align}");
    expect(display).toContain("\\end{align}");
    for (let k = 1; k < segs.length; k++) expect(segs[k].start).toBe(segs[k - 1].end);
    // a display that is one condition is one segment, and no part of anything
    expect(segs.every((s) => s.display === undefined)).toBe(true);
  });
  // The finding: "i.i.d.", "e.g.", "Fig. 3" each ended a segment.
  it("a period ends a segment only where it ends a sentence", () => {
    const shown = (tex: string) => segmentStatement(tex).map((s) => segmentShown(s.text));
    const whole = String.raw`Let $X_1, \dots, X_n$ be i.i.d. Gaussian vectors, e.g. standard ones, i.e. with identity covariance (cf. Lemma 2 and Eq. (3), resp. Fig. 4) so that $\bar X_n \to \mu$ a.s. $P$-almost everywhere w.r.t. the product law.`;
    expect(shown(whole)).toEqual([whole]);
    expect(shown(String.raw`Suppose $X$ and $Y$ are i.i.d. Then $E[X] = E[Y]$. Moreover the variance is finite; it equals $\sigma^2$.`)).toEqual([
      String.raw`Suppose $X$ and $Y$ are i.i.d. Then $E[X] = E[Y]$.`, "Moreover the variance is finite;", String.raw`it equals $\sigma^2$.`,
    ]);
    expect(shown(String.raw`The bound holds for $n \ge 2$. $T_n$ is then tight. (ii) The limit is unique.`)).toEqual([String.raw`The bound holds for $n \ge 2$.`, "$T_n$ is then tight.", "(ii) The limit is unique."]);
    // the segments still tile the text, and no cut falls inside math
    const segs = segmentStatement(String.raw`Assume $a < b. c$ holds, i.e. $a$ is small. Then $b > 0$.`);
    expect(segs.map((s) => s.text).join("")).toBe(String.raw`Assume $a < b. c$ holds, i.e. $a$ is small. Then $b > 0$.`);
    expect(segs.map((s) => segmentShown(s.text))).toEqual([String.raw`Assume $a < b. c$ holds, i.e. $a$ is small.`, "Then $b > 0$."]);
  });
  it("drops the label-only head and the graph's hypotheses note; never cuts inside inline math", () => {
    expect(segs.some((s) => segmentShown(s.text) === "")).toBe(false);
    expect(segs.map((s) => s.text).join("")).not.toContain("[Hypotheses:");
    expect(shown("If $a, if b$ holds, then $c$.")).toEqual(["If $a, if b$ holds,", "then $c$."]);
  });
  it("cuts a list at each item, the list's own markup staying with its first and last item", () => {
    expect(shown(String.raw`Suppose the following hold. \begin{enumerate} \item $|K(u)|\leq \bar{K}$ \item $f$ is bounded. \item the conditions of Lemma~\ref{l} hold. \end{enumerate} Then $x=y$.`)).toEqual([
      "Suppose the following hold.", String.raw`\begin{enumerate} \item $|K(u)|\leq \bar{K}$`, String.raw`\item $f$ is bounded.`, String.raw`\item the conditions of Lemma~\ref{l} hold. \end{enumerate}`, "Then $x=y$.",
    ]);
    // any environment whose body opens with an item is a list (the paper's own included)
    expect(shown(String.raw`Assume: \begin{conditions}[(i)] \item $a<b$; \item $c$ is finite \end{conditions} then $d$.`)).toEqual([
      String.raw`Assume: \begin{conditions}[(i)] \item $a<b$;`, String.raw`\item $c$ is finite \end{conditions}`, "then $d$.",
    ]);
  });
  // After a `$$ … $$` display the inline matcher paired the display's last `$` with the next inline
  // `$`: math and prose swapped up to the next display, cuts were missed and fell inside math.
  it("blanks the displays before reading inline math: `$$ … $$` and `\\[ … \\]` cut alike, never inside `$…$`", () => {
    const tail = String.raw` Then $a>0$. Moreover it holds. \begin{enumerate} \item First $b<1$. \item Second thing. \end{enumerate} Then $c$ holds.`;
    const dollars = shown(String.raw`Suppose the following. $$ x = 1 $$` + tail);
    expect(dollars).toEqual(shown(String.raw`Suppose the following. \[ x = 1 \]` + tail).map((s) => s.replace(String.raw`\[ x = 1 \]`, () => "$$ x = 1 $$")));
    expect(dollars).toEqual(["Suppose the following.", "$$ x = 1 $$", "Then $a>0$.", "Moreover it holds.", String.raw`\begin{enumerate} \item First $b<1$.`, String.raw`\item Second thing. \end{enumerate}`, "Then $c$ holds."]);
    expect(shown(String.raw`Let $$ x = 1 $$ and $a>0$ hold. Then $u < v. Also w$ is fine.`)).toEqual(["Let $$ x = 1 $$", "and $a>0$ hold.", "Then $u < v. Also w$ is fine."]);
    expect(shown(String.raw`Let $$ x = 1 $$ and assume $a>0$. If so, then $b>0$ and $c>0$, where $d$ is given.`)).toEqual(["Let $$ x = 1 $$", "and assume $a>0$.", "If so, then $b>0$", "and $c>0$,", "where $d$ is given."]);
  });
  it("cuts a list of three or more inline conditions at each; two joined by a comma alone stay one", () => {
    expect(shown(String.raw`Suppose $a>0$, $b<1$, and $c=2$. Then $d$.`)).toEqual(["Suppose $a>0$,", "$b<1$,", "and $c=2$.", "Then $d$."]);
    expect(shown(String.raw`Suppose Assumptions 1--3 hold, $x>0$, $y>0$ and $z>0$.`)).toEqual(["Suppose Assumptions 1--3 hold, $x>0$,", "$y>0$", "and $z>0$."]);
    expect(shown(String.raw`If for some $\delta>0$, $E|X|^{2+\delta}<\infty$, then $Y$.`)).toEqual([String.raw`If for some $\delta>0$, $E|X|^{2+\delta}<\infty$,`, "then $Y$."]);
  });
  it("never leaves a segment with no word and no math: an `\\emph{…}` around the statement closes with its last piece", () => {
    for (const st of [String.raw`\emph{Suppose $a>0$. Then $b>0$.}`, String.raw`\emph{Suppose $a>0$. Then $b>0$.
}`, String.raw`{\em Suppose $a>0$. Then $b>0$. }`]) {
      const segs = shown(st);
      expect(segs, st).toHaveLength(2);
      for (const s of segs) expect(/[\p{L}\p{N}$]/u.test(s.replace(/\\[A-Za-z]+/g, "")), s).toBe(true);
    }
  });
  it("on every statement F5 links in the toolkit's runs: the segments tile it, and no cut falls inside inline math", () => {
    const toolkit = process.env.PAPERFORMALIZER_TEST_TOOLKIT ?? "";
    const runs = toolkit && existsSync(path.join(toolkit, "runs")) ? readdirSync(path.join(toolkit, "runs")) : [];
    let n = 0;
    for (const slug of runs) {
      const file = path.join(toolkit, "runs", slug, "formalization", "graph.json");
      const alt = path.join(toolkit, "runs", slug, "graph.json");
      const g = existsSync(file) ? file : existsSync(alt) ? alt : null;
      if (!g) continue;
      for (const node of (JSON.parse(readFileSync(g, "utf8")).nodes ?? []) as Array<{ nl?: { statement?: string } }>) {
        const st = node.nl?.statement;
        if (!st?.trim()) continue;
        // `shown` checks the tiling and that every segment holds its inline `$` in pairs
        shown(st.replace(/\s*\[Hypotheses:[^\]]*\]\s*$/, ""));
        n++;
      }
    }
    if (runs.length) expect(n).toBeGreaterThan(0);
  });
  it("cuts before a repeated ', that' — but not at 'that is'", () => {
    expect(shown(String.raw`Suppose that $S_2$ is a simple random sample from $S_1$, that $n_2/n_1\rightarrow\rho$, and that for some $\delta>0$, $E|\psi|^{2+\delta}<\infty$.`)).toEqual([
      "Suppose that $S_2$ is a simple random sample from $S_1$,", String.raw`that $n_2/n_1\rightarrow\rho$,`, String.raw`and that for some $\delta>0$, $E|\psi|^{2+\delta}<\infty$.`,
    ]);
    expect(shown("The map is smooth, that is, $C^1$.")).toEqual(["The map is smooth, that is, $C^1$."]);
  });
  it("cuts at the markers of an inline enumeration when they form a run", () => {
    expect(shown(String.raw`Then: $(a)$ When panel data are available, $\tau^{p}=\tau$; $\left( b\right) $ otherwise $\tau^{rc}=\tau$, and (c) both are finite.`)).toEqual([
      String.raw`Then: $(a)$ When panel data are available, $\tau^{p}=\tau$;`, String.raw`$\left( b\right) $ otherwise $\tau^{rc}=\tau$,`, "and (c) both are finite.",
    ]);
    expect(shown("Assume (i) $f$ is bounded (ii) $g$ is measurable (iii) $h$ is finite.")).toEqual(["Assume (i) $f$ is bounded", "(ii) $g$ is measurable", "(iii) $h$ is finite."]);
    // one marker is no run; a function's argument and an equation's number in running text are no markers
    expect(shown("By (a) the bound holds for $f(a)$ and $g(b)$.")).toEqual(["By (a) the bound holds for $f(a)$ and $g(b)$."]);
    expect(shown("Combining (1) with (2) gives the claim.")).toEqual(["Combining (1) with (2) gives the claim."]);
    expect(shown("The estimator satisfies: (1) it is unbiased, (2) it is consistent.")).toEqual(["The estimator satisfies:", "(1) it is unbiased,", "(2) it is consistent."]);
  });
  it("cuts before the 'and' between two inline relations, and only there", () => {
    expect(shown(String.raw`Assume $E[Y^2]<\infty$ and $\|\alpha_0\|_\infty\leq\bar\alpha$, and $n\to\infty$. Then $A$ holds and $B$ holds.`)).toEqual([
      String.raw`Assume $E[Y^2]<\infty$`, String.raw`and $\|\alpha_0\|_\infty\leq\bar\alpha$,`, String.raw`and $n\to\infty$.`, "Then $A$ holds and $B$ holds.",
    ]);
    expect(shown("Let $x$ and $y$ be real and $x<y$.")).toEqual(["Let $x$ and $y$ be real and $x<y$."]);
  });
  it("cuts a display that holds several conditions into one part each, named after its first part", () => {
    const raw = String.raw`Suppose \[ E[\{Y-\gamma_0(W)\}^2 \mid W ]\leq \bar{\sigma}^2,\quad \|\alpha_0^{\min}\|_{\infty}\leq\bar{\alpha},\quad \|\hat\alpha\|_\infty\leq\bar\alpha'. \] Then $x=y$.`;
    expect(shown(raw)).toEqual([
      String.raw`Suppose \[ E[\{Y-\gamma_0(W)\}^2 \mid W ]\leq \bar{\sigma}^2,\quad`, String.raw`\|\alpha_0^{\min}\|_{\infty}\leq\bar{\alpha},\quad`, String.raw`\|\hat\alpha\|_\infty\leq\bar\alpha'. \]`, "Then $x=y$.",
    ]);
    expect(segmentStatement(raw).map((s) => s.display)).toEqual(["s1", "s1", "s1", undefined]);
    // rows of an aligned display, `\qquad`, and `\text{and}` between conditions (which stays with the one before)
    expect(shown(String.raw`\begin{align} a &\leq b \\ c &= d \end{align}`)).toEqual([String.raw`\begin{align} a &\leq b \\`, String.raw`c &= d \end{align}`]);
    expect(shown(String.raw`$$ a<b \qquad\text{and}\qquad c<d $$`)).toEqual([String.raw`$$ a<b \qquad\text{and}\qquad`, "c<d $$"]);
    // a list of subjects after a space goes whole with its relation; a value list after a comma alone stays behind
    expect(shown(String.raw`\[ a\lesssim b<\infty,\qquad c, d\lesssim e. \]`)).toEqual([String.raw`\[ a\lesssim b<\infty,\qquad`, String.raw`c, d\lesssim e. \]`]);
    expect(shown(String.raw`\[ a\leq b \quad c, d, e\leq f \]`)).toEqual([String.raw`\[ a\leq b \quad`, String.raw`c, d, e\leq f \]`]);
    expect(shown(String.raw`\[ x\in\{1, 2\}, 3, y\leq z \]`)).toEqual([String.raw`\[ x\in\{1, 2\}, 3,`, String.raw`y\leq z \]`]);
  });
  it("leaves a display that is one statement whole: a continued equation, a comma inside brackets, a case split", () => {
    for (const one of [
      String.raw`\begin{align} \tau &= E[Y(1)] - E[Y(0)] \\ &= \mu_1 - \mu_0 \\ &\leq C \end{align}`,
      String.raw`\[ f(x, y) = \max\{x, y\}, \quad x \in \mathbb{R} \]`.replace(String.raw`, \quad x \in \mathbb{R}`, ""),
      String.raw`\[ g(x) = \begin{cases} 1, & x \geq 0 \\ 0, & x < 0 \end{cases} \]`,
      String.raw`\[ \hat\tau = \frac{1}{n}\sum_{i=1}^n \left( Y_i - \hat\mu(X_i), \hat\pi(X_i) \right) \]`,
    ]) expect(shown(one), one).toHaveLength(1);
  });
});

describe("the rows of a statement (Lean side, deterministic)", () => {
  const src = `/-- doc -/
theorem srs_clt (N n : ℕ → ℕ) [∀ a, Nonempty (Fin (N a))]
    (y : ∀ a, Fin (N a) → ℝ) -- the population
    (hN : Tendsto N atTop atTop) (hreg : HajekRegularity N n y) :
    P N ∧ (Q n ∧ R) ∧ S y := by
  simp [foo]`;
  it("gives the rows of the nested view: one per binder group (instances marked), then every clause at every depth", () => {
    const rows = leanRows(src)!;
    expect(rows.map((r) => `${r.kind}:${r.id}:${r.names}`)).toEqual([
      "binder:r1:N n", "instance:r2:", "binder:r3:y", "binder:r4:hN", "binder:r5:hreg",
      "conclusion:r6:", "conclusion:r7:", "conclusion:r8:", "conclusion:r9:",
    ]);
    expect(rows[2].lean).toBe("∀ a, Fin (N a) → ℝ");
    // the bracketed conjunct is cut again; the card that only branches has no row of its own
    expect(rows.slice(5).map((r) => r.lean)).toEqual(["P N", "Q n", "R", "S y"]);
    expect(leanRows("theorem t (x : ℕ) : x = x := rfl")!.at(-1)).toMatchObject({ id: "r2", kind: "conclusion", lean: "x = x" });
  });
  it("a clause that carries its own quantifiers and hypotheses gives one row for each, then what it concludes", () => {
    const rows = leanRows("theorem t (P : Pop) : (A P → B P (f x) → C P ∧ D P) ∧ (∀ E : Ex P, (G E) → ∃ c : ℝ, 0 < c ∧ H E c) ∧ K P := by\n  sorry")!;
    expect(rows.map((r) => [r.id, r.kind, r.lean])).toEqual([
      ["r1", "binder", "Pop"],
      ["r2", "premise", "A P"], ["r3", "premise", "B P (f x)"], ["r4", "conclusion", "C P"], ["r5", "conclusion", "D P"],
      // a bracketed premise is a premise, not a binder; the `∃` its parts share is the clause's own row
      ["r6", "premise", "∀ E : Ex P"], ["r7", "premise", "(G E)"], ["r8", "conclusion", "∃ c : ℝ,"], ["r9", "conclusion", "0 < c"], ["r10", "conclusion", "H E c"],
      ["r11", "conclusion", "K P"],
    ]);
    expect(leanRows("theorem u : A → B := by sorry")!.map((r) => `${r.kind}:${r.id}`)).toEqual(["premise:r1", "conclusion:r2"]);
    expect(leanRows("def f : ℕ := 0")).toBeNull();
  });
  it("the links and the page take their ids from one view", () => {
    const view = leanStatementView(src)!;
    const ids: string[] = [];
    const walk = (c: (typeof view.conclusions)[number]) => { c.hyps.forEach((h) => ids.push(h.id!)); if (c.id) ids.push(c.id); (c.sub ?? []).forEach(walk); };
    view.sharedHyps.forEach((h) => ids.push(h.id!));
    view.conclusions.forEach(walk);
    expect(ids).toEqual(viewRows(view).map((r) => r.id));
    // reading the rows does not renumber them
    expect(viewRows(view)).toEqual(viewRows(view));
  });
  it("the flat cut (links written before the nested view; a statement the view cannot structure)", () => {
    const rows = flatLeanRows(src)!;
    expect(rows.map((r) => `${r.kind}:${r.id}`)).toEqual([
      "binder:N n", "instance:inst1", "binder:y", "binder:hN", "binder:hreg", "conclusion:⊢1", "conclusion:⊢2", "conclusion:⊢3",
    ]);
    expect(rows.at(-2)!.lean).toBe("(Q n ∧ R)");
    expect(flatLeanRows("theorem t (x : ℕ) : x = x := rfl")!.at(-1)).toMatchObject({ id: "⊢", lean: "x = x" });
    const chained = flatLeanRows("theorem t (P : Pop) : (A P → B P (f x) → C P ∧ D P) ∧ (∀ E : Ex P, G E → H E) ∧ K P := by\n  sorry")!;
    expect(chained.map((r) => [r.id, r.kind, r.lean])).toEqual([
      ["P", "binder", "Pop"],
      ["⊢1.h1", "premise", "A P"], ["⊢1.h2", "premise", "B P (f x)"], ["⊢1.1", "conclusion", "C P"], ["⊢1.2", "conclusion", "D P"],
      ["⊢2", "conclusion", "(∀ E : Ex P, G E → H E)"],
      ["⊢3", "conclusion", "K P"],
    ]);
    expect(flatLeanRows("theorem u : A → B := by sorry")!.map((r) => r.id)).toEqual(["⊢.h1", "⊢"]);
    // a binder the view cannot parse: the flat cut still gives rows
    expect(leanStatementView("theorem v () (x : ℕ) : x = x := rfl")).toBeNull();
    expect(leanRows("theorem v () (x : ℕ) : x = x := rfl")!.map((r) => r.id)).toEqual(["x", "⊢"]);
    expect(conjuncts("a ∧ (b ∧ c) ∧ d")).toEqual(["a", "(b ∧ c)", "d"]);
  });
  it("declSource finds a theorem by its leaf name and stops at the next declaration", () => {
    const file = `namespace X\n\n/-- a -/\ntheorem other : True := trivial\n\ntheorem srs_clt (x : ℕ) : x = x := rfl\n\ntheorem after : True := trivial\n`;
    const s = declSource(file, "Papers.X.srs_clt")!;
    expect(s.startsWith("theorem srs_clt")).toBe(true);
    expect(s).not.toContain("after");
  });
});

// The finding this guards: a theorem stated through `type_of% @name` was offered to the model as
// the one row `type_of% @name`, while the page drew the named theorem's rows with no id.
describe("statementRows: a clause written `type_of% @name` is asked as that theorem's rows", () => {
  const root = mkdtempSync(path.join(tmpdir(), "tc-nllinks-"));
  const dir = path.join(root, "Papers", "Demo");
  mkdirSync(dir, { recursive: true });
  writeFileSync(path.join(dir, "Parts.lean"), [
    "namespace Papers.Demo", "",
    "theorem ral_part {n : ℕ} (hn : 0 < n) : A n ∧ (∀ m, m < n → B m) := by", "  sorry", "",
    "theorem matching_part (k : ℕ) : C k := by", "  sorry", "",
    "end Papers.Demo", "",
  ].join("\n"));
  const BOOT = "theorem boot : (type_of% @ral_part) ∧ (type_of% @matching_part) := by\n  sorry";
  writeFileSync(path.join(dir, "T.lean"), `import Papers.Demo.Parts\n\nnamespace Papers.Demo\n\n${BOOT}\n\nend Papers.Demo\n`);
  const lean = leanScopes({ toolkitRoot: root, leanDir: dir, read: async (abs) => { try { return readFileSync(abs, "utf8"); } catch { return null; } } });

  it("offers every row of the named statements, keyed under the clause, and none for the clause's own line", async () => {
    const cut = (await statementRows(BOOT, { file: "T.lean", decl: "Papers.Demo.boot", lean }))!;
    expect(cut.rows.map((r) => `${r.id} ${r.kind} ${r.names ? `${r.names} : ` : ""}${r.lean}`)).toEqual([
      "r1/r1 binder n : ℕ", "r1/r2 binder hn : 0 < n", "r1/r3 conclusion A n", "r1/r4 premise ∀ m", "r1/r5 premise m < n", "r1/r6 conclusion B m",
      "r2/r1 binder k : ℕ", "r2/r2 conclusion C k",
    ]);
    // the prompt the step sends: these rows, by these ids
    const block = itemsBlock([{ obj_id: "T-1", node: "thm:boot", decl: "Papers.Demo.boot", key: cut.key, segments: segmentStatement("Under the conditions of both, $A$ holds."), rows: cut.rows }]);
    expect(block).toContain("  r1/r5: m < n");
    expect(block).toContain("  r2/r2: C k");
    expect(block).not.toContain("type_of%");
  });
  it("links are written under a key that takes the named statements in: any of them edited, and it changes", async () => {
    const at = { file: "T.lean", decl: "Papers.Demo.boot", lean };
    const key = (await statementRows(BOOT, at))!.key;
    expect((await statementRows(BOOT, at))!.key).toBe(key);
    expect((await statementRows(BOOT))!.rows.map((r) => r.lean)).toEqual(["type_of% @ral_part", "type_of% @matching_part"]);
    expect((await statementRows(BOOT))!.key).not.toBe(key);
    const edited = mkdtempSync(path.join(tmpdir(), "tc-nllinks-"));
    const dir2 = path.join(edited, "Papers", "Demo");
    mkdirSync(dir2, { recursive: true });
    writeFileSync(path.join(dir2, "Parts.lean"), readFileSync(path.join(dir, "Parts.lean"), "utf8").replace("C k", "C (k + 1)"));
    writeFileSync(path.join(dir2, "T.lean"), readFileSync(path.join(dir, "T.lean"), "utf8"));
    const lean2 = leanScopes({ toolkitRoot: edited, leanDir: dir2, read: async (abs) => { try { return readFileSync(abs, "utf8"); } catch { return null; } } });
    expect((await statementRows(BOOT, { ...at, lean: lean2 }))!.key).not.toBe(key);
  });
});

const item: LinkItem = {
  obj_id: "T-1", node: "thm:a", decl: "X.a", key: "k",
  segments: [{ id: "s1", text: "Let x.", start: 0, end: 6 }, { id: "s2", text: "then y.", start: 6, end: 13 }],
  rows: [
    { id: "x", kind: "binder", names: "x", lean: "ℕ" },
    { id: "inst1", kind: "instance", names: "", lean: "Fintype α" },
    { id: "⊢", kind: "conclusion", names: "", lean: "y" },
  ],
};
/** A result of `n` rows `r1…rn` over `m` segments `s1…sm`. */
const wide = (obj_id: string, n: number, m = 6): LinkItem => ({
  obj_id, node: obj_id, decl: obj_id, key: "k",
  segments: Array.from({ length: m }, (_, k) => ({ id: `s${k + 1}`, text: `S${k + 1}.`, start: 3 * k, end: 3 * k + 3 })),
  rows: Array.from({ length: n }, (_, k) => ({ id: `r${k + 1}`, kind: "premise" as const, names: "", lean: `P ${k + 1}` })),
});
const answer = (it: LinkItem, segments: (row: string, k: number) => string[]) =>
  ({ obj_id: it.obj_id, rows: it.rows.filter((r) => r.kind !== "instance").map((r, k) => ({ row: r.id, segments: segments(r.id, k), unstated: segments(r.id, k).length === 0 })), uncovered: [] });

describe("checkReply (the closed world)", () => {
  it("accepts a total answer by id (instance rows are not asked)", () => {
    const reply = { results: [{ obj_id: "T-1", rows: [{ row: "x", segments: ["s1"], unstated: false }, { row: "⊢", segments: ["s2"], unstated: false }], uncovered: [] }] };
    const r = checkReply([item], reply);
    expect(r.problems).toEqual([]);
    expect(r.ok.get("T-1")!.rows.map((x) => x.row)).toEqual(["x", "⊢"]);
    expect(itemsBlock([item])).not.toContain("inst1");
  });
  it("drops an item with a skipped row, an unknown id, or unstated contradicting its segments", () => {
    const skipped = checkReply([item], { results: [{ obj_id: "T-1", rows: [{ row: "x", segments: ["s1"], unstated: false }], uncovered: [] }] });
    expect(skipped.problems[0]).toContain("rows not answered: ⊢");
    const unknown = checkReply([item], { results: [{ obj_id: "T-1", rows: [{ row: "x", segments: ["s9"], unstated: false }, { row: "⊢", segments: ["s2"], unstated: false }], uncovered: ["s7"] }] });
    expect(unknown.problems[0]).toContain("unknown segment s9");
    expect(unknown.problems[0]).toContain("uncovered segment s7");
    const contradiction = checkReply([item], { results: [{ obj_id: "T-1", rows: [{ row: "x", segments: ["s1"], unstated: true }, { row: "⊢", segments: [], unstated: true }], uncovered: [] }] });
    expect(contradiction.problems[0]).toContain("row x");
    expect(contradiction.ok.size).toBe(0);
    expect(checkReply([item], "not json").problems).toEqual(["T-1: no answer"]);
  });
  // The finding this guards: every row answered with every segment passed the check — and then
  // every row answered with the same TWO segments did (645 rows of a run, all `[s1, s2]`).
  it("refuses a blanket answer: more rows than the result allows given one identical list, of any length", () => {
    const it10 = wide("T-2", 10);
    const blanket = checkReply([it10], { results: [answer(it10, () => ["s1", "s2", "s3", "s4", "s5", "s6"])] });
    expect(blanket.ok.size).toBe(0);
    expect(blanket.problems[0]).toMatch(/^T-2: rows r1, r2, .*r10 \(10 of 10\) carry one identical list of segments: give each row the smallest set/);
    // the same list in another order is the same list; a short list is a blanket too
    expect(checkReply([it10], { results: [answer(it10, (_r, k) => (k % 2 ? ["s3", "s1", "s2"] : ["s1", "s2", "s3"]))] }).ok.size).toBe(0);
    expect(checkReply([it10], { results: [answer(it10, () => ["s1", "s2"])] }).ok.size).toBe(0);
    expect(checkReply([it10], { results: [answer(it10, () => ["s1"])] }).ok.size).toBe(0);
    // what is no blanket: a clause's quantifier, hypotheses and conclusion on one phrase (four rows); lists of their own
    expect(checkReply([it10], { results: [answer(it10, (_r, k) => (k < 4 ? ["s1"] : [`s${(k % 2) + 4}`]))] }).problems).toEqual([]);
    expect(sharedRows(answer(it10, (_r, k) => (k < 5 ? ["s1", "s2"] : [`s${k - 2}`])).rows, 10, 6)).toEqual(["r1", "r2", "r3", "r4", "r5"]);
    // one segment: the limit grows with the result — a quarter of its rows, or twice its rows per segment
    expect([sharedLimit(10, 6), sharedLimit(40, 30), sharedLimit(40, 4), sharedLimit(645, 25)]).toEqual([4, 10, 20, 162]);
    const it40 = wide("T-5", 40, 30);
    expect(checkReply([it40], { results: [answer(it40, (_r, k) => (k < 10 ? ["s1"] : [`s${(k % 28) + 3}`]))] }).problems).toEqual([]);
    expect(checkReply([it40], { results: [answer(it40, (_r, k) => (k < 20 ? ["s1"] : [`s${(k % 28) + 3}`]))] }).ok.size).toBe(0);
  });
  // The finding: 6 of 12 rows on one identical two-phrase list passed, under a limit made for one shared phrase.
  it("a list of several segments is a blanket on more than three rows, whatever the size of the result", () => {
    expect([sharedLimit(12, 6, 2), sharedLimit(645, 25, 3), sharedLimit(12, 6, 1)]).toEqual([3, 3, 4]);
    const it12 = wide("T-6", 12, 12);
    const own = (k: number) => [`s${k + 1}`];
    for (const n of [4, 6]) {
      const half = checkReply([it12], { results: [answer(it12, (_r, k) => (k < n ? ["s1", "s2"] : own(k)))] });
      expect(half.ok.size, `${n} rows`).toBe(0);
      expect(half.problems[0]).toContain(`(${n} of 12) carry one identical list of segments`);
    }
    // asked again and answered the same way, the rows are stored — marked, never as links of their own
    const again = checkReply([it12], { results: [answer(it12, (_r, k) => (k < 6 ? ["s1", "s2"] : own(k)))] }, true).ok.get("T-6")!;
    const stored = storedResult(it12, again);
    expect(stored.rows.filter((r) => r.coarse).map((r) => r.id)).toEqual(["r1", "r2", "r3", "r4", "r5", "r6"]);
    expect(stored.metrics.shared).toBe(6);
    // honest sharing stands unmarked: three hypotheses a two-phrase condition states together, two binders on one phrase
    const honest = checkReply([it12], { results: [answer(it12, (_r, k) => (k < 3 ? ["s1", "s2"] : k < 5 ? ["s3"] : own(k)))] });
    expect(honest.problems).toEqual([]);
    expect(storedResult(it12, honest.ok.get("T-6")).rows.some((r) => r.coarse)).toBe(false);
  });
  it("lenient (a result's second answer): keeps what is sound, leaves a bad row unanswered, lets a blanket list stand", () => {
    const it4 = wide("T-3", 4);
    const reply = { results: [{ obj_id: "T-3", uncovered: ["s9", "s6"], rows: [
      { row: "r1", segments: ["s1"], unstated: false }, { row: "r2", segments: ["s9"], unstated: false },
      { row: "r3", segments: ["s2", "s8"], unstated: false }, { row: "r9", segments: ["s1"], unstated: false },
    ] }] };
    expect(checkReply([it4], reply).ok.size).toBe(0);
    const kept = checkReply([it4], reply, true);
    expect(kept.ok.get("T-3")).toEqual({ obj_id: "T-3", uncovered: ["s6"], rows: [{ row: "r1", segments: ["s1"], unstated: false }, { row: "r3", segments: ["s2"], unstated: false }] });
    expect(kept.problems[0]).toContain("rows not answered: r2, r4");
    const it10 = wide("T-4", 10);
    expect(checkReply([it10], { results: [answer(it10, () => ["s1", "s2", "s3"])] }, true).ok.get("T-4")!.rows).toHaveLength(10);
    expect(checkReply([it10], { results: [answer(it10, () => ["s1", "s2"])] }, true).ok.get("T-4")!.rows).toHaveLength(10);
    // nothing sound at all is still no answer
    expect(checkReply([it4], { results: [{ obj_id: "T-3", rows: [{ row: "r9", segments: [], unstated: true }], uncovered: [] }] }, true).ok.size).toBe(0);
  });
  it("linkMetrics: what F5 measures of a result", () => {
    const it6 = wide("T-5", 6);
    const links = { obj_id: "T-5", uncovered: [], rows: [
      { row: "r1", segments: ["s1"], unstated: false }, { row: "r2", segments: ["s1"], unstated: false },
      { row: "r3", segments: ["s2", "s3", "s4"], unstated: false }, { row: "r4", segments: [], unstated: true },
    ] };
    expect(linkMetrics(it6, links)).toEqual({ asked: 6, linked: 3, unstated: 1, unanswered: 2, unique: 0.33, max_segments: 3, shared: 0 });
  });
});

describe("linkItems: calls by a row budget, one more ask for a result that failed", () => {
  const tpl = { assign: "ASSIGN\n{{items}}", verify: "VERIFY\n{{items}}\n{{assignment}}" };
  it("packs results into calls of at most 120 asked rows, in order; a larger result goes alone", () => {
    const items = [wide("A", 50), wide("B", 60), wide("C", 30), wide("D", 300), wide("E", 10), { ...wide("F", 115), rows: [...wide("F", 115).rows, ...Array.from({ length: 40 }, (_, k) => ({ id: `i${k}`, kind: "instance" as const, names: "", lean: "I" }))] }];
    expect(batchByRows(items).map((b) => b.map((x) => x.obj_id))).toEqual([["A", "B"], ["C"], ["D"], ["E"], ["F"]]);
    expect(batchByRows([wide("A", 60), wide("B", 60), wide("C", 1)]).map((b) => b.length)).toEqual([2, 1]);
    expect(batchByRows([])).toEqual([]);
  });
  it("asks a failed result once more, alone and told why; the others of its call are not asked again", async () => {
    const [a, b] = [wide("A", 5), wide("B", 5)];
    const calls: Array<[string, string]> = [];
    const ask = async (label: string, prompt: string) => {
      calls.push([label, prompt]);
      if (label.includes("verify")) return { results: [answer(a, (_r, k) => [`s${k + 1}`]), answer(b, (_r, k) => [`s${k + 1}`])], changes: [] };
      // first: B is a blanket answer; again: B alone, answered properly
      if (label.includes("again")) return { results: [answer(b, (_r, k) => [`s${k + 1}`])], changes: [] };
      return { results: [answer(a, (_r, k) => [`s${k + 1}`]), answer(b, () => ["s1", "s2", "s3"])], changes: [] };
    };
    const out = await linkItems([a, b], tpl, ask);
    expect(calls.map(([l]) => l)).toEqual(["F5 nl-links assign 1/1", "F5 nl-links assign 1/1 again B", "F5 nl-links verify 1/1"]);
    expect(calls[1][1]).toContain("## B (B)");
    expect(calls[1][1]).not.toContain("## A (A)");
    expect(calls[1][1]).toContain("Your previous answer for this result was not accepted — rows r1, r2, r3, r4, r5 (5 of 5) carry one identical list");
    expect([...out.linked.keys()].sort()).toEqual(["A", "B"]);
    expect(out.problems).toEqual([expect.stringMatching(/^B: rows r1.* \(asked again: answered\)$/)]);
  });
  it("an unparsable reply costs one more ask per result, never the batch; a result that fails twice is left unlinked", async () => {
    const [a, b] = [wide("A", 3), wide("B", 3)];
    const labels: string[] = [];
    const ask = async (label: string) => {
      labels.push(label);
      if (label.endsWith("assign 1/1")) return null;
      if (label.endsWith("again A")) return { results: [answer(a, (_r, k) => [`s${k + 1}`])], changes: [] };
      if (label.endsWith("again B")) return "still not json";
      return { results: [answer(a, (_r, k) => [`s${k + 1}`])], changes: ["T-1 row r1: s2 → s1"] };
    };
    const out = await linkItems([a, b], tpl, ask);
    expect(labels).toEqual(["F5 nl-links assign 1/1", "F5 nl-links assign 1/1 again A", "F5 nl-links assign 1/1 again B", "F5 nl-links verify 1/1"]);
    expect([...out.linked.keys()]).toEqual(["A"]);
    expect(out.problems).toEqual(["A: no answer (asked again: answered)", "B: no answer (asked again: not answered; no answer)"]);
    expect(out.changes).toEqual(["T-1 row r1: s2 → s1"]);
  });
  it("a verify reply that breaks the closed world keeps the assignment it audited", async () => {
    const a = wide("A", 3);
    const ask = async (label: string) => (label.includes("verify") ? { results: [{ obj_id: "A", rows: [], uncovered: [] }], changes: [] } : { results: [answer(a, (_r, k) => [`s${k + 1}`])], changes: [] });
    const out = await linkItems([a], tpl, ask);
    expect(out.linked.get("A")!.rows.map((r) => r.segments)).toEqual([["s1"], ["s2"], ["s3"]]);
    expect(out.problems).toEqual(["verify A: rows not answered: r1, r2, r3 (assignment kept)"]);
  });
  it("the prompts say what a blanket answer is: the smallest set of segments, in both", () => {
    const dir = path.join(__dirname, "..", "..", "src", "formalization", "prompts", "F5");
    for (const f of ["stage5_nl_links.txt", "stage5_nl_links_verify.txt"]) {
      const text = readFileSync(path.join(dir, f), "utf8");
      expect(text, f).toMatch(/SMALLEST set/);
      expect(text, f).toContain("rows of one clause seldom share a list");
      expect(text, f).toContain("{{items}}");
    }
  });
});
