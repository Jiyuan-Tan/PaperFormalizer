/**
 * THE MEANING OF A READING, AS A VERDICT BASIS READS IT (basis scheme ≥ 4, `core_graph.ts`).
 *
 * A symbol reading, a symbol-table entry's type / def, a pinned reading or a bookkeeping condition is
 * part of the basis of every verdict given under it — but a re-typesetting of that text (the compile
 * sweep writing `W ∈ 𝒲` as `$W\in\mathcal{W}$`, `\hat\gamma` as `\hat{\gamma}`, a reflowed line)
 * says the same thing and must not re-open those verdicts. `normalizeBasisText` maps such a text to
 * a canonical form that forgets typesetting only: math delimiters, whitespace, quote marks, trailing
 * periods, spacing and delimiter-sizing commands, empty groups, text wrappers, synonymous commands
 * (`\le`/`\leq`, `\mid`/`|`, …), the braces of a single-token argument (`x_i`/`x_{i}`) and the common
 * Unicode math characters (`∈`/`\in`, `α`/`\alpha`, `ℝ`/`\mathbb{R}`, `₀`/`_{0}`). It never changes
 * letter case, a prime (`'`), a font (`\mathcal` vs `\mathbb`, `\bar` vs `\overline`) or a word: two
 * texts that differ in anything a reader could take as meaning keep different forms.
 *
 * Statement text is NEVER normalized: a change to a statement is a real change.
 */

/** Unicode math characters → the TeX command they typeset (the forms the compile sweep writes). */
const UNICODE_TEX: Readonly<Record<string, string>> = {
  "∈": "\\in", "∉": "\\notin", "∋": "\\ni", "⊂": "\\subset", "⊆": "\\subseteq", "⊃": "\\supset", "⊇": "\\supseteq",
  "≤": "\\leq", "≥": "\\geq", "≠": "\\neq", "≈": "\\approx", "≡": "\\equiv", "∼": "\\sim", "≃": "\\simeq", "≍": "\\asymp",
  "→": "\\rightarrow", "←": "\\leftarrow", "↦": "\\mapsto", "⇒": "\\Rightarrow", "⇔": "\\Leftrightarrow", "↔": "\\leftrightarrow",
  "∞": "\\infty", "∑": "\\sum", "∏": "\\prod", "∫": "\\int", "∂": "\\partial", "∇": "\\nabla", "√": "\\sqrt",
  "∀": "\\forall", "∃": "\\exists", "¬": "\\neg", "∧": "\\wedge", "∨": "\\vee", "∪": "\\cup", "∩": "\\cap", "∅": "\\emptyset",
  "×": "\\times", "·": "\\cdot", "⋅": "\\cdot", "∘": "\\circ", "±": "\\pm", "∓": "\\mp", "⊥": "\\perp", "∣": "|",
  "…": "\\ldots", "⋯": "\\ldots", "⟨": "\\langle", "⟩": "\\rangle", "‖": "\\|", "⊗": "\\otimes", "⊕": "\\oplus",
  "α": "\\alpha", "β": "\\beta", "γ": "\\gamma", "δ": "\\delta", "ε": "\\varepsilon", "ϵ": "\\epsilon", "ζ": "\\zeta",
  "η": "\\eta", "θ": "\\theta", "ϑ": "\\vartheta", "ι": "\\iota", "κ": "\\kappa", "λ": "\\lambda", "μ": "\\mu", "ν": "\\nu",
  "ξ": "\\xi", "π": "\\pi", "ρ": "\\rho", "σ": "\\sigma", "ς": "\\varsigma", "τ": "\\tau", "υ": "\\upsilon", "φ": "\\varphi",
  "ϕ": "\\phi", "χ": "\\chi", "ψ": "\\psi", "ω": "\\omega",
  "Γ": "\\Gamma", "Δ": "\\Delta", "Θ": "\\Theta", "Λ": "\\Lambda", "Ξ": "\\Xi", "Π": "\\Pi", "Σ": "\\Sigma", "Υ": "\\Upsilon",
  "Φ": "\\Phi", "Ψ": "\\Psi", "Ω": "\\Omega",
  "ℝ": "\\mathbb{R}", "ℕ": "\\mathbb{N}", "ℤ": "\\mathbb{Z}", "ℚ": "\\mathbb{Q}", "ℂ": "\\mathbb{C}", "ℙ": "\\mathbb{P}",
  "ℬ": "\\mathcal{B}", "ℰ": "\\mathcal{E}", "ℱ": "\\mathcal{F}", "ℋ": "\\mathcal{H}", "ℐ": "\\mathcal{I}", "ℒ": "\\mathcal{L}",
  "ℳ": "\\mathcal{M}", "ℛ": "\\mathcal{R}", "ℎ": "h",
  "–": "--", "—": "---", "−": "-", "ℓ": "\\ell", "≲": "\\lesssim", "≳": "\\gtrsim", "≪": "\\ll", "≫": "\\gg", "′": "'", "∥": "\\|",
  "⊤": "\\top", "⋂": "\\bigcap", "⋃": "\\bigcup", "≺": "\\prec", "≻": "\\succ", "∖": "\\setminus", "⌊": "\\lfloor", "⌋": "\\rfloor",
  "⌈": "\\lceil", "⌉": "\\rceil",
};

const SUB: Readonly<Record<string, string>> = { "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4", "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9", "₊": "+", "₋": "-", "ᵢ": "i", "ⱼ": "j", "ₖ": "k", "ₙ": "n", "ₜ": "t" };
const SUP: Readonly<Record<string, string>> = { "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4", "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9", "⁺": "+", "⁻": "-", "ⁿ": "n", "ᵀ": "T" };

/** A mathematical alphanumeric character (U+1D400 block) as its TeX: the script / double-struck /
 * bold capitals and letters the compile sweep writes as `\mathcal` / `\mathbb` / `\mathbf`; null for
 * any other character. */
function mathAlnum(cp: number): string | null {
  const letter = (base: number, font: string | null): string | null => {
    const k = cp - base;
    if (k < 0 || k >= 52) return null;
    const c = String.fromCharCode(k < 26 ? 65 + k : 97 + k - 26);
    return font === null ? c : `\\${font}{${c}}`;
  };
  return (
    letter(0x1d400, "mathbf") ?? // bold
    letter(0x1d434, null) ?? // italic: the default math font
    letter(0x1d49c, "mathcal") ?? // script
    letter(0x1d4d0, "mathcal") ?? // bold script
    letter(0x1d538, "mathbb") // double-struck
  );
}

/** Commands spelled two ways for the same symbol: → the one form kept. */
const SYNONYMS: ReadonlyArray<readonly [RegExp, string]> = [
  [/\\le(?![a-zA-Z])/g, "\\leq"],
  [/\\ge(?![a-zA-Z])/g, "\\geq"],
  [/\\ne(?![a-zA-Z])/g, "\\neq"],
  [/\\to(?![a-zA-Z])/g, "\\rightarrow"],
  [/\\gets(?![a-zA-Z])/g, "\\leftarrow"],
  [/\\(?:dots|cdots|dotsc|dotsb)(?![a-zA-Z])/g, "\\ldots"],
  [/\.\.\./g, "\\ldots"],
  [/\\(?:mid|vert|lvert|rvert)(?![a-zA-Z])/g, "|"],
  [/\\(?:Vert|lVert|rVert)(?![a-zA-Z])/g, "\\|"],
  [/\\lbrace(?![a-zA-Z])/g, "\\{"],
  [/\\rbrace(?![a-zA-Z])/g, "\\}"],
  [/\\colon(?![a-zA-Z])/g, ":"],
  [/\\[dt]frac(?![a-zA-Z])/g, "\\frac"],
  [/\\land(?![a-zA-Z])/g, "\\wedge"],
  [/\\lor(?![a-zA-Z])/g, "\\vee"],
  [/\\lnot(?![a-zA-Z])/g, "\\neg"],
  [/\\iff(?![a-zA-Z])/g, "\\Leftrightarrow"],
  [/\\implies(?![a-zA-Z])/g, "\\Rightarrow"],
];

/** Commands that only size or space: dropped (`\left.` / `\right.` with their null delimiter; a tie
 * `~` only before a reference or a number — a bare `~` may be a plain-text "distributed as"). */
const DROPPED = /\\(?:left|right|middle)\.|\\(?:left|right|middle|[bB]igg?[lr]?|displaystyle|textstyle|scriptstyle|quad|qquad|nonumber|limits|nolimits)(?![a-zA-Z])|(?<!\\)\\[,;:! ]|(?<=[A-Za-z.])~(?=\\(?:ref|eqref|cref|Cref|cite|citet|citep)(?![a-zA-Z])|\d)/g;

/** Wrappers whose argument is plain text or an upright name: → the argument. */
const TEXT_WRAPPER = /\\(?:text|textrm|textnormal|textup|textit|textbf|emph|mbox|mathrm|operatorname)\s*\{([^{}]*)\}/g;

/** Accent and font commands taking one argument: a single-token argument is braced (`\hat\gamma`
 * and `\hat{\gamma}` alike). */
const ONE_ARG = /\\(hat|widehat|bar|overline|underline|tilde|widetilde|check|vec|dot|ddot|breve|acute|grave|mathcal|mathbb|mathbf|mathsf|mathscr|mathfrak|mathit|boldsymbol|bm)(?![a-zA-Z])\s*(\\[a-zA-Z]+|[A-Za-z0-9])/g;

/** A sub- or superscript's single-token argument, braced (`x_i` and `x_{i}` alike). */
const SCRIPT_ARG = /([_^])\s*(\\[a-zA-Z]+|[A-Za-z0-9])/g;

/**
 * `text` in the canonical form a verdict basis reads (see the module overview): two texts that differ
 * only in typesetting get the same form. Idempotent.
 */
export function normalizeBasisText(text: string): string {
  let t = text.normalize("NFC");
  // Quote marks (a closing single quote that is an apostrophe stays one; an ASCII `'` is a prime).
  t = t.replace(/``([^`']*?)''/g, "$1").replace(/`([^`']*?)'/g, "$1");
  t = t.replace(/’/g, "'").replace(/(?<!\\)"/g, "").replace(/[“”„‟‘‚‛«»‹›`]/g, "");
  // Math delimiters.
  t = t.replace(/(?<!\\)\\[()[\]]/g, " ").replace(/(?<!\\)\$/g, " ");
  // Unicode math → TeX.
  let out = "";
  for (const ch of t) {
    const cp = ch.codePointAt(0)!;
    out += UNICODE_TEX[ch] !== undefined ? `${UNICODE_TEX[ch]} ` : cp >= 0x1d400 && cp <= 0x1d7ff ? (mathAlnum(cp) ?? ch) : ch;
  }
  t = out
    .replace(/[₀-₉₊₋ᵢⱼₖₙₜ]+/g, (run) => `_{${[...run].map((c) => SUB[c]).join("")}}`)
    .replace(/[⁰¹²³⁴-⁹⁺⁻ⁿᵀ]+/g, (run) => `^{${[...run].map((c) => SUP[c]).join("")}}`);
  // Text wrappers, synonyms, sizing / spacing.
  for (let prev = ""; prev !== t; ) (prev = t), (t = t.replace(TEXT_WRAPPER, "$1"));
  for (const [re, to] of SYNONYMS) t = t.replace(re, to);
  t = t.replace(DROPPED, " ");
  // Single-token arguments braced; empty groups dropped; whitespace dropped.
  for (let prev = ""; prev !== t; ) (prev = t), (t = t.replace(ONE_ARG, "\\$1{$2}"));
  t = t.replace(SCRIPT_ARG, "$1{$2}");
  for (let prev = ""; prev !== t; ) (prev = t), (t = t.replace(/\{\s*\}/g, ""));
  t = t.replace(/\s+/g, "");
  // Trailing periods.
  return t.replace(/\.+$/, "");
}
