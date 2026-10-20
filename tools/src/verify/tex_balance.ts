/**
 * Structural balance of a TeX fragment taken from a paper: every brace group, math span
 * (`$…$`, `$$…$$`, `\(…\)`, `\[…\]`) and `\begin{X}…\end{X}` environment opened in it is closed
 * in it, in order. A stored statement or proof is a slice of the paper; a slice cut inside a
 * display (a proof ended at the QED mark set inside its last `eqnarray*`) fails this, and so
 * never reaches the referee, the fixer or the renderer as though it were whole.
 *
 * Unlike the compile check (tex_fragment_check.ts), which asks whether a model-written fragment can be
 * inserted as a macro argument (and so rejects `%`, `#`, a paragraph break), this reads paper
 * source as written: comments are skipped, `\verb` spans are opaque, only structure counts.
 */

/** One construct opened and not yet closed: `{`, `$`, `$$`, `\(`, `\[`, or `env:X`. */
export interface OpenConstruct {
  kind: string;
  /** offset of the opener in the scanned text */
  at: number;
  /** an environment's: the index of its `\begin` in the scan's `EnvTag` list */
  tag?: number;
}

/** One `\begin{X}` (`begin`) or `\end{X}` met by the scan, with `[start, end)` its offset. `matched`:
 * paired with its `\end` / `\begin` in the text. `outer`: what encloses it, outermost first — an open
 * environment as the index of its `\begin` in the list, any other construct as its kind (`{`, `$`, …). */
export interface EnvTag {
  begin: boolean;
  env: string;
  start: number;
  end: number;
  matched: boolean;
  outer: Array<number | string>;
}

const closerOf = (kind: string): string =>
  kind === "{" ? "}" : kind === "$" ? "$" : kind === "$$" ? "$$" : kind === "\\(" ? "\\)" : kind === "\\[" ? "\\]" : `\\end{${kind.slice(4)}}`;
const openerOf = (kind: string): string => (kind.startsWith("env:") ? `\\begin{${kind.slice(4)}}` : kind);

interface Scan {
  /** constructs still open at the end of the scan, outermost first */
  open: OpenConstruct[];
  /** closers met with no matching opener, or closing across another construct */
  stray: Array<{ closer: string; at: number; open: string | null }>;
}

/**
 * Scan `text[from, to)`. `stopWhenClosedAfter`: return as soon as, at an offset ≥ it, nothing
 * opened since `from` is still open (`closedAt` is that offset) — the first point past a mark
 * where the fragment may end. `tags`: each environment tag met is appended to it.
 */
function scan(text: string, from: number, to: number, stopWhenClosedAfter?: number, tags?: EnvTag[]): Scan & { closedAt: number | null } {
  const open: OpenConstruct[] = [];
  const stray: Scan["stray"] = [];
  const outer = (): Array<number | string> => open.map((o) => o.tag ?? o.kind);
  const close = (kind: string, closer: string, at: number): OpenConstruct | null => {
    for (let k = open.length - 1; k >= 0; k -= 1) {
      if (open[k]!.kind !== kind) continue;
      // closing across inner constructs: they are left unclosed (reported by the caller)
      if (k !== open.length - 1) stray.push({ closer, at, open: openerOf(open.at(-1)!.kind) });
      const o = open[k]!;
      open.length = k;
      return o;
    }
    stray.push({ closer, at, open: null });
    return null;
  };
  const inMath = (): boolean => open.some((o) => o.kind === "$" || o.kind === "$$" || o.kind === "\\(" || o.kind === "\\[");
  for (let i = from; i < to; i += 1) {
    if (stopWhenClosedAfter !== undefined && i >= stopWhenClosedAfter && open.length === 0) return { open, stray, closedAt: i };
    const c = text[i]!;
    if (c === "%") {
      const nl = text.indexOf("\n", i);
      i = nl < 0 || nl >= to ? to : nl;
      continue;
    }
    if (c === "\\") {
      // (never read past `to`: a scan up to a cut sees only the text before it)
      const rest = text.slice(i, Math.min(i + 120, to));
      const verb = /^\\verb\*?([^A-Za-z\s*])/.exec(rest);
      if (verb) {
        const endAt = text.indexOf(verb[1]!, i + verb[0].length);
        i = endAt < 0 || endAt >= to ? to : endAt;
        continue;
      }
      const be = /^\\(begin|end)\s*\{([^{}]*)\}/.exec(rest);
      if (be) {
        const env = be[2]!.trim();
        const kind = `env:${env}`;
        if (be[1] === "begin") {
          tags?.push({ begin: true, env, start: i, end: i + be[0].length, matched: false, outer: outer() });
          open.push({ kind, at: i, ...(tags ? { tag: tags.length - 1 } : {}) });
        } else {
          const o = close(kind, `\\end{${env}}`, i);
          if (tags) {
            if (o?.tag !== undefined) tags[o.tag]!.matched = true;
            tags.push({ begin: false, env, start: i, end: i + be[0].length, matched: o !== null, outer: outer() });
          }
        }
        i += be[0].length - 1;
        continue;
      }
      const n = i + 1 < to ? text[i + 1] : undefined;
      if (n === "(" || n === "[") {
        // `\[` inside math is a spacing/argument bracket only after `\\` (a row break's
        // optional argument is read as `\\[2pt]`, handled by the escape below)
        if (!(n === "[" && inMath())) open.push({ kind: `\\${n}`, at: i });
      } else if (n === ")" || n === "]") {
        const kind = n === ")" ? "\\(" : "\\[";
        close(kind, `\\${n}`, i);
      }
      i += 1; // an escaped character (`\$`, `\{`, `\\`, …) or a control word's first letter
      continue;
    }
    if (c === "$") {
      const dbl = i + 1 < to && text[i + 1] === "$";
      const kind = dbl ? "$$" : "$";
      const top = open.at(-1)?.kind;
      if (top === kind) open.pop();
      else if (dbl && top === "$") {
        // `$$` closing an inline span and opening the next (`$a$$b$`): read as two `$`
        open.pop();
        open.push({ kind: "$", at: i + 1 });
      } else open.push({ kind, at: i });
      if (dbl) i += 1;
      continue;
    }
    if (c === "{") open.push({ kind: "{", at: i });
    else if (c === "}") close("{", "}", i);
  }
  if (stopWhenClosedAfter !== undefined && to >= stopWhenClosedAfter && open.length === 0) return { open, stray, closedAt: to };
  return { open, stray, closedAt: null };
}

/** Each environment tag of `text`, in order (`EnvTag`): read as `scan` reads — comments skipped,
 * `\verb` opaque, an escaped backslash no tag (`\\end` is a row break and the word "end"). Pure. */
export function envTags(text: string): EnvTag[] {
  const tags: EnvTag[] = [];
  scan(text, 0, text.length, undefined, tags);
  return tags;
}

/** The environments a text leaves open or closes without opening (`envTags`): `close` the unmatched
 * `\end{X}` in the order met, `open` the unmatched `\begin{X}` innermost last. Pure. */
export function envImbalance(tex: string): { close: string[]; open: string[] } {
  const tags = envTags(tex).filter((t) => !t.matched);
  return { close: tags.filter((t) => !t.begin).map((t) => t.env), open: tags.filter((t) => t.begin).map((t) => t.env) };
}

/** The constructs opened in `text[from, at)` and still open at `at`, outermost first. */
export function openConstructsAt(text: string, from: number, at: number): OpenConstruct[] {
  return scan(text, from, at).open;
}

/**
 * The first offset ≥ `at` (and ≤ `limit`) at which nothing opened in `text` since `from` is
 * still open; null when the constructs open at `at` do not all close before `limit`.
 */
export function closingPointAfter(text: string, from: number, at: number, limit: number): number | null {
  return scan(text, from, limit, at).closedAt;
}

function lineCol(text: string, at: number): string {
  const before = text.slice(0, at);
  const line = before.split("\n").length;
  return `line ${line}`;
}

function excerptAt(text: string, at: number): string {
  const s = text.slice(at, at + 40).replace(/\s+/g, " ").trim();
  return s.length === 40 ? `${s}…` : s;
}

/**
 * Why `tex` is not a balanced fragment (empty: it is): each construct left open, each closer
 * without its opener, named with the fragment line it sits on and the text it starts.
 */
export function texBalanceProblems(tex: string): string[] {
  const { open, stray } = scan(tex, 0, tex.length);
  return [
    ...stray.map((s) =>
      s.open === null
        ? `${s.closer} with no opener (${lineCol(tex, s.at)}: "${excerptAt(tex, s.at)}")`
        : `${s.closer} closes across an unclosed ${s.open} (${lineCol(tex, s.at)})`,
    ),
    ...open.map((o) => `${openerOf(o.kind)} not closed by ${closerOf(o.kind)} (opened ${lineCol(tex, o.at)}: "${excerptAt(tex, o.at)}")`),
  ];
}

