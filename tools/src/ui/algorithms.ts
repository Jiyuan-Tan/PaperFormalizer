// Pseudocode for the paper page: the `algorithmic` environment (algorithmic / algpseudocode, upper- or
// mixed-case commands) and an algorithm2e body, as numbered lines with their keywords and indentation.
// `inline` renders a TeX fragment (math, text commands) the way the rest of the page does. Pure.

type Inline = (tex: string) => string;
interface Line { level: number; html: string; numbered: boolean }

const esc = (s: string): string => s.replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]!);
const kw = (word: string): string => `<b class="kw">${esc(word)}</b>`;

/** A balanced `{…}` group at `i` (after spaces), or null. */
function group(s: string, i: number): { body: string; end: number } | null {
  let j = i;
  while (s[j] === " " || s[j] === "\n" || s[j] === "\t") j++;
  if (s[j] !== "{") return null;
  let d = 0;
  for (let k = j; k < s.length; k++) {
    if (s[k] === "\\") { k++; continue; }
    if (s[k] === "{") d++;
    else if (s[k] === "}" && --d === 0) return { body: s.slice(j + 1, k), end: k + 1 };
  }
  return null;
}
/** An optional `[…]` at `i` (after spaces), or null. */
function opt(s: string, i: number): { body: string; end: number } | null {
  const m = /^\s*\[([^\]]*)\]/.exec(s.slice(i));
  return m ? { body: m[1]!, end: i + m[0].length } : null;
}

function linesHTML(lines: Line[], numbered: boolean): string {
  let n = 0;
  const items = lines.filter((l) => l.html.trim()).map((l) => {
    const num = numbered && l.numbered ? `<span class="ln">${++n}</span>` : `<span class="ln"></span>`;
    return `<li style="--lvl:${l.level}">${num}<span class="lt">${l.html}</span></li>`;
  });
  return `<ol class="algo${numbered ? " numbered" : ""}">${items.join("")}</ol>`;
}

// algorithmic / algpseudocode: what each command opens, closes or states (keys lowercase)
const OPEN: Record<string, [string, string]> = { if: ["if", "then"], for: ["for", "do"], forall: ["for all", "do"], while: ["while", "do"], loop: ["loop", ""], repeat: ["repeat", ""], function: ["function", ""], procedure: ["procedure", ""] };
const CLOSE: Record<string, string> = { endif: "end if", endfor: "end for", endwhile: "end while", endloop: "end loop", endfunction: "end function", endprocedure: "end procedure" };
const LABEL: Record<string, string> = { require: "Require:", ensure: "Ensure:", input: "Input:", output: "Output:" };
const ALGORITHMIC_CMD = /\\(State|Statex|STATE|STATEX|Require|REQUIRE|Ensure|ENSURE|Input|Output|INPUT|OUTPUT|If|IF|ElsIf|ELSIF|Else|ELSE|EndIf|ENDIF|For|FOR|ForAll|FORALL|EndFor|ENDFOR|While|WHILE|EndWhile|ENDWHILE|Loop|LOOP|EndLoop|ENDLOOP|Repeat|REPEAT|Until|UNTIL|Function|EndFunction|Procedure|EndProcedure|Return|RETURN|Comment|COMMENT|Call)(?![A-Za-z])\*?/g;

/** The body of an `algorithmic` environment (its `[1]` option numbers every line). */
export function renderAlgorithmic(body: string, inline: Inline): string {
  const o = opt(body, 0);
  const numbered = Boolean(o && Number(o.body) > 0);
  const src = o ? body.slice(o.end) : body;
  const lines: Line[] = [];
  let level = 0;
  let cur = null as Line | null;
  const push = (html: string, numberedLine = true): Line => { cur = { level, html, numbered: numberedLine }; lines.push(cur); return cur; };
  const text = (t: string) => { if (t.trim()) { if (cur) cur.html += inline(t); else push(inline(t)); } };
  let last = 0;
  // an annotation block (`\vsOriginal{…}`, a repaired step's printed and corrected text) is one text:
  // a command inside it (`\Return`, `\Comment`) is the step's own and starts no line
  const marks: Array<[number, number]> = [];
  for (const v of src.matchAll(/\\vs[A-Za-z]+/g)) {
    let end = v.index! + v[0].length;
    for (let g = group(src, end); g; g = group(src, end)) end = g.end;
    marks.push([v.index!, end]);
  }
  ALGORITHMIC_CMD.lastIndex = 0;
  for (let m: RegExpExecArray | null; (m = ALGORITHMIC_CMD.exec(src));) {
    const inMark = marks.find(([a, b]) => a < m!.index && m!.index < b);
    if (inMark) { ALGORITHMIC_CMD.lastIndex = inMark[1]; continue; }
    text(src.slice(last, m.index));
    const name = m[1]!.toLowerCase();
    let i = m.index + m[0].length;
    const arg = (): string => { const g = group(src, i); if (!g) return ""; i = g.end; return g.body; };
    if (name === "state") push("");
    else if (name === "statex") push("", false);
    else if (name in LABEL) push(`${kw(LABEL[name]!)} `, false); // unnumbered, as algorithmicx prints them
    else if (name === "return") (cur && !cur.html.trim() ? cur : push("")).html += `${kw("return")} `;
    // a comment closes the line it follows — a block's head or end line included
    else if (name === "comment") { const c = arg(); (cur ?? lines.at(-1) ?? push("")).html += ` <span class="cmt">▷ ${inline(c)}</span>`; }
    else if (name === "call") { const f = arg(), a = arg(); (cur ?? push("")).html += `<span class="call">${inline(f)}</span>(${inline(a)})`; }
    else if (name in OPEN) {
      const [w, tail] = OPEN[name]!;
      if (name === "function" || name === "procedure") { const f = arg(), a = arg(); push(`${kw(w)} <span class="call">${inline(f)}</span>(${inline(a)})`); }
      else { const c = name === "loop" || name === "repeat" ? "" : arg(); push(`${kw(w)}${c ? ` ${inline(c)}` : ""}${tail ? ` ${kw(tail)}` : ""}`); }
      level++;
    } else if (name === "elsif") { level = Math.max(0, level - 1); push(`${kw("else if")} ${inline(arg())} ${kw("then")}`); level++; }
    else if (name === "else") { level = Math.max(0, level - 1); push(kw("else")); level++; }
    else if (name === "until") { level = Math.max(0, level - 1); push(`${kw("until")} ${inline(arg())}`); }
    else if (name in CLOSE) { level = Math.max(0, level - 1); push(kw(CLOSE[name]!)); }
    // the line a block keyword opened takes no further text: what follows starts the next one
    if (name in OPEN || name in CLOSE || name === "else" || name === "elsif" || name === "until") cur = null;
    last = i;
    ALGORITHMIC_CMD.lastIndex = i;
  }
  text(src.slice(last));
  return linesHTML(lines, numbered);
}

// algorithm2e: statements end in `\;`, a block takes its body as a brace argument (a `\lIf`-style
// block, its one statement), and a block may carry a comment in parentheses: `\For(\tcc{…}){…}{…}`.
const A2E_BLOCK = /\\(eIf|uIf|uElseIf|uElse|Repeat|Fn|l?(?:ForEach|ForAll|For|While|ElseIf|If|Else))(?![A-Za-z])/g;
const A2E_HEAD: Record<string, [string, string]> = { For: ["for", "do"], ForEach: ["foreach", "do"], ForAll: ["forall", "do"], While: ["while", "do"], If: ["if", "then"], uIf: ["if", "then"], ElseIf: ["else if", "then"], uElseIf: ["else if", "then"], Fn: ["function", ""] };
const A2E_LABEL: Record<string, string> = { KwIn: "Input:", KwOut: "Output:", KwData: "Data:", KwResult: "Result:", Input: "Input:", Output: "Output:" };
/** Layout and keyword-definition commands, with the number of brace arguments each takes. */
const A2E_SETUP: Record<string, number> = {
  SetAlgoLined: 0, SetAlgoNoLine: 0, SetAlgoVlined: 0, SetAlgoNoEnd: 0, DontPrintSemicolon: 0, PrintSemicolon: 0, LinesNumbered: 0, LinesNotNumbered: 0,
  SetNoFillComment: 0, BlankLine: 0, ResetInOut: 1, IncMargin: 1, DecMargin: 1, SetAlFnt: 1, SetAlCapFnt: 1, SetAlTitleFnt: 1, SetArgSty: 1, SetFuncSty: 1,
  SetDataSty: 1, SetKwSty: 1, SetCommentSty: 1, SetProcNameSty: 1, SetProcArgSty: 1, SetFuncArgSty: 1, SetAlgoCaptionSeparator: 1, vspace: 1,
  SetKwInOut: 2, SetKwInput: 2, SetKwData: 2, SetKwFunction: 2, SetKw: 2, SetKwBlock: 3, SetKwRepeat: 3, SetAlgorithmName: 3, SetKwProg: 4, SetKwFor: 4, SetKwIF: 6, SetKwSwitch: 7,
};

/** `src` without the setup commands (and their arguments). */
function stripSetup(src: string): string {
  const re = new RegExp(String.raw`\\(${Object.keys(A2E_SETUP).join("|")})(?![A-Za-z])\*?`, "g");
  let out = "", last = 0;
  for (let m: RegExpExecArray | null; (m = re.exec(src));) {
    let j = m.index + m[0].length;
    for (let k = 0; k < A2E_SETUP[m[1]!]!; k++) { const g = group(src, j); if (!g) break; j = g.end; }
    out += src.slice(last, m.index); last = j; re.lastIndex = j;
  }
  return out + src.slice(last);
}

/** Split at `\;` outside braces and math (a `\;` inside a formula is a thin space). */
function statements(src: string): string[] {
  const out: string[] = [];
  let depth = 0, math = false, from = 0;
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    if (c === "\\") { if (src[i + 1] === ";" && depth === 0 && !math) { out.push(src.slice(from, i)); from = i + 2; } i++; continue; }
    if (c === "{") depth++;
    else if (c === "}") depth = Math.max(0, depth - 1);
    else if (c === "$") math = !math;
  }
  out.push(src.slice(from));
  return out;
}

/** The body of an algorithm2e `algorithm` environment (caption and labels already removed). */
export function renderAlgorithm2e(body0: string, inline: Inline): string {
  const lines: Line[] = [];
  const numbered = /\\LinesNumbered\b/.test(body0);
  // names the paper defines for its own functions, data and keywords show as names
  let body = body0;
  for (const m of body0.matchAll(/\\SetKw(Function|Data|)\s*\{\s*\\?([A-Za-z]+)\s*\}\s*\{((?:[^{}]|\{[^{}]*\})*)\}/g)) {
    const [kind, name, shown] = [m[1]!, m[2]!, m[3]!];
    const call = new RegExp(String.raw`\\${name}(?![A-Za-z])(\s*\{((?:[^{}]|\{[^{}]*\})*)\})?`, "g");
    body = body.replace(call, (_x, a: string | undefined, args: string | undefined) =>
      kind === "Function" ? `\\textsc{${shown}}${a ? `(${args})` : ""}` : kind === "Data" ? `\\textsc{${shown}}` : `\u0003${shown}\u0004`);
  }
  body = stripSetup(body);
  const walk = (src: string, level: number): void => {
    let buf = "";
    const flush = () => {
      for (const stmt of statements(buf)) {
        const t = stmt.replace(/\\(KwIn|KwOut|KwData|KwResult|Input|Output)(?![A-Za-z])\s*\{((?:[^{}]|\{[^{}]*\})*)\}/g, (_x, k: string, v: string) => `\u0000${k}\u0001${v}\u0002`);
        for (const piece of t.split(/(?=\u0000)/)) {
          const m = /^\u0000(\w+)\u0001([\s\S]*?)\u0002([\s\S]*)$/.exec(piece);
          if (m) {
            lines.push({ level, html: `${kw(A2E_LABEL[m[1]!] ?? `${m[1]}:`)} ${fmt(m[2]!, inline)}`, numbered: false });
            if (m[3]!.trim()) lines.push({ level, html: fmt(m[3]!, inline), numbered: true });
          } else if (piece.trim()) lines.push({ level, html: fmt(piece, inline), numbered: true });
        }
      }
      buf = "";
    };
    let last = 0;
    A2E_BLOCK.lastIndex = 0;
    for (let m: RegExpExecArray | null; (m = A2E_BLOCK.exec(src));) {
      buf += src.slice(last, m.index);
      flush();
      const oneLine = /^l[A-Z]/.test(m[1]!);
      const name = oneLine ? m[1]!.slice(1) : m[1]!;
      let i = m.index + m[0].length;
      // a comment on the block, in parentheses
      let note = "";
      const p = /^\s*\(/.exec(src.slice(i));
      if (p) {
        let d = 0, j = i + p[0].length - 1;
        for (; j < src.length; j++) { if (src[j] === "(") d++; else if (src[j] === ")" && --d === 0) break; }
        note = fmt(src.slice(i + p[0].length, j), inline); i = j + 1;
      }
      const arg = (): string => { const g = group(src, i); if (!g) return ""; i = g.end; return g.body; };
      const head = (h: string) => lines.push({ level, html: `${h}${note ? ` ${note}` : ""}`, numbered: true });
      if (name === "Else" || name === "uElse") {
        const b = arg();
        if (oneLine) head(`${kw("else")} ${fmt(b.replace(/\\;\s*$/, ""), inline)}`); else { head(kw("else")); walk(b, level + 1); }
      } else if (name === "Repeat") {
        const until = arg(), b = arg();
        head(kw("repeat")); walk(b, level + 1);
        lines.push({ level, html: `${kw("until")} ${fmt(until, inline)}`, numbered: true });
      } else if (name === "eIf") {
        const c = arg(), t = arg(), e = arg();
        head(`${kw("if")} ${fmt(c, inline)} ${kw("then")}`); walk(t, level + 1);
        lines.push({ level, html: kw("else"), numbered: true }); walk(e, level + 1);
      } else {
        const [w, tail] = A2E_HEAD[name] ?? [name, ""];
        const c = arg(), b = arg();
        const top = `${kw(w)} ${fmt(c, inline)}${tail ? ` ${kw(tail)}` : ""}`;
        if (oneLine) head(`${top} ${fmt(b.replace(/\\;\s*$/, ""), inline)}`); else { head(top); walk(b, level + 1); }
      }
      last = i;
      A2E_BLOCK.lastIndex = i;
    }
    buf += src.slice(last);
    flush();
  };
  walk(body, 0);
  return linesHTML(lines, numbered);
}

/** `\tcp{…}` / `\tcc{…}` (starred, with a placement option) marked as comments, their text brace-matched
 *  to any depth (`\tcp{\footnotesize {… $\abs{x}$ …}}`). */
function comments(s: string): string {
  let out = "", i = 0;
  for (const m of s.matchAll(/\\(?:tcp|tcc)(?![A-Za-z])\*?(?:\[[^\]]*\])?\s*(?=\{)/g)) {
    if (m.index! < i) continue;
    const g = group(s, m.index! + m[0].length);
    if (!g) continue;
    out += s.slice(i, m.index) + `\u0005${g.body}\u0006`;
    i = g.end;
  }
  return out + s.slice(i);
}

/** A statement's text with the inline keywords (`\KwTo`, `\KwRet`) and comments set apart. */
function fmt(s0: string, inline: Inline): string {
  const s = s0.replace(/\\KwTo(?![A-Za-z])/g, "\u0003to\u0004")
    .replace(/\\(KwRet|Return)(?![A-Za-z])\s*\{((?:[^{}]|\{[^{}]*\})*)\}/g, "\u0003return\u0004 $2").replace(/\\(KwRet|Return)(?![A-Za-z])/g, "\u0003return\u0004")
    .replace(/\u0005|\u0006/g, "");
  return comments(s).split(/(\u0003[^\u0004]*\u0004|\u0005[^\u0006]*\u0006)/).map((part) =>
    part.startsWith("\u0003") ? ` ${kw(part.slice(1, -1))} ` : part.startsWith("\u0005") ? ` <span class="cmt">▷ ${inline(part.slice(1, -1))}</span>` : part.trim() ? inline(part) : "").join("");
}
