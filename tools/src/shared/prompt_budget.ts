// The length budget of one model call. The provider refuses an input past 1,048,576 characters
// ("Input exceeds the maximum length"), and the refusal names neither the stage nor what filled
// the prompt. A prompt over the budget is therefore never sent: the call fails BEFORE dispatch
// with the stage, the size and the largest sections, so the stage that pasted too much is fixed
// (a prompt that long is a stage carrying whole artifacts it should scope or hand over by file).

/** What one prompt may hold, in characters: the provider's hard limit less room for what the
 *  runners append (scratch instruction, session marker). */
export const PROMPT_INPUT_MAX = 1_000_000;

/** A line this long is a pasted artifact (a JSON document), a section of its own. */
const BLOB_LINE_MIN = 20_000;

export interface PromptSection {
  /** The `=== … ===` header, or the head of the line that introduces a pasted artifact. */
  name: string;
  chars: number;
}

/** A prompt cut at its `=== … ===` headers and at every pasted artifact (a line of
 *  `BLOB_LINE_MIN` characters or more, named by its own first words — the label a stage puts
 *  before the JSON it pastes), largest first. Pure. */
export function promptSections(prompt: string): PromptSection[] {
  const out: PromptSection[] = [];
  let cur: PromptSection = { name: "(head)", chars: 0 };
  const close = (): void => {
    if (cur.chars > 0) out.push(cur);
  };
  let prev = "";
  for (const line of prompt.split("\n")) {
    if (line.length >= BLOB_LINE_MIN) {
      close();
      const label = /^[\[{]/.test(line) ? prev.trim() : line;
      out.push({ name: `${label.slice(0, 90).trim()}…`, chars: line.length + 1 });
      cur = { name: "(text after it)", chars: 0 };
    } else if (/^=== .+ ===\s*$/.test(line) && !/^=== END\b/.test(line)) {
      close();
      cur = { name: line.trim(), chars: line.length + 1 };
    } else {
      cur.chars += line.length + 1;
    }
    if (line.trim()) prev = line;
  }
  close();
  return out.sort((a, b) => b.chars - a.chars);
}

export class PromptTooLongError extends Error {
  constructor(message: string, public readonly chars: number) {
    super(message);
    this.name = "PromptTooLongError";
  }
}

/** Throw `PromptTooLongError` when `prompt` is over `max`; `who` names the call (stage and label). */
export function assertPromptFits(prompt: string, who: string, max: number = PROMPT_INPUT_MAX): void {
  if (prompt.length <= max) return;
  const top = promptSections(prompt).slice(0, 5).map((s) => `  - ${s.chars} chars: ${s.name}`);
  throw new PromptTooLongError(
    `${who}: the prompt is ${prompt.length} characters, over the ${max} one call may hold (the provider refuses past 1048576) — not sent. ` +
      `Largest sections:\n${top.join("\n")}\n` +
      "Fix the stage that builds it: scope the pasted artifact to what the call needs, or hand it over by file.",
    prompt.length,
  );
}
