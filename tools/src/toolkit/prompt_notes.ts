// Per-base-library prompt notes: a base library may ship a Markdown file of usage notes
// (its tactics, simp sets, conventions) named by `prompt_notes` in `theoremchecker.json`. The F2
// scaffold and F4 filler prompts append one `## Notes for <name>` section per base library that
// has one; a library without notes contributes nothing.
import { readFileSync } from "node:fs";
import { loadToolkitConfig, type ToolkitConfig } from "./config.js";

/** The run's toolkit: `ctx.toolkit`, else the toolkit found from the repo root, else null. */
function resolveToolkit(ctx: { repoRoot: string; toolkit?: ToolkitConfig }): ToolkitConfig | null {
  if (ctx.toolkit) return ctx.toolkit;
  try {
    return loadToolkitConfig({ cwd: ctx.repoRoot });
  } catch {
    return null;
  }
}

/**
 * The `## Notes for <name>` sections of every base library with `prompt_notes`, in config order;
 * "" when none has notes. A configured notes file that cannot be read is a configuration error
 * and throws (naming the file), so an agent is never silently dispatched without the notes the
 * owner configured.
 */
export function baseLibraryNotesBlock(
  ctx: { repoRoot: string; toolkit?: ToolkitConfig },
  read: (file: string) => string = (f) => readFileSync(f, "utf8"),
): string {
  const cfg = resolveToolkit(ctx);
  if (!cfg) return "";
  const sections: string[] = [];
  for (const b of cfg.baseLibraries) {
    if (!b.promptNotes) continue;
    let text: string;
    try {
      text = read(b.promptNotes);
    } catch (e) {
      throw new Error(
        `prompt_notes of base library ${b.name} is unreadable at ${b.promptNotes} ` +
          `(${e instanceof Error ? e.message : String(e)}); fix or remove it in ${cfg.configPath}`,
      );
    }
    if (text.trim()) sections.push(`## Notes for ${b.name}\n\n${text.trim()}`);
  }
  return sections.join("\n\n");
}
