// Canonical read path for core JSON artifacts.
//
// A core file is written by the RUNNER (`JSON.stringify`), and its strings are the paper's text
// verbatim: V1's model writes a reference core (`core_refs.json`, read in `verify/stage_v1.ts`
// through `normalizeRawModelJson`) and the runner copies the text. So a core is read as the
// valid JSON it is, with no repair of its strings, behind the decoded control-character
// backstop (fail-loud with the artifact path, never silent corruption). Every reader of a
// core-shaped artifact goes through here rather than bare `JSON.parse`, which would skip the
// schema and that backstop.
import { readFile } from "node:fs/promises";
import { CoreSchema, type Core } from "./schema.js";
import { assertNoDecodedControlChars } from "./latex_serialization.js";
import { artifactPath } from "../paths.js";
import type { PipelineContext } from "../types.js";

/** `runs/<slug>/discovery/core.json`: the typed core V1.5 accepted and the F stages read. */
export function coreJsonPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "core.json");
}

/** Schema-parse and control-check already-read core text — for callers that need
 * their own read/error wrapping but must NOT fall back to bare `JSON.parse`. */
export function parseTypedCore(text: string, source: string): Core {
  // No model-JSON normalization and no LaTeX repair: both encode how MODELS mis-author TeX
  // (a `\t` before a letter is an under-escaped `\theta`, a lone `\` before a line break a
  // botched row terminator, …). On the runner's file a `\t` escape is a real tab of a
  // tab-indented paper and a control space at a line end is the paper's; rewriting either
  // breaks the verbatim contract the lint enforces.
  const core = CoreSchema.parse(JSON.parse(text)) as Core;
  // A tab is the source's indentation (TeX reads it as a space); every other control
  // character stays refused.
  assertNoDecodedControlChars(core, source);
  return core;
}

/** Read + schema-parse + control-check a core artifact. Throws with the artifact path on
 * unrecoverable corruption. */
export async function readTypedCore(filePath: string): Promise<Core> {
  return parseTypedCore(await readFile(filePath, "utf8"), `core artifact ${filePath}`);
}

/** The ids of the UMBRELLA statements of a core (`schema.ts` `umbrella`, verify mode): results that
 * only say that the blocks split off them hold. */
export function umbrellaIds(core: Pick<Core, "statements">): string[] {
  return core.statements.filter((s) => s.umbrella).map((s) => s.id);
}

/**
 * The core AS THE F STAGES FORMALIZE IT: without its umbrella statements and every edge to one. An
 * umbrella has no Lean declaration of its own — no plan entry, no `@node` tag, no graph node, no review
 * target, no proof hole, no docstring: it is established exactly when all its blocks are, and that is
 * DERIVED where a run is read (`verify/report.ts`, `ui/run_model.ts`), never recorded by an F stage.
 * So every F-stage gate sees a core in which each statement takes a declaration, and a plan entry or a
 * tag naming an umbrella is refused as one naming no core node. The same object when the core has no
 * umbrella. Pure.
 */
export function formalizationView(core: Core): Core {
  const gone = new Set(umbrellaIds(core));
  if (gone.size === 0) return core;
  return { ...core, statements: core.statements.filter((s) => !gone.has(s.id)).map((s) => (s.depends_on.some((d) => gone.has(d)) ? { ...s, depends_on: s.depends_on.filter((d) => !gone.has(d)) } : s)) };
}

/** `readTypedCore` for an F stage: the formalization view (`formalizationView`). */
export async function readFormalizationCore(filePath: string): Promise<Core> {
  return formalizationView(await readTypedCore(filePath));
}
