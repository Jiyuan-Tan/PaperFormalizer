/**
 * `paperformalizer annotate <slug>` — rewrite a run's annotated paper (`runs/<slug>/annotated/`) for
 * the run as it stands, without running any stage (`annotate_run.ts`): the pending decisions of a
 * halt render at their passages exactly as the halt wrote them. No model is called. A block that could
 * not be set as TeX, or a pdflatex error, makes it exit non-zero, listing them (`render_check.ts`; a
 * tool defect, never waived). `--compile-record <path>`
 * keeps the compile guard's record elsewhere (default under the run's `logs/`). The run's state is
 * read, never written.
 */
import { existsSync } from "node:fs";
import path from "node:path";
import { applyWorkerEnv } from "../local_config.js";
import { assertQidSlug, statePath, verifyRunDir } from "../paths.js";
import { loadState } from "../state.js";
import { loadToolkitConfig } from "../toolkit/config.js";
import { annotateRun, type AnnotatedOutcome } from "./annotate_run.js";
import { lintAnnotated, renderBlock } from "./render_check.js";

export const ANNOTATE_USAGE =
  "Usage: paperformalizer annotate <slug> [--toolkit <path>] [--compile-record <path>]\n" +
  "  rewrite runs/<slug>/annotated/ for the run as it stands (no stage runs, no model call; state.json is only read).\n" +
  "  A block that could not be set as TeX (escaped, a code point, a pdflatex error) makes the command exit non-zero\n" +
  "  listing them — the PDF is still written.";

export const LINT_ANNOTATED_USAGE =
  "Usage: paperformalizer lint-annotated <slug> [--toolkit <path>]\n" +
  "  check runs/<slug>/annotated/ as written: the blocks the renderer could not set as TeX, pdflatex errors, and\n" +
  "  every \\vs… block scanned for \\textbackslash, \\^{}, [U+XXXX] code points and an odd number of $;\n" +
  "  exits non-zero listing them. No model call, nothing written.";

/** `paperformalizer lint-annotated <slug>`: the render check of the tree as written. */
export async function runLintAnnotatedCli(argv: string[], deps: { log?: (m: string) => void } = {}): Promise<void> {
  let slug: string | null = null;
  let toolkitArg: string | null = null;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i]!;
    if (a === "--toolkit") {
      const v = argv[i + 1];
      if (!v || v.startsWith("--")) throw new Error(`--toolkit needs a value.\n${LINT_ANNOTATED_USAGE}`);
      toolkitArg = v;
      i += 1;
    } else if (a.startsWith("--")) throw new Error(`unknown flag ${a}.\n${LINT_ANNOTATED_USAGE}`);
    else if (slug === null) slug = a;
    else throw new Error(`one slug only.\n${LINT_ANNOTATED_USAGE}`);
  }
  if (!slug) throw new Error(LINT_ANNOTATED_USAGE);
  assertQidSlug(slug);
  const toolkit = loadToolkitConfig({ explicit: toolkitArg });
  const runDir = verifyRunDir(toolkit.toolkitRoot, slug);
  if (!existsSync(runDir)) throw new Error(`no run ${slug} under ${toolkit.toolkitRoot}.`);
  const log = deps.log ?? ((m: string) => console.log(`[lint-annotated] ${m}`));
  const block = renderBlock(await lintAnnotated(runDir));
  if (block) throw new Error(`render check: ${block}`);
  log(`${path.join(runDir, "annotated")}: every block is set as TeX, no pdflatex error.`);
}

export interface AnnotateArgs {
  slug: string;
  toolkit: string | null;
  compileRecord: string | null;
}

export function parseAnnotateArgs(argv: string[]): AnnotateArgs {
  let slug: string | null = null;
  let toolkit: string | null = null;
  let compileRecord: string | null = null;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i]!;
    if (a === "--toolkit" || a === "--compile-record") {
      const v = argv[i + 1];
      if (!v || v.startsWith("--")) throw new Error(`${a} needs a value.\n${ANNOTATE_USAGE}`);
      if (a === "--toolkit") toolkit = v;
      else compileRecord = path.resolve(v);
      i += 1;
    } else if (a.startsWith("--")) throw new Error(`unknown flag ${a}.\n${ANNOTATE_USAGE}`);
    else if (slug === null) slug = a;
    else throw new Error(`one slug only.\n${ANNOTATE_USAGE}`);
  }
  if (!slug) throw new Error(ANNOTATE_USAGE);
  assertQidSlug(slug);
  return { slug, toolkit, compileRecord };
}

/** Why `annotate` exits non-zero, or null: the paper was not written, or a block could not be set
 * as TeX (a tool defect: listed, never waived — `render_check.ts`). */
export function annotateFailure(out: AnnotatedOutcome): Error | null {
  if (out.error) return new Error(`the annotated paper was not written: ${out.error}`);
  const render = renderBlock(out.render);
  return render ? new Error(`render check: ${render}\n  The annotated paper (written anyway): ${out.line}\n  Correct a text from the run's record, else fix the renderer with a test; then re-run this command (\`paperformalizer lint-annotated\` re-checks the tree as written).`) : null;
}

export async function runAnnotateCli(argv: string[], deps: { log?: (m: string) => void } = {}): Promise<void> {
  applyWorkerEnv();
  const a = parseAnnotateArgs(argv);
  const toolkit = loadToolkitConfig({ explicit: a.toolkit });
  const log = deps.log ?? ((m: string) => console.log(`[annotate] ${m}`));
  if (!existsSync(statePath(toolkit.toolkitRoot, a.slug))) throw new Error(`no run ${a.slug} under ${toolkit.toolkitRoot} (no state.json).`);
  const state = await loadState(toolkit.toolkitRoot, a.slug);
  if (!state.verify) throw new Error(`${a.slug} is not a verify run (state.json has no verify block).`);
  const out = await annotateRun({
    runDir: verifyRunDir(toolkit.toolkitRoot, a.slug),
    qid: a.slug,
    state,
    when: "annotate",
    ...(a.compileRecord ? { compileRecord: a.compileRecord } : {}),
    log,
  });
  const failure = annotateFailure(out);
  if (failure) throw failure;
}
