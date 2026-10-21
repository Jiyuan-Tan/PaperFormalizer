// Central model registry. The pipeline dispatches to two agent runners — OpenAI
// `codex` (extraction, referees, scaffold, proofs, reviews) and Anthropic `claude` (plan, curation) —
// and every concrete model id flows through this module so a user on a different
// model lineup can override them WITHOUT editing source.
//
// Each logical role has a committed default (the current lineup) and an env-var
// override. Set the env var to any id the corresponding CLI accepts:
//   - codex roles  → an OpenAI `codex` model id (e.g. "gpt-6.1-sol")
//   - claude roles → a `claude` CLI --model value: an alias ("opus"/"sonnet"/
//     "haiku") or a pinned id ("claude-opus-4-8").
//
// Env overrides (all optional):
//   PAPERFORMALIZER_MODEL_CODEX_KERNEL   F2 scaffolder, proof filler, F2.5–F4 reviewers (default gpt-6.1-sol)
//   PAPERFORMALIZER_MODEL_CODEX_MECH     mechanical / clerical (V1 extraction, F1.5, F5) (default gpt-6.1-sol)
//   PAPERFORMALIZER_MODEL_CODEX_VERIFY   V1 fixer, V1.5 referee + clarity               (default gpt-6.1-sol)
//   PAPERFORMALIZER_MODEL_CLAUDE_MAIN    F1 planner, curator, gardener                  (default opus)
//
// On a machine with codex alone the claude roles run on the codex kernel model at high effort
// (`claude_roles.ts`).

/** A value accepted by the `claude` CLI `--model` flag: an alias
 *  (opus/sonnet/haiku) or a pinned model id. */
export type ClaudeModel = string;

function envModel(key: string, def: string): string {
  const v = process.env[key];
  return v && v.trim() ? v.trim() : def;
}

/** Concrete model ids by logical role, each overridable via its env var. */
export const MODELS = {
  /** codex, hard kernel-math / proof tier: the F2 scaffolder, the proof filler and the F2.5–F4 reviewers. */
  // Every gpt-6-sol tier moved to gpt-6.1-sol (user decision 2026-09-30).
  codexKernel: envModel("PAPERFORMALIZER_MODEL_CODEX_KERNEL", "gpt-6.1-sol"),
  /** codex, mechanical / clerical tier. */
  codexMechanical: envModel("PAPERFORMALIZER_MODEL_CODEX_MECH", "gpt-6.1-sol"),
  /** codex, the verify tier: the V1 fixer and the V1.5 referee (nodes and symbols) (user decisions
   *  2026-09-26: gpt-5.6-sol; 2026-09-30: gpt-6.1-sol). */
  codexVerify: envModel("PAPERFORMALIZER_MODEL_CODEX_VERIFY", "gpt-6.1-sol"),
  /** claude, main reviewer / producer tier. */
  claudeMain: envModel("PAPERFORMALIZER_MODEL_CLAUDE_MAIN", "opus"),
} as const;
