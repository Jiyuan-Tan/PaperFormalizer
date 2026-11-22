// The run slug `paperformalizer verify --slug <s>` creates its run under (`deriveVerifyQid`,
// src/verify/cli.ts): lowercased, each run of non-[a-z0-9] → "_", "_" trimmed, capped at
// VERIFY_SLUG_MAX (40), trailing "_" trimmed. The batch driver follows a queue entry under this
// name, never the entry's own spelling (2026-11-10: a 41-character entry was started, its run
// created 40 characters long, and the driver — waiting for runs/<41 characters>/ — let it go;
// the run stopped at its first checkpoint with no orchestrator). Kept equal by its test.
export const RUN_SLUG_MAX = 40;
export const runSlug = (s) => s.toLowerCase().replace(/[^a-z0-9]+/g, "_").replace(/^_+|_+$/g, "").slice(0, RUN_SLUG_MAX).replace(/_+$/, "");
