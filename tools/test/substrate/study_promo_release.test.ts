// A study's promotion workspace and the study pipeline (`pipeline.ts`): released on this machine once
// the coordinate step ends for good, kept for a retry. The study runs the real pipeline with canned
// scaffolder / reviewer / build; its coordinate step's outcome is given (`SubstratePipelineDeps.coordinate`).
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { substrateLeanDir, substrateRunDir } from "../../src/substrate/paths.js";
import { runSubstratePipeline, type SubstratePipelineDeps } from "../../src/substrate/pipeline.js";
import { writeSkeleton } from "../toolkit/helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const REQUIREMENT = `# Substrate requirement

## Goal
A fact.

## Provides (API contract)
A theorem.

## Statement / milestones
True.

## Standard reference
Folklore.

## Intended reuse
Everywhere.

## May assume / must derive
Nothing.
`;

/** A study `slug` ready to run its pipeline through its coordinate step, whose outcome is `coordinate`'s. */
async function study(slug: string, coordinate: SubstratePipelineDeps["coordinate"]) {
  const root = await mkdtemp(path.join(os.tmpdir(), "study-promo-"));
  tmp.push(root);
  const cfg = await writeSkeleton(root);
  const runDir = substrateRunDir(root, slug);
  await mkdir(runDir, { recursive: true });
  await writeFile(path.join(runDir, "requirement.md"), REQUIREMENT);
  const leanDir = substrateLeanDir(root, slug, cfg.lib);
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "Main.lean"), `module\n\npublic import Mathlib.Tactic\n\ntheorem staged_${slug} : True := trivial\n`);
  const deps: SubstratePipelineDeps = {
    runScaffolder: async () => ({ decision: "review", plan_markdown: "plan", codex_prompts: [] }),
    runFillers: async () => [],
    buildTargets: async () => ({ ok: true, errors: [], sorryCount: 0, perFile: {} }),
    runReviewer: async () => ({
      pass: true, findings: "",
      checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true, documented: true },
    }),
    coordinate,
    writePlan: async () => {},
  };
  return { run: () => runSubstratePipeline({ toolkit: cfg, slug, resume: false }, deps) };
}

describe("a study's promotion workspace (2026-11-11)", () => {
  it("is released on this machine when the coordinate step ends for good (committed, refused), kept for a retry", async () => {
    for (const [last, phase] of [[{ ok: true, log: "committed" }, "done"], [{ ok: false, conflict: true, log: "refused" }, "escalated"]] as const) {
      const local = await mkdtemp(path.join(os.tmpdir(), "study-local-"));
      tmp.push(local);
      const promo = path.join(local, "ws", "study_alpha.promo");
      await mkdir(path.join(promo, "TC"), { recursive: true });
      const seen: boolean[] = [];
      const outcomes: Array<{ ok: boolean; log: string; conflict?: boolean }> = [{ ok: false, log: "the gate failed in the workspace" }, last];
      const alpha = await study("alpha", async () => { seen.push(existsSync(promo)); return outcomes.shift()!; });
      process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT = local;
      try {
        expect((await alpha.run()).phase).toBe(phase);
      } finally {
        delete process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
      }
      expect(seen, phase).toEqual([true, true]);
      expect(existsSync(promo), phase).toBe(false);
    }
  });
});
