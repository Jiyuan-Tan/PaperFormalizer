import { mkdtemp, mkdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { shareableOf } from "../../src/verify/share_record.js";

describe("shareableOf", () => {
  it("a bundle is offered for sharing only with its seal and no blocking item; else the reason", async () => {
    const run = await mkdtemp(path.join(os.tmpdir(), "tc-shareable-"));
    expect(await shareableOf(run)).toEqual({ ok: false, reason: "the run has no bundle yet" });
    await mkdir(path.join(run, "bundle"));
    await writeFile(path.join(run, "bundle", "bundle.json"), JSON.stringify({ todo: { total: 4, blocking: 3 } }));
    expect((await shareableOf(run)).reason).toMatch(/no seal/u);
    await writeFile(path.join(run, "bundle", "f4_seal.json"), "{}");
    expect(await shareableOf(run)).toEqual({ ok: false, reason: "3 blocking items in corrected_paper/TODO.md" });
    await writeFile(path.join(run, "bundle", "bundle.json"), JSON.stringify({ todo: { total: 1, blocking: 0 } }));
    expect(await shareableOf(run)).toEqual({ ok: true });
  });
});
