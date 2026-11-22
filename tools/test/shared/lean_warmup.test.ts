// The cold-start guard reads what is on disk only: no build, no lock, no wait. A toolkit never
// built, a dependency checkout missing (a node whose package cache was never synced) or Mathlib
// unbuilt is cold; a required package that nothing imports (unbuilt) is not.
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readdir, rm, symlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { coldLakeParts, LEANLSP_WARMUP_ENV, warmUpLeanOrThrow } from "../../src/shared/lean_warmup.js";

let root: string;
const mk = (rel: string) => mkdir(path.join(root, rel), { recursive: true });
beforeEach(async () => {
  root = await mkdtemp(path.join(os.tmpdir(), "warmup-"));
  await mk("tk/.lake/build/lib/lean");
  await mk("tk/.lake/packages/mathlib/.lake/build/lib/lean");
  await mk("tk/.lake/packages/checkdecls");
  await mk("dep/.lake/build/lib/lean");
  await writeFile(path.join(root, "tk", "lake-manifest.json"), JSON.stringify({
    packagesDir: ".lake/packages",
    packages: [{ type: "path", name: "Dep", dir: "../dep" }, { type: "git", name: "mathlib" }, { type: "git", name: "checkdecls" }],
  }));
});
afterEach(async () => {
  delete process.env[LEANLSP_WARMUP_ENV];
  await rm(root, { recursive: true, force: true });
});

describe("warmUpLeanOrThrow", () => {
  it("passes a warm toolkit and writes nothing", async () => {
    const tk = path.join(root, "tk");
    const before = await readdir(tk, { recursive: true });
    await warmUpLeanOrThrow(tk, "verify");
    expect(await readdir(tk, { recursive: true })).toEqual(before);
    expect(existsSync(path.join(tk, ".lake-build.lock"))).toBe(false);
  });

  it("throws on a cold one: never built, a dangling dependency link, Mathlib unbuilt", async () => {
    const tk = path.join(root, "tk");
    await rm(path.join(root, "tk/.lake/packages/checkdecls"), { recursive: true });
    await symlink(path.join(root, "nowhere"), path.join(root, "tk/.lake/packages/checkdecls"));
    await rm(path.join(root, "tk/.lake/packages/mathlib/.lake"), { recursive: true });
    await rm(path.join(root, "tk/.lake/build"), { recursive: true });
    expect(coldLakeParts(tk)).toEqual([
      `the toolkit's own build (${path.join(tk, ".lake", "build")})`,
      `Mathlib's build (${path.join(tk, ".lake/packages/mathlib/.lake/build")})`,
      `dependency checkdecls (${path.join(tk, ".lake/packages/checkdecls")})`,
    ]);
    await expect(warmUpLeanOrThrow(tk, "study")).rejects.toThrow(/COLD — missing the toolkit's own build/);
    process.env[LEANLSP_WARMUP_ENV] = "0";
    await warmUpLeanOrThrow(tk, "study");
    process.env[LEANLSP_WARMUP_ENV] = "ten";
    await expect(warmUpLeanOrThrow(tk, "study")).rejects.toThrow(/Invalid/);
  });
});
