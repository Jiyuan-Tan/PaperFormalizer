import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";

describe("sync_viewer.mjs: the viewer copied into the registry", () => {
  it("carries each third-party library with its license (their licenses require the notice in every copy)", () => {
    const registry = mkdtempSync(path.join(tmpdir(), "tc-sync-viewer-"));
    // a registry is the folder holding site/build.mjs
    mkdirSync(path.join(registry, "site"));
    writeFileSync(path.join(registry, "site", "build.mjs"), "");
    execFileSync(process.execPath, [path.join(__dirname, "..", "..", "scripts", "sync_viewer.mjs"), registry], { stdio: "pipe" });
    const viewer = path.join(registry, "site", "viewer");
    for (const f of ["purify.min.js", "katex/katex.min.js", "pdfjs/pdf.min.mjs"]) expect(existsSync(path.join(viewer, f))).toBe(true);
    expect(readFileSync(path.join(viewer, "purify.LICENSE"), "utf8")).toContain("Apache License");
    expect(readFileSync(path.join(viewer, "katex", "LICENSE"), "utf8")).toContain("MIT License");
    expect(readFileSync(path.join(viewer, "pdfjs", "LICENSE"), "utf8")).toContain("Apache License");
  }, 60_000);
});
