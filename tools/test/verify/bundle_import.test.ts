import { execFileSync } from "node:child_process";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { describe, expect, it } from "vitest";

// Loaded first in a plain Node process, as `leansmith report` loads it (vitest's own module
// loader hides an import cycle): the bundle reaches the page model, which reads a run's share record
// through `share_record.ts`, never `share.ts`, which needs the bundle loaded.
describe("bundle module", () => {
  it("loads first without a cycle through the share command", () => {
    const tools = path.resolve(__dirname, "../..");
    const out = execFileSync(process.execPath, ["--import", "tsx", "--input-type=module", "-e", `const m = await import(${JSON.stringify(pathToFileURL(path.join(tools, "src/verify/bundle.ts")).href)}); console.log(m.PAPER_DIR);`], { cwd: tools, encoding: "utf8" });
    expect(out.trim()).toBe("corrected_paper");
  }, 60_000);
});
