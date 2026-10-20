import { readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";

const prompt = readFileSync(join(process.cwd(), "src/verify/prompts/V1.5/review.txt"), "utf8").replace(/\r\n/g, "\n");

describe("V1.5 referee prompt", () => {
  it("pins a reading of an assumption's phrase on the assumption, so every user carries it (live drdid: a sampling reading pinned on one result left its siblings' reviewers asking again)", () => {
    expect(prompt).toContain("names that node in the reading's\n                `of`: it then binds every result using it");
  });
  it("a statement that defers its conditions to other results is read as those results state it — an error only where none of them proves a conclusion", () => {
    const flat = prompt.replace(/\s+/g, " ");
    expect(flat).toContain("each of its conclusions holds under the conditions of the referenced result that proves it, in the cases that result covers");
    expect(flat).toContain("an `error` only where a conclusion is proved by no referenced result under any conditions they give, or contradicts one");
    expect(flat).toContain("a referenced result's own defect is graded on that result");
  });
});
