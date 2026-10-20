import { describe, expect, it } from "vitest";
import { FROM_STAGE_USAGE } from "../../src/constants.js";
import { deriveVerifyQid, parseVerifyArgsForTest, USAGE } from "../../src/verify/cli.js";
import { dryRunLeftover } from "../../src/verify/dry_run.js";

const parse = parseVerifyArgsForTest;

describe("theoremchecker verify argument parsing", () => {
  it("parses a bare input", () => {
    expect(parse(["paper.tex"])).toEqual({
      input: "paper.tex",
      toolkit: null,
      slug: null,
      main: null,
      targets: null,
      resume: false,
      fromStage: null,
      stopAfter: null,
      clearGates: [],
      freshReview: false,
      fromTranscript: false,
      rejectRewind: null,
      clearPatchCap: false,
      acceptCap: false,
      acceptRepair: false,
      declineRepair: null,
      redoRepair: null,
      rejectFinding: null,
      addCondition: null,
      editReading: null,
      removeReading: null,
      umbrella: null,
      auto: false,
      fullAuto: false,
      deferProposals: false,
      dryRun: false,
      stop: false,
    });
  });

  it("parses the answers to the orchestrator's halts: each needs --resume, one at a time, never with --from-stage", () => {
    expect(parse(["paper.tex", "--resume", "--reject-rewind", "Assumption 3 grants it"])).toMatchObject({ rejectRewind: "Assumption 3 grants it", clearPatchCap: false, acceptCap: false });
    expect(parse(["paper.tex", "--resume", "--clear-patch-cap"])).toMatchObject({ clearPatchCap: true });
    expect(parse(["paper.tex", "--resume", "--accept-cap"])).toMatchObject({ acceptCap: true });
    expect(parse(["paper.tex", "--resume", "--accept-repair"])).toMatchObject({ acceptRepair: true, declineRepair: null });
    expect(parse(["paper.tex", "--resume", "--reject-finding", "the probability is conditional on the training sample"])).toMatchObject({ rejectFinding: ["the probability is conditional on the training sample"], declineRepair: null });
    // repeatable: one answer per node
    expect(parse(["paper.tex", "--resume", "--reject-finding", "thm:a: r", "--reject-finding", "prop:b: bookkeeping: m is not identically zero"])).toMatchObject({ rejectFinding: ["thm:a: r", "prop:b: bookkeeping: m is not identically zero"] });
    expect(() => parse(["paper.tex", "--reject-finding", "x"])).toThrow(/requires --resume/);
    // an owner reading on record, reworded or removed by its id: repeatable, and the two combine
    expect(parse(["paper.tex", "--resume", "--edit-reading", "ass:pin-owner-2: the constants depend only on $c$", "--edit-reading", "ass:bk-owner-1: - is read as minus", "--remove-reading", "ass:pin-owner-3"])).toMatchObject({
      editReading: ["ass:pin-owner-2: the constants depend only on $c$", "ass:bk-owner-1: - is read as minus"],
      removeReading: ["ass:pin-owner-3"],
    });
    expect(() => parse(["paper.tex", "--remove-reading", "ass:pin-owner-3"])).toThrow(/requires --resume/);
    expect(() => parse(["paper.tex", "--resume", "--remove-reading", "thm:a"])).toThrow(/--remove-reading requires an owner reading's id/);
    expect(() => parse(["paper.tex", "--resume", "--remove-reading", "ass:pin-3"])).toThrow(/--remove-reading requires an owner reading's id/);
    expect(() => parse(["paper.tex", "--resume", "--edit-reading", "ass:pin-owner-2:  "])).toThrow(/--edit-reading requires "<id>: <new text>"/);
    expect(() => parse(["paper.tex", "--resume", "--edit-reading", "thm:a: text"])).toThrow(/--edit-reading requires/);
    expect(() => parse(["paper.tex", "--resume", "--remove-reading", "ass:pin-owner-3", "--accept-cap"])).toThrow(/give one/);
    expect(() => parse(["paper.tex", "--resume", "--from-stage", "V1.5", "--remove-reading", "ass:pin-owner-3"])).toThrow(/does not combine with --from-stage/);
    expect(parse(["paper.tex", "--resume", "--decline-repair", "the weaker limit is not the point"])).toMatchObject({ declineRepair: "the weaker limit is not the point", acceptRepair: false });
    expect(() => parse(["paper.tex", "--accept-repair"])).toThrow(/requires --resume/);
    expect(() => parse(["paper.tex", "--resume", "--accept-repair", "--decline-repair", "r"])).toThrow(/give one/);
    // item by item in one resume: node-scoped receipt answers combine; a bare one covers the rest
    expect(parse(["paper.tex", "--resume", "--accept-repair", "thm:local", "--redo-repair", "thm:local-local-clause: keep Gaussian kernels"])).toMatchObject({
      acceptRepair: ["thm:local"],
      redoRepair: ["thm:local-local-clause: keep Gaussian kernels"],
    });
    expect(parse(["--resume", "--accept-repair", "thm:a,lem:b", "paper.tex"])).toMatchObject({ acceptRepair: ["thm:a", "lem:b"], input: "paper.tex" });
    expect(parse(["--resume", "--accept-repair", "paper.tex"])).toMatchObject({ acceptRepair: true, input: "paper.tex" });
    expect(parse(["paper.tex", "--resume", "--accept-repair", "--redo-repair", "thm:b: g", "--redo-repair", "thm:c: h"])).toMatchObject({ acceptRepair: true, redoRepair: ["thm:b: g", "thm:c: h"] });
    expect(parse(["paper.tex", "--resume", "--accept-repair", "thm:a", "--decline-repair", "thm:b: not the point"])).toMatchObject({ acceptRepair: ["thm:a"], declineRepair: "thm:b: not the point" });
    expect(() => parse(["paper.tex", "--redo-repair", "thm:b: g"])).toThrow(/requires --resume/);
    expect(() => parse(["paper.tex", "--resume", "--redo-repair", "thm:b: g", "--accept-cap"])).toThrow(/give one/);
    expect(() => parse(["paper.tex", "--clear-patch-cap"])).toThrow(/requires --resume/);
    expect(() => parse(["paper.tex", "--reject-rewind", "r"])).toThrow(/requires --resume/);
    expect(() => parse(["paper.tex", "--resume", "--accept-cap", "--clear-patch-cap"])).toThrow(/give one/);
    expect(() => parse(["paper.tex", "--resume", "--accept-cap", "--from-stage", "F2"])).toThrow(/--from-stage/);
    expect(() => parse(["paper.tex", "--resume", "--reject-rewind"])).toThrow(/requires a value/);
  });

  it("parses every option", () => {
    expect(
      parse([
        "/papers/draft",
        "--toolkit",
        "/home/me/tk",
        "--clear-gate",
        "proof_loop_cap_hit",
        "--clear-gate",
        "general_review_halt",
        "--slug",
        "my_run",
        "--from-stage",
        "F2.5",
        "--stop-after",
        "F4",
        "--resume",
        "--auto",
        "--defer-proposals",
        "--dry-run",
      ]),
    ).toEqual({
      input: "/papers/draft",
      toolkit: "/home/me/tk",
      slug: "my_run",
      main: null,
      targets: null,
      resume: true,
      fromStage: "F2.5",
      stopAfter: "F4",
      clearGates: ["proof_loop_cap_hit", "general_review_halt"],
      freshReview: false,
      fromTranscript: false,
      rejectRewind: null,
      clearPatchCap: false,
      acceptCap: false,
      acceptRepair: false,
      declineRepair: null,
      redoRepair: null,
      rejectFinding: null,
      addCondition: null,
      editReading: null,
      removeReading: null,
      umbrella: null,
      auto: true,
      fullAuto: false,
      deferProposals: true,
      dryRun: true,
      stop: false,
    });
  });

  it("--main is a cold start's; --targets a cold start's or --from-stage V1's (the new transcription takes the scope), never a plain --resume's", () => {
    expect(parse(["/papers/draft", "--main", "tex/main.tex", "--targets", "thm:main, thm:aux ,"])).toMatchObject({ main: "tex/main.tex", targets: ["thm:main", "thm:aux"] });
    expect(parse(["paper.tex", "--from-stage", "V1", "--targets", "thm:main"])).toMatchObject({ fromStage: "V1", targets: ["thm:main"] });
    expect(() => parse(["paper.tex", "--resume", "--targets", "thm:main"])).toThrow(/--targets sets the scope .* --from-stage V1, not with a plain --resume/);
    expect(() => parse(["paper.tex", "--from-stage", "V1.5", "--targets", "thm:main"])).toThrow(/--targets sets the scope/);
    expect(() => parse(["paper.tex", "--resume", "--main", "tex/main.tex"])).toThrow(/--main names the main file of a new run/);
    expect(() => parse(["paper.tex", "--from-stage", "V1", "--main", "tex/main.tex"])).toThrow(/--main names the main file of a new run/);
  });


  it.each([
    [[], /Missing <paper\.tex\|dir\|archive>/],
    [["a.tex", "b.tex"], /Unexpected argument: b\.tex/],
    [["paper.tex", "--main", "--auto"], /--main requires a value/],
    [["paper.tex", "--slug", "a", "--slug", "b"], /--slug given more than once/],
    [["paper.tex", "--targets", " , "], /--targets is empty/],
    [["paper.tex", "--from-stage", "V2"], /not a verify stage/],
    [["paper.tex", "--from-stage", "F1", "--fresh-review"], /--fresh-review needs --from-stage V1 or V1\.5/],
  ] as Array<[string[], RegExp]>)("rejects %j", (argv, err) => {
    expect(() => parse(argv)).toThrow(err);
  });

  it("validates --stop-after: a verify stage, not before --from-stage, never F2.5/F3/F3.5 (naming F2 and F4)", () => {
    expect(parse(["paper.tex", "--stop-after", "V1.5"]).stopAfter).toBe("V1.5");
    expect(() => parse(["paper.tex", "--stop-after", "D0"])).toThrow(/not a verify stage/);
    expect(() => parse(["paper.tex", "--from-stage", "F2", "--stop-after", "F1"])).toThrow(/precedes --from-stage/);
    for (const s of ["F2.5", "F3", "F3.5"]) {
      expect(() => parse(["paper.tex", "--stop-after", s])).toThrow(/can never fire[\s\S]*--stop-after F2 \(halt before[\s\S]*F4/);
    }
  });

  it("refuses --from-stage F3/F3.5/F4, naming the stages a rewind can start at", () => {
    for (const s of ["F3", "F3.5", "F4"]) {
      expect(() => parse(["paper.tex", "--resume", "--from-stage", s])).toThrow(/not an entry point[\s\S]*V1\|V1\.5\|F1\|F1\.5\|F2\|F2\.5\|F5\|V6[\s\S]*--from-stage F2\.5/);
    }
    expect(parse(["paper.tex", "--resume", "--from-stage", "F2.5"]).fromStage).toBe("F2.5");
  });

  it("the usage line lists the stages each flag takes, from the lists the refusals use", () => {
    expect(USAGE).toContain("--from-stage <stage> ∈ V1|V1.5|F1|F1.5|F2|F2.5|F5|V6; --stop-after <stage> ∈ V1|V1.5|F1|F1.5|F2|F4|F5|V6");
    for (const s of ["F3", "F3.5", "F4"]) expect(() => parse(["paper.tex", "--resume", "--from-stage", s])).toThrow(FROM_STAGE_USAGE);
  });

  it("a dry run ends by naming the directory it left, to delete", () => {
    expect(dryRunLeftover("/tk/runs/smoke")).toMatch(/dry run: it wrote \/tk\/runs\/smoke .* delete the directory/);
  });

  it("requires --resume for --clear-gate", () => {
    expect(() => parse(["paper.tex", "--clear-gate", "proof_loop_cap_hit"])).toThrow(/--clear-gate requires --resume/);
  });
});

describe("verify run id (the plain slug)", () => {
  it("slugifies the input basename, prefers an explicit --slug, caps the length", () => {
    expect(deriveVerifyQid("/papers/My Paper (v2).tex", null)).toBe("my_paper_v2");
    expect(deriveVerifyQid("/papers/bundle/", null)).toBe("bundle");
    expect(deriveVerifyQid("/papers/whatever.tex", "AteBounds")).toBe("atebounds");
    expect(deriveVerifyQid(`${"a".repeat(80)}.tex`, null)).toBe("a".repeat(40));
  });

  it("never lets a path escape the run root", () => {
    // Separators and dots are slugified away, so the qid stays one path segment.
    expect(deriveVerifyQid("x.tex", "../../etc/passwd")).toBe("etc_passwd");
    expect(() => deriveVerifyQid("/papers/....", null)).toThrow(/Cannot derive a run slug/);
    expect(() => deriveVerifyQid("x.tex", "!!!")).toThrow(/Cannot derive a run slug/);
  });
});
