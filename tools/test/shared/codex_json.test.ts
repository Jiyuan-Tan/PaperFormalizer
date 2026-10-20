import { describe, expect, it, beforeEach, afterEach } from "vitest";
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path, { join } from "node:path";
import { fileURLToPath } from "node:url";
import {
  expectStringJsonOutput,
  parseJsonWithEscapeRepair,
  persistCodexRaw,
  repairInvalidStringEscapes,
  tryBraceBalanceRepair,
} from "../../src/shared/codex_json.js";
import { extractJsonObject } from "../../src/judgment.js";

let tmp: string;
beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "cs-codex-json-"));
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("expectStringJsonOutput", () => {
  it("returns the FIRST balanced object when codex double-emits", () => {
    // Failure mode observed in research pipeline: codex emits a pretty-printed
    // object followed by a compact restatement. Previous behavior: first-{/last-}
    // slice produced the concatenation, which JSON.parse rejects.
    const double = '{"a":1,"b":[2,3]}\n{"a":1,"b":[2,3]}';
    expect(expectStringJsonOutput(double)).toEqual({ a: 1, b: [2, 3] });
  });

  it("repairs a 1-char truncation (missing outer })", () => {
    const truncated = '{"insight":{"id":"x","theorems":[{"t":1}]}';
    expect(expectStringJsonOutput(truncated)).toEqual({
      insight: { id: "x", theorems: [{ t: 1 }] },
    });
  });

  it("tags unrepairable parse failures with code codex_malformed_output", () => {
    try {
      expectStringJsonOutput('{"a": "uncl');
      throw new Error("expected throw");
    } catch (err: unknown) {
      expect((err as { code?: string }).code).toBe("codex_malformed_output");
    }
  });

  it("does NOT repair inputs missing more than 3 closers (likely structural)", () => {
    const tooBroken = "{".repeat(5) + '"a":1';
    expect(tryBraceBalanceRepair(tooBroken)).toBeNull();
  });

  it("parses every captured model emission", () => {
    // Captured real emissions (one carried raw LaTeX that killed a finished verdict).
    const dir = fileURLToPath(new URL("../fixtures/model_emissions", import.meta.url));
    const files = readdirSync(dir).filter((f) => f.endsWith(".txt"));
    expect(files.length, "no fixtures captured").toBeGreaterThan(0);
    for (const f of files) {
      expect(() => expectStringJsonOutput(readFileSync(`${dir}/${f}`, "utf8")), `failed to parse ${f}`).not.toThrow();
    }
  });
});

describe("persistCodexRaw", () => {
  it("writes the raw payload under codex_raw/", async () => {
    const written = await persistCodexRaw(tmp, "passA", "any stdout bytes");
    expect(written).not.toBeNull();
    expect(existsSync(written!)).toBe(true);
    expect(readFileSync(written!, "utf8")).toBe("any stdout bytes");
    const entries = readdirSync(path.join(tmp, "codex_raw"));
    expect(entries.length).toBe(1);
    expect(entries[0]).toMatch(/^passA__/);
  });
});

describe("repairInvalidStringEscapes", () => {
  it("repairs LaTeX inline math inside a string", () => {
    const raw = String.raw`{"critique":"shells \(q_d(P)=r_n\), with the converse"}`;
    const fixed = repairInvalidStringEscapes(raw)!;
    expect(JSON.parse(fixed).critique).toBe(String.raw`shells \(q_d(P)=r_n\), with the converse`);
  });

  it.each([
    ["an already-escaped backslash", String.raw`{"critique":"c_G \\le 3/16"}`],
    ["a genuine \\uXXXX escape", String.raw`{"s":"\u00e9"}`],
    ["backslash-free structure", `{"a":1}`],
  ])("leaves %s alone", (_label, raw) => {
    expect(repairInvalidStringEscapes(raw)).toBeNull();
  });

  it("cannot change structure — only string contents", () => {
    // A repair that could alter structure might make a parse succeed DIFFERENTLY,
    // which is worse than failing.
    const raw = String.raw`{"a":"\(","b":[1,2],"c":{"d":"\)"}}`;
    const parsed = JSON.parse(repairInvalidStringEscapes(raw)!);
    expect(parsed.b).toEqual([1, 2]);
    expect(parsed.c.d).toBe("\\)");
    expect(Object.keys(parsed)).toEqual(["a", "b", "c"]);
  });
});

describe("the repair is a strict extension of JSON.parse", () => {
  // The repair fires ONLY on bytes JSON.parse already rejects, so on anything that parsed
  // before (including F-stage payloads that embed Lean source) it must be a no-op.
  it("is identical to JSON.parse on already-valid payloads", () => {
    const valid = [
      String.raw`{"a":"plain"}`,
      String.raw`{"tex":"\\alpha + \\beta"}`,
      String.raw`{"multi":"line one\nline two\ttabbed"}`,
      String.raw`{"unicode":"\u00e9 caf\u00e9"}`,
      String.raw`{"path":"C:\\Users\\x"}`,
      String.raw`{"nested":{"arr":[1,2,{"k":"\\frac{1}{2}"}]}}`,
      String.raw`{"quoted":"he said \"hi\""}`,
      String.raw`{"solidus":"a\/b"}`,
    ];
    for (const v of valid) {
      expect(parseJsonWithEscapeRepair(v), `changed under repair: ${v}`).toEqual(JSON.parse(v));
      expect(extractJsonObject(v), `changed under funnel: ${v}`).toEqual(JSON.parse(v));
    }
  });

  it("is idempotent on a repaired payload", () => {
    const raw = String.raw`{"critique":"bound \(d/\epsilon\)"}`;
    const once = extractJsonObject(raw);
    expect(extractJsonObject(JSON.stringify(once))).toEqual(once);
  });
});

describe("source guard — no bare JSON.parse at a model-output boundary", () => {
  const srcDir = fileURLToPath(new URL("../../src", import.meta.url));
  const binDir = fileURLToPath(new URL("../../bin", import.meta.url));
  // A call site is only safe if the escape defense is visible ON that expression.
  const DEFENSES = [
    "parseJsonWithEscapeRepair",
    "normalizeRawModelJson",
    "readTypedCore",
    "repairInvalidStringEscapes",
    "extractJsonObject",
    "expectStringJsonOutput",
    "parseJsonLoose",
  ];
  // Expressions that identify a MODEL-authored source: agent stdout, or a file an agent
  // wrote itself. Pipeline-written state (state.json, caches, stores) is deliberately
  // excluded — those are re-serialized by us and fail loud by design.
  const MODEL_SOURCES = [
    /\bstdout\b/,
    /\bout\.stdout\b/,
    /paths\.plan\b/,
    /\bplanPath\b/,
    /\bverdictFile\b/,
    // No leading \b: these appear as suffixes of longer identifiers (`absoluteSolvePath`).
    /SolvePath\b/,
    /solveJsonPath\b/,
  ];

  const walk = (dir: string): string[] =>
    readdirSync(dir).flatMap((name) => {
      const p = join(dir, name);
      return statSync(p).isDirectory() ? walk(p) : p.endsWith(".ts") ? [p] : [];
    });

  it("has no unguarded JSON.parse over agent stdout or an agent-written plan", () => {
    const offenders: string[] = [];
    for (const file of [...walk(srcDir), ...walk(binDir)]) {
      readFileSync(file, "utf8").split("\n").forEach((line, i) => {
        if (!line.includes("JSON.parse(")) return;
        if (!MODEL_SOURCES.some((re) => re.test(line))) return;
        if (DEFENSES.some((d) => line.includes(d))) return;
        const rel = file.startsWith(srcDir) ? `src/${file.slice(srcDir.length + 1)}` : `bin/${file.slice(binDir.length + 1)}`;
        offenders.push(`${rel}:${i + 1}: ${line.trim()}`);
      });
    }
    expect(
      offenders,
      "Model-authored JSON must go through the escape defense — a raw LaTeX backslash " +
        "otherwise kills the whole payload. Wrap the read in parseJsonWithEscapeRepair (any " +
        "model output) or normalizeRawModelJson (known-TeX D-stage boundaries).",
    ).toEqual([]);
  });
});
