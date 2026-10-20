import { describe, expect, it } from "vitest";
import { describeJsonSyntaxError } from "../../src/formalization/stage1.js";

describe("describeJsonSyntaxError", () => {
  it.each([
    // brackets inside strings are ignored
    ['{\n  "a": "x ] y",\n  "nodes": {\n    "n1": {"k": 1}\n  ],\n  "b": 2\n}', "opened `{` at line 3, closed by `]` at line 5"],
    ['{"a": [1, 2, {"b": "}"}]}', null],
    ['{"a": [1, 2', "unclosed `[` opened at line 1"],
  ])("describeJsonSyntaxError(%j) → %j", (text, expected) => {
    expect(describeJsonSyntaxError(text)).toBe(expected);
  });
});
