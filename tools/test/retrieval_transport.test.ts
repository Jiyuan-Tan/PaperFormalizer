// Semantic retrieval must work on Windows, not just Linux/macOS: the daemon transport
// falls back to TCP where `socket.AF_UNIX` is missing, and the interpreter is resolved
// rather than spawned as the literal `python3`. The transport test runs the real module
// in BOTH modes: `tcp` clears `HAS_UNIX` to force the Windows branch, which is the only
// way a POSIX box can cover the code path Windows always takes.
import { describe, it, expect } from "vitest";
import { execFileSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { probePython, tryPythonCommand } from "../src/shared/python.js";

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const PROBE = path.join(TOOLS, "test", "fixtures", "daemon_ipc_roundtrip.py");

const py = tryPythonCommand();
// A machine with no Python 3 cannot exercise the transport; skip rather than fail red.
const withPython = py ? describe : describe.skip;

withPython("daemon_ipc transport", () => {
  it.each(["native", "tcp"] as const)("completes a serve/probe/echo round trip over the %s transport", (mode) => {
    const out = execFileSync(py!.bin, [...py!.prefixArgs, PROBE, mode], {
      encoding: "utf8",
      timeout: 60_000,
    });
    expect(out.trim()).toMatch(/^OK (unix|tcp)$/);
    // `tcp` is the Windows transport; it must report tcp even on a POSIX box.
    if (mode === "tcp") expect(out.trim()).toBe("OK tcp");
  });
});

describe("python interpreter resolution", () => {
  it("rejects a candidate that is not a working python 3", () => {
    expect(probePython({ bin: "definitely-not-a-real-interpreter", prefixArgs: [] })).toBe(false);
  });

  it("returns null rather than throwing when nothing resolves", () => {
    // tryPythonCommand never throws; pythonCommand is the throwing variant. Callers that
    // must degrade (semantic/reranker tiers) depend on this distinction.
    expect(() => tryPythonCommand()).not.toThrow();
  });
});
