// Fixture: a CLI-less runner for child_registry.test.ts. Installs the stop handlers, records
// children to <outDir>/children.json and spawns a long-lived fake worker, then waits to be
// signalled. Run as a STANDALONE node process: signal handlers and process.exit must not touch
// the vitest worker.
//
// argv[2] = mode: "group"    one detached `bash` whose background `sleep` stays in its group
//                 "setsid"   the `sleep` leaves the group (setsid), like a self-detaching worker
//                 "maplimit" three such workers through mapLimit at concurrency 1
// argv[3] = outDir: grandchild pids go to grandchild.pid, started items to started.txt,
//           handler log lines to log.txt.
import { appendFileSync } from "node:fs";
import path from "node:path";
import { installStopHandlers, setChildrenFile } from "../../src/shared/child_registry.js";
import { mapLimit } from "../../src/formalization/reviewer_verdicts.js";
import { spawnWithInactivityTimeout } from "../../src/workers/spawn.js";

const mode = process.argv[2] ?? "group";
const outDir = process.argv[3]!;
installStopHandlers({
  log: (line) => {
    appendFileSync(path.join(outDir, "log.txt"), `${line}\n`);
    console.error(line);
  },
});
setChildrenFile(path.join(outDir, "children.json"));

const pidFile = path.join(outDir, "grandchild.pid");
const worker = (tag: string) =>
  spawnWithInactivityTimeout(
    "bash",
    ["-c", `${mode === "setsid" ? "setsid " : ""}sleep 300 & echo $! >> '${pidFile}'; wait`],
    { inactivityTimeoutMs: 600_000, child: { kind: "fake-codex", tag } },
  );

if (mode === "maplimit") {
  await mapLimit([0, 1, 2], 1, async (i) => {
    appendFileSync(path.join(outDir, "started.txt"), `${i}\n`);
    return await worker(`item${i}`);
  });
} else {
  await worker("t1");
}
appendFileSync(path.join(outDir, "log.txt"), "harness: workers returned (unexpected)\n");
