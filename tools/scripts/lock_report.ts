// Wait and hold of a toolkit's Lake build lock and promotion lock, per day, from the hold records
// (`src/shared/lock_holds.ts`): the Lake lock's shared and exclusive holds, and how many held it at
// once (peak, and mean while held); and the commits that landed off their base or were refused for
// a file of their read set (`commit.ts`, I1′). Read-only.
//
//   npx tsx scripts/lock_report.ts <toolkit> [days back, default 7] [--json]
import process from "node:process";
import { formatLockSummary, readCommitEvents, readLockHolds, summarizeCommitEvents, summarizeLockHolds } from "../src/shared/lock_holds.js";

const [toolkit, daysArg] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
if (!toolkit) {
  console.error("usage: npx tsx scripts/lock_report.ts <toolkit> [days back] [--json]");
  process.exit(2);
}
const since = new Date(Date.now() - Number(daysArg ?? 7) * 86_400_000).toISOString().slice(0, 10);
const rows = summarizeLockHolds(await readLockHolds(toolkit, since));
const commits = summarizeCommitEvents(await readCommitEvents(toolkit, since));
if (process.argv.includes("--json")) console.log(JSON.stringify({ holds: rows, commits }, null, 2));
else {
  console.log(formatLockSummary(rows) || "no hold recorded");
  for (const c of commits) console.log(`${c.day} commits: ${c.offBase} landed off their base, ${c.readsMiss} refused for a read-set file; ${c.additive} additive landed on a later generation, ${c.additiveMiss} refused there`);
}
