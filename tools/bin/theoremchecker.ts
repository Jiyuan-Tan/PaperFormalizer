#!/usr/bin/env node
import process from "node:process";
import { fileURLToPath } from "node:url";
import { FROM_STAGE_USAGE, STOP_AFTER_USAGE, STUDY_SYNOPSIS } from "../src/constants.js";
import { applyWorkerEnv } from "../src/local_config.js";
import { applyAuthEnv, authSummary } from "../src/auth.js";
import { installStopHandlers } from "../src/shared/child_registry.js";

export type TheoremCheckerMode = "doctor" | "init" | "demo" | "ui" | "verify" | "propose" | "study" | "toolkit-health" | "garden" | "docstrings" | "annotate" | "lint-annotated" | "report" | "seal" | "share" | "relink";

export const THEOREMCHECKER_USAGE =
  "Usage: theoremchecker <doctor|init|demo|ui|verify|propose|study|toolkit-health|garden|docstrings|annotate|lint-annotated|report|seal|share|relink> <args...>\n" +
  "  theoremchecker doctor\n" +
  "      check this machine's prerequisites (programs, versions, logins) and print how to get what is missing\n" +
  "  theoremchecker init <dir> [--domains id,id] [--libraries name,name] [--owner \"Name\"] [--email e] [--no-build]\n" +
  "      create a personal toolkit (template, chosen domain libraries, git repo, Mathlib cache, build); --list prints the choices\n" +
  "  theoremchecker demo [--dir <path>] [--port N] [--open] [--restart]\n" +
  "      a guided tour of a run on the page, for a first-time user (recorded: no model, no Lean, no account)\n" +
  "  theoremchecker ui [--toolkit <path>] [--port N] [--open] [--new]\n" +
  "      the local web UI (127.0.0.1 only): toolkit, library, and each paper's run, live; decisions run the CLI\n" +
  "  theoremchecker verify <paper.tex|dir|archive> [--toolkit <path>] [--slug s] [--main relpath]\n" +
  "                        [--targets label,label] [--resume] [--from-stage <stage>] [--fresh-review] [--from-transcript]\n" +
  "                        [--stop-after <stage>] [--clear-gate <flag>]... [--defer-proposals] [--auto] [--full-auto] [--dry-run]\n" +
  "                        answering a halt (each with --resume): [--reject-rewind \"<reason>\"] [--clear-patch-cap] [--accept-cap]\n" +
  "                        [--accept-repair [<node>,…]] [--decline-repair \"[<node>,…: ]<reason>\"] [--redo-repair \"<node>: <guidance>\"]...\n" +
  "                        [--reject-finding \"[<node>: [bookkeeping: ]]<reading>\"]... [--add-condition \"<node>: <condition>\"]...\n" +
  "                        [--edit-reading \"<id>: <new text>\"]... [--remove-reading <id>]... [--umbrella <node>]...\n" +
  "  theoremchecker verify --stop --slug <s> [--toolkit <path>]\n" +
  "      stop a run: its live runner and the codex/claude/lake children recorded in logs/children.json\n" +
  `      --from-stage ∈ ${FROM_STAGE_USAGE}; --stop-after ∈ ${STOP_AFTER_USAGE}; the run id is the slug (--slug, else the file name);\n` +
  "      `theoremchecker verify` alone prints what each flag does\n" +
  "  theoremchecker propose <slug> [--round A|B] [--apply [--recommended] | --reopen-deferred] [--toolkit <path>] [--dry-run]\n" +
  "      a toolkit promotion round (A: cited results after F1; B: proved results after the report):\n" +
  "      re-render the checklist, --apply the owner's decisions (--recommended: the agent's recommendations), or re-propose the entries deferred in round B\n" +
  `  ${STUDY_SYNOPSIS}\n` +
  "      build a proved, reviewed toolkit module from runs/study_<slug>/requirement.md\n" +
  "  theoremchecker toolkit-health [--toolkit <path>] [--all] [--json] [--no-rebuild]\n" +
  "      re-derive doc/toolkit_graph.json from the Lean and report the toolkit's health and reuse trend\n" +
  "  theoremchecker garden [--toolkit <path>] [--no-rebuild] [--dry-run] [--verify <garden-….md> [--items g-1,…]]\n" +
  "      gardening suggestions from the toolkit's graph (the orchestrator decides each), or --verify the accepted items carried out by hand\n" +
  "  theoremchecker docstrings [--toolkit <path>] [--modules M1,M2]\n" +
  "      bring the toolkit's docstrings to the docstring contract (NL translation + crosslinks); docstring edits only\n" +
  "  theoremchecker annotate <slug> [--toolkit <path>] [--compile-record <path>]\n" +
  "      rewrite the run's annotated paper as it stands (no model call); exits non-zero on a block that could not be set as TeX\n" +
  "  theoremchecker lint-annotated <slug> [--toolkit <path>]\n" +
  "      check the annotated paper as written (escaped TeX, code points, odd $ in a block, pdflatex errors)\n" +
  "  theoremchecker report <slug> [--toolkit <path>] [--out <dir>] [--verify-public] [--arxiv <id>]\n" +
  "      write the run's report and corrected-paper bundle again from its records (no stage, no model call, no lake)\n" +
  "  theoremchecker relink <slug> [--toolkit <path>] [--only <node>,…] [--fresh]\n" +
  "      link the run's results to their Lean statements row by row again (F5's link step alone; calls its model)\n" +
  "  theoremchecker seal <bundle dir | f4_seal.json>\n" +
  "      check a bundle's F4 seal: its code is its own, and both reviewers passed every statement target, the files beside it are the ones it was written with (no toolkit, no model call, no lake)\n" +
  "  theoremchecker share <slug> [--toolkit <path>] [--dry-run]\n" +
  "      publish the finished run's bundle (the corrected paper's TeX source and PDF, the findings, the Lean code, the report)\n" +
  "      on the public site of shared papers; it shows what is sent, sends only after you type the slug at a terminal, then you sign in to GitHub in your browser and confirm (no model call, no lake)\n" +
  "  The toolkit is --toolkit <path>, else THEOREMCHECKER_TOOLKIT, else the nearest ancestor of the cwd\n" +
  "  holding theoremchecker.json.";

export function parseTheoremCheckerCommand(argv: string[]): { mode: TheoremCheckerMode; args: string[] } {
  const [mode, ...args] = argv;
  if (mode === "doctor" || mode === "init" || mode === "demo" || mode === "ui" || mode === "verify" || mode === "propose" || mode === "study" || mode === "toolkit-health" || mode === "garden" || mode === "docstrings" || mode === "annotate" || mode === "lint-annotated" || mode === "report" || mode === "seal" || mode === "share" || mode === "relink") {
    return { mode, args };
  }
  throw new Error(THEOREMCHECKER_USAGE);
}

/** The usage a `--help`/`-h` asks for (the command's own; the whole CLI's before a command), else null. */
export async function helpText(argv: string[]): Promise<string | null> {
  const asks = (a: string | undefined): boolean => a === "--help" || a === "-h";
  if (asks(argv[0])) return THEOREMCHECKER_USAGE;
  if (!argv.slice(1).some(asks)) return null;
  switch (parseTheoremCheckerCommand(argv).mode) {
    case "doctor": return (await import("../src/doctor.js")).DOCTOR_USAGE;
    case "init": return (await import("../src/toolkit/init.js")).INIT_USAGE;
    case "demo": return (await import("../src/demo/cli.js")).DEMO_USAGE;
    case "ui": return (await import("../src/ui/cli.js")).UI_USAGE;
    case "verify": return (await import("../src/verify/cli.js")).USAGE;
    case "propose": return (await import("../src/proposals/cli.js")).PROPOSE_USAGE;
    case "study": return (await import("../src/study_cli.js")).STUDY_USAGE;
    case "toolkit-health": return (await import("../src/proposals/cli.js")).TOOLKIT_HEALTH_USAGE;
    case "garden": return (await import("../src/proposals/cli.js")).GARDEN_USAGE;
    case "docstrings": return (await import("../src/toolkit/docstrings_cli.js")).DOCSTRINGS_USAGE;
    case "annotate": return (await import("../src/verify/annotate_cli.js")).ANNOTATE_USAGE;
    case "lint-annotated": return (await import("../src/verify/annotate_cli.js")).LINT_ANNOTATED_USAGE;
    case "report": return (await import("../src/verify/report_cli.js")).REPORT_USAGE;
    case "seal": return (await import("../src/verify/f4_seal.js")).SEAL_USAGE;
    case "share": return (await import("../src/verify/share.js")).SHARE_USAGE;
    case "relink": return (await import("../src/formalization/relink_cli.js")).RELINK_USAGE;
  }
}

async function main(argv: string[]): Promise<void> {
  // Asked for help: print it and start nothing (no toolkit is resolved, no login read).
  const help = await helpText(argv);
  if (help !== null) {
    console.log(help);
    return;
  }
  const { mode, args } = parseTheoremCheckerCommand(argv);
  if (mode === "doctor") {
    const { runDoctorCli } = await import("../src/doctor.js");
    runDoctorCli(args);
    return;
  }
  // Creating a toolkit needs no model, auth or run machinery.
  if (mode === "init") {
    const { runInitCli } = await import("../src/toolkit/init.js");
    await runInitCli(args);
    return;
  }
  // The demo plays a recorded run back on the page: no model, auth or run machinery.
  if (mode === "demo") {
    const { runDemoCli } = await import("../src/demo/cli.js");
    await runDemoCli(args);
    return;
  }
  // The UI reads run records and starts the CLI for actions; it needs no model or auth itself.
  if (mode === "ui") {
    const { runUiCli } = await import("../src/ui/cli.js");
    await runUiCli(args);
    return;
  }
  // Checking a seal reads one file.
  if (mode === "seal") {
    const { runSealCli } = await import("../src/verify/f4_seal.js");
    await runSealCli(args);
    return;
  }
  // Sharing sends a finished bundle: no model, no run machinery.
  if (mode === "share") {
    const { runShareCli } = await import("../src/verify/share.js");
    await runShareCli(args);
    return;
  }
  // Children run in their own process groups, so a group kill of this process misses them:
  // SIGTERM/SIGINT/SIGHUP and exit tear the child registry down here.
  installStopHandlers();
  // Machine env + billing path resolved ONCE here, before any mode-specific import, so a
  // misconfigured api mode fails before a run starts rather than mid-dispatch.
  applyWorkerEnv();
  applyAuthEnv();
  console.log(`[theoremchecker] auth: ${authSummary()}`);
  if (mode === "toolkit-health") {
    const { runToolkitHealthCli } = await import("../src/proposals/cli.js");
    await runToolkitHealthCli(args);
    return;
  }
  if (mode === "garden") {
    const { runGardenCli } = await import("../src/proposals/cli.js");
    await runGardenCli(args);
    return;
  }
  if (mode === "docstrings") {
    const { runDocstringsCli } = await import("../src/toolkit/docstrings_cli.js");
    await runDocstringsCli(args);
    return;
  }
  if (mode === "propose") {
    const { runProposeCli } = await import("../src/proposals/cli.js");
    await runProposeCli(args);
  } else if (mode === "study") {
    const { runStudyCli } = await import("../src/study_cli.js");
    await runStudyCli(args);
  } else if (mode === "verify") {
    const { runVerifyCli } = await import("../src/verify/cli.js");
    await runVerifyCli(args);
  } else if (mode === "annotate") {
    const { runAnnotateCli } = await import("../src/verify/annotate_cli.js");
    await runAnnotateCli(args);
  } else if (mode === "relink") {
    const { runRelinkCli } = await import("../src/formalization/relink_cli.js");
    await runRelinkCli(args);
  } else if (mode === "report") {
    const { runReportCli } = await import("../src/verify/report_cli.js");
    await runReportCli(args);
  } else {
    const { runLintAnnotatedCli } = await import("../src/verify/annotate_cli.js");
    await runLintAnnotatedCli(args);
  }
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  main(process.argv.slice(2)).catch((err: unknown) => {
    const message = err instanceof Error ? err.message : String(err);
    console.error(`theoremchecker: ${message}`);
    // A deliberate user-facing error carries its own actionable message, so the default output
    // stays clean. An UNEXPECTED throw reduces to a bare line with no location; set
    // `THEOREMCHECKER_TRACE=1` to keep the stack on the first failure instead of re-running.
    if (process.env.THEOREMCHECKER_TRACE && err instanceof Error && err.stack) {
      console.error(err.stack);
    }
    process.exitCode = 1;
  });
}
