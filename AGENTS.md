# LeanSmith — agent guide

This file is the guide for the coding agent that installs and runs LeanSmith for a user, Claude
Code and Codex alike (`CLAUDE.md` only imports it). Where it conflicts with a higher-priority system or developer
instruction of your harness, follow that instruction and keep the intent of this file.

**Pipeline prompts are self-contained.** A model call the pipeline itself makes (a V1/V1.5/fixer/F-stage
prompt, run with its working directory in a run dir under a toolkit) follows its inline prompt only:
nothing in this file applies to it.

## Layout

    LeanSmith/            this repository (git root; work from here)
      tools/                   the TypeScript pipeline: bin/ (CLI), src/, test/, scripts/node_env.sh
                               (src/ui/: the local web UI, `leansmith ui`)
      doc/USER_MANUAL.md       user-facing manual
      .claude/skills/leansmith/SKILL.md   the orchestrator guide (stages, halts, reading a run)
      templates/toolkit/       template for a new toolkit (`leansmith init` copies it)
      third_party/             adapted copies of optional domain libraries, on the pinned Mathlib
      tools/data/libraries.json  the pin (Lean, Mathlib) and the optional-library catalog
      <toolkit>/               your toolkit — its own git repository, wherever `init` put it; passed with `--toolkit`:
        runs/<slug>/           one verify run per paper
        Toolkit/, Papers/      Lean libraries

Causalean is one optional domain library (README).

## Installing for a user

Follow README "Install". Every domain library (Causalean, StatLean, FoML, optlib, …) is optional:
never choose for the user — show them `leansmith init --list`, ask which they want and where
the toolkit should live, then run `init` with their answer. While it builds, offer a first-time
user the demo (README "Try the demo"): start `leansmith demo` detached and give them its link.
When the user finishes the tour, stop the demo server you started by its PID; closing its browser
tab does not stop it. Do not leave a detached demo running after the installation guide is finished.
A library that is not offered is ported to the pin by `doc/PORTING.md`.

## Running the pipeline

Before running or orchestrating `leansmith verify` (or reading a run for the user), read
`.claude/skills/leansmith/SKILL.md` — Claude loads it as the `leansmith` skill; Codex reads
the file directly. From `tools/`, always `source scripts/node_env.sh` first (never hand-pin a Node):

    npx tsx bin/leansmith.ts verify <src> --toolkit <toolkit> --slug <slug> --stop-after V1.5

- At the start of an interaction on a run, bring up the toolkit's local UI and give the user its link
  (`npx tsx bin/leansmith.ts ui --toolkit <toolkit>`, detached; it prints the link of a UI already
  running and exits), then attach yourself to the run by watching it,
  `node tools/scripts/orch_watch_loop.mjs --toolkit <toolkit> <slug>…` over your unfinished runs (a run in phase `done` is left out)
  (Claude: under the Monitor tool, plus a recurring check-in; Codex: `orch.mjs watch <slug> --toolkit <toolkit>
  --timeout 600`, re-run it). Keep it running while you orchestrate: it reports every halt,
  finish or crash (also of a run the user resumed from the page) and when the user rejects a ruling of
  yours on the page or reports an issue on a comment; act on it yourself. Launch long runs detached (`setsid nohup … &`) with
  the log in a scratch directory. Kill a run by its PID, never by a pattern that can match your own
  shell. See the skill's "Mechanics".
- The user decides, on the paper's page, what changes what the paper claims or what enters their
  toolkit: a repair that would WEAKEN a main result (`--accept-repair` / `--decline-repair` /
  `--redo-repair`) and the promotion rounds (the round A / round B checklists). Always put your
  recommendation beside each item first (`orch.mjs recommend`; for a redo, with `--guidance`: the
  page shows it in the decision card and starts the user's redo from it), then tell the user it is
  waiting, and wait; never rule on these yourself. The same holds at ANY stage, the Lean stages
  included, for a ruling that would leave a main result weaker than the paper prints it (a
  condition added to it, a reading that narrows it): stop, put the ruling you would make and why
  on the page (`orch.mjs ask`), tell the user, and wait for their answer there or in the session.
  The one exception is a bookkeeping assumption, which is not a weakening and stays yours — what
  only makes an object well defined or measurable, a convention any reader supplies. Anything
  that is not bookkeeping and can weaken the paper, ask; when you cannot tell, ask. A run the user
  started with `--full-auto` delegates all of these to you (skill "Who decides"): recommend on each,
  and the recommendation is carried out and listed for their review. Never turn it on yourself.
  Every other ruling at a halt (`--reject-finding`, `--reject-rewind`, cap
  decisions, …) is delegated to the orchestrating agent: decide it per the skill, and record with
  `orch.mjs decided` one that leaves a lemma's or a definition's verified statement weaker than the
  paper's (the page shows it for the user's review; act on a rejection the watcher reports). So are F-stage directives
  (`flags.scaffold_redirect` in a run's `state.json`, `--clear-gate` on a cap gate): the orchestrating
  agent writes them itself. What only the user can give (a cited source you cannot access; widening the model
  workers' sandbox, `codexSandbox`), ask on the page (`orch.mjs ask`), with one line in the session.
- Fetch cited sources yourself; ask the user only for one you cannot access. For arXiv, read the TeX
  source, never the PDF.
- A parser, lint or renderer gap met while orchestrating is expected: absorb it in the run's files
  first; a code fix is the rare last step (skill "When the pipeline itself fails").
- Long waits: use your harness's background execution so you are notified on completion, rather than
  polling with sleeps.

## Lean

- Never run `lake` on the toolkit while a run or another agent builds it (`ps` first).
- Green is not proved: `lake` exits 0 with `sorry`. Check a full build of the module, grep the source
  for `sorry|admit|axiom`, and `#print axioms` via `lake env lean`.

## Talking to the user

- The user talks with you on the paper's page: answer a page message there (`orch.mjs reply`), and
  put a halt, a ruling, a question or a result on the page (`recommend`, `ask`, `decided`, `reply`).
  The interactive session is the user's debugging window: keep it terse — a line per action, no
  progress narration, no repeat of what the page already says.
- Explain in plain, brief language first — what goes wrong and why it matters — then name files and
  mechanisms. Be concise; refer to code by `path:line` instead of repeating it.
- Math in chat: Unicode (⊆, ∀, ≤, π …), not LaTeX; the terminal does not render it.
