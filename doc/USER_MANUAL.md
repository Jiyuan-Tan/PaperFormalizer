# TheoremChecker user manual

TheoremChecker checks the mathematics of a LaTeX paper in Lean. It transcribes the paper's results
(V1), has a referee check the transcription and the proofs (V1.5), formalizes and proves the
results against your base libraries and your personal toolkit (F1–F5), and writes a per-result
report (V6).

## Install

The README's "Install" is the one place that lists the requirements and the steps (clone, `npm
install`, `theoremchecker doctor` to check the prerequisites, `theoremchecker init` for your
toolkit, a first `verify`). Every command below runs from `tools/` after `source scripts/node_env.sh`.

## The toolkit

Every run needs a **toolkit**: your own Lake project with a `theoremchecker.json` at its root. It
holds your curated library (`Toolkit/Foundations`, `Toolkit/Tricks`), the per-paper Lean output
(`Papers/`), and the run records (`runs/`). The base libraries it builds on (Mathlib, and
optionally others such as Causalean) are read-only Lake dependencies declared in
`theoremchecker.json`.

Create one with `theoremchecker init <dir>` (README "Install"): it copies `templates/toolkit/`,
installs the optional domain libraries you choose (`--domains`, `--libraries`; `init --list` shows
them), makes the toolkit a git repository and builds it. The template has the lakefile (Mathlib
pinned; the domain libraries between the `# BEGIN/END domain libraries` markers; the `Toolkit` and
`Papers` libraries; the `paper_index` / `toolkit_index` executables TheoremChecker needs, built on
the template's own index extractor `TheoremCheckerIndexCore.lean` — every `verify` refuses a
toolkit whose lakefile lacks one), the barrels `Toolkit.lean` / `Toolkit/<Division>.lean` /
`Papers.lean`, an empty `doc/ledger.json` and a `.gitignore`. The `theoremchecker.json` `init`
writes for a Causalean toolkit:

    {
      "version": 1,
      "owner": { "name": "Your Name", "email": "you@example.org" },
      "toolkit": { "lib": "Toolkit", "papers_lib": "Papers", "divisions": ["Foundations", "Tricks"] },
      "base": [
        { "name": "Mathlib", "kind": "transitive", "search": ["loogle", "leansearch"] },
        { "name": "Causalean", "kind": "path", "path": ".lake/packages/Causalean",
          "index": ".lake/packages/Causalean/doc/library_index.json",
          "alias_file": "../TheoremChecker/tools/data/aliases/causalean.json",
          "prompt_notes": "../TheoremChecker/tools/data/prompt_notes/causalean.md" }
      ],
      "lean": { "toolchain": "leanprover/lean4:v4.33.0" }
    }

Per base library, all optional: `index` (a `library_index.json`-shaped declaration index, searched
by `npm run search`), `review_sidecars`, `alias_file` (concept synonyms that widen retrieval) and
`prompt_notes` (a Markdown file of the library's tactics and conventions, appended to the F2
scaffold and F4 filler prompts as `## Notes for <name>`). Relative paths resolve against the
toolkit root. TheoremChecker ships the alias file and the notes for Causalean under `tools/data/`;
`init` writes an index for a library that ships none under the toolkit's `doc/base_index/`.

TheoremChecker finds the toolkit, in order, from `--toolkit <path>`, the `THEOREMCHECKER_TOOLKIT`
environment variable, or the nearest ancestor of the current directory that contains
`theoremchecker.json`. If none applies it stops and says so; it never guesses a directory.

It holds three library tiers:

- **base** — read-only Lake dependencies (Mathlib, and e.g. Causalean), listed in `theoremchecker.json`;
- **toolkit** — `Toolkit/Foundations/…` (standard definitions and named results absent from the
  base) and `Toolkit/Tricks/…` (the user's own reusable lemmas). Everything in it is proved; it
  grows only by the owner's decisions in the promotion rounds ("Promoting results into your toolkit"), by `theoremchecker study`,
  or by the owner's own hand;
- **papers** — `Papers/<Slug>/`, one module tree per verified paper; may import base and toolkit,
  and only the root `Papers.lean` barrel imports it (added when the run's F5 completes).

Layering, module headers, size and run-token names are lint rules (`bin/lint_toolkit_layout.ts`),
not conventions.

To lint a toolkit by hand: `npm run lint:layout -- --toolkit
<path> [--scope toolkit|all]` (layering, module size, header contract, run tokens) and
`npm run lint:module-headers -- --toolkit <path> --strict`, from `tools/`; instead of `--toolkit`,
set `THEOREMCHECKER_TOOLKIT` or run from inside the toolkit. They lint a toolkit, not this
repository, so `npm run check` runs neither (it header-lints the shipped template barrels,
`npm run lint:template`).

## The local UI

    npx tsx bin/theoremchecker.ts ui [--toolkit <path>] [--port N] [--open] [--new]

opens a web page for your toolkit on this computer (Windows, macOS or Linux; any current browser).
It listens on 127.0.0.1 only and prints a link carrying this session's key — open that link (`--open`
does it for you); other pages and other machines cannot reach it. Three views, all live (a change
on disk reaches an open page within about a second; nothing needs a reload):

- **Papers** — your papers with their stage and status, and what is waiting for you.
- **Library** — the toolkit's results read from the Lean sources: each declaration's docstring next
  to its statement, row by row, what it uses, what uses it, and which papers use it.
- **Paper** — the paper as the run marks it (`annotated/`, else the source): the printed text that is
  wrong in red, the correction in blue, TheoremChecker's notes in the margin, a proof map (an arrow
  reads "used by"), and for each result its referee verdict, the conditions added, and its Lean
  statement linked to the paper's words: hypotheses one to a row, the conclusion as numbered
  clauses, a clause that carries hypotheses or parts of its own nested under it, and a predicate
  the paper's own Lean defines opening in place under the row that names it. A long statement block
  (printed or corrected) is set one sentence to a line, in the text's own order, as a paper sets a
  theorem: the sentences that introduce notation or fix a convention, those that assume and those
  that conclude each form a group of lines with space between the groups — no headings and no
  bullets, the same in all three views (All markup, Corrected, Original); a very long displayed
  definition is folded under the words that lead to it. The page reads a sentence's group off its
  form; every sentence is shown, word for word and in place. A promotion round is decided at the end of the paper and
  written into its checklist.

**Who acts on a run.** You work with an agent in an interactive session (Claude Code or Codex) started
in this repository: ask it, for example, "Use TheoremChecker to verify the paper at <path>". It
starts the run, brings up this page, gives you the link, and attaches itself to the run (the paper's
page shows "<agent> attached"). From then on it acts at every halt and resumes. What is yours to decide, never the agent's:

- a repair that would weaken a main result (accept, decline, redo with guidance) and the promotion
  rounds — on the page, with the agent's recommendation beside each item;
- any other ruling that would leave a main result weaker than you print it, unless it only adds a
  bookkeeping assumption (what makes an object well defined or measurable, a convention any reader
  supplies): the agent asks you first, on the page, and enters your answer;
- sharing a paper, widening the sandbox of the model workers, and a gardening item that would retire
  or remove a result of your toolkit.

The agent rules everything else by itself (a reading that weakens nothing, a proposed rewind, a cap,
its directives to the Lean stages). A ruling of its own that leaves a lemma or a definition weaker
than printed, no main result assuming more, it lists for your review afterwards.

To take the agent's word for the repairs or for a round's entries, "Accept all recommendations" —
under the title beside the repairs' notice, and on a promotion
round's checklist — enters its recommendation on every item you have not set yourself and, after one
confirmation that says what goes out, sends them as you would; it stays disabled while an item has
no recommendation. Each ruling it lists for your review appears on the paper's page under "Review the agent's
decisions": Approve it, or Reject it with what the agent should do instead — the agent acts on
that at once. Every other comment in the margin (a finding, an applied repair, a clarification) has
an optional "Report an issue" link at its foot: if you find the comment wrong, describe the issue and
send it — the agent takes it up, and the comment shows "Issue reported — addressed" once it has. You
can edit or withdraw a report until then; nothing waits on these. When the agent needs something only you can give
(a cited source it could not fetch), the request shows on the page and in your inbox: "Reply" on it
(or answer in the session) — a reply may carry files (the cited paper as a PDF, say: up to 5 files of
40 MB each, 100 MB per message; documents, pictures and archives only), which the agent reads as data. "Message the agent",
beside "Stop the run" and on every run's page, tells the agent anything else. The page is where you and the agent talk; the agent answers there, and keeps its interactive session (where you started it) short, for debugging. The agent reads what
you write and acts in its session; a message changes nothing in the run by itself (the decision
buttons stay the only way the page does). Your message reads "delivered" while the agent's watcher is on the run, and otherwise says when
it will be read; with no agent attached it is kept and delivered once one is. The agent's answers
appear under yours and the thread always ends with the box to write on in. An answer you have not
read is a small "new message" mark on the paper's row, not something that "needs you" (only a
decision of yours and a request of the agent's are); opening the paper's page reads it. "Clear
conversation" archives the thread in the run's folder (`orch_messages.archive.json`) to start
afresh; it asks again before clearing a message the agent has not acted on yet. The page shows a
desktop notification when something new waits for you — your browser asks
for its permission the first time the page opens; the header's button turns them off (remembered by
the browser) — and the tab's title counts the papers that wait. The page resumes a run, and applies
a promotion round, only while an agent is attached (an apply
that stops part-way is the agent's to settle; one refused before it applied anything shows why above
the checklist); with none, it tells you how to
start one.

Actions run the same CLI you would type, in the background; their output is in the run's
`logs/ui_<time>.log`. Ctrl+C stops the UI; runs it started keep going.

One UI runs per toolkit: run the command again and it prints the link of the one already running
(`--new` starts another). The orchestrating agent starts it at the beginning of a session and gives
you the link. From another computer, forward the port first — `ssh -L 7341:127.0.0.1:7341 <host>` —
then open the link (any local port works for the forward).

## The demo

    npx tsx bin/theoremchecker.ts demo [--dir <path>] [--port N] [--open] [--restart]

plays one recorded run of a made-up paper (`tools/data/demo/paper/`) on the real page, in a toolkit
of its own (`--dir`, default `~/.theoremchecker/demo`; port 7342), with a tour in the corner of the
page. The tour moves on with its Next button, or with what you send where a run would wait for you:
your decisions on a repair that would weaken a main result, the apply of a promotion round. A
stand-in for the agent takes them (nothing is started) and answers a message with a note on what a
real agent would do. No model, no Lean, no account. It goes on where you left it; `--restart` begins
again.

The states are written by hand, not taken from a live run: `tools/scripts/demo_author.mjs` takes the demo paper through
a dry run, writes its halts in by hand (the finding, the suggested repair, the rounds' entries, the
agent's recommendations) and keeps each state as a layered snapshot under
`tools/data/demo/snapshots/` (`demo_capture.mjs copy` / `build`); run it again when the run records
change shape. `tools/data/demo/demo.json` is the tour: one step per state, with its view, its words,
the element it points at, and how it ends.

## `theoremchecker verify`

    npx tsx bin/theoremchecker.ts verify <paper.tex|dir|archive> [--toolkit <path>] [--slug s]
        [--main relpath] [--targets label,label] [--resume] [--from-stage <stage>] [--fresh-review]
        [--from-transcript] [--stop-after <stage>] [--clear-gate <flag>]... [--defer-proposals] [--auto] [--dry-run]
        [--reject-rewind "<reason>"] [--clear-patch-cap] [--accept-cap]
        [--accept-repair [<node>,…]] [--decline-repair "[<node>,…: ]<reason>"] [--redo-repair "<node>: <guidance>"]...
        [--reject-finding "[<node>: [bookkeeping: ]]<reading>"]... [--add-condition "<node>: <condition>"]...
        [--edit-reading "<id>: <new text>"]... [--remove-reading <id>]... [--umbrella <node>]...
    npx tsx bin/theoremchecker.ts verify --stop --slug s [--toolkit <path>]

Every flag from `--reject-rewind` on answers a halt and goes with `--resume`; the halt message
lists the ones that answer it. The table at the end of this section says what each does and where
its full account is (the orchestrator guide's "Halt options" table says who rules).

- **Input**: a `.tex` file, a directory, or an archive (`.tar.gz`, `.zip`, an arXiv e-print).
  `--main` names the main file when several files carry `\documentclass`. A `.tex` file that
  includes files lying beside it is taken with its directory (the file as the main one); one whose
  included `.tex` files are missing is refused — pass the paper's directory or an archive.
- **Run id**: the slug — `--slug`, else the input's file name, lowercased with every run of other
  characters turned into `_` (at most 40 characters). The same slug resumes the same run.
- **Stages**: `V1`, `V1.5`, `F1`, `F1.5`, `F2`, `F2.5`, `F3`, `F3.5`, `F4`, `F5`, `V6` (what each
  decides and when it halts: "What the stages decide", under "Orchestrator reference").
  `--from-stage` re-enters a stage of an existing run; `--stop-after` halts once a stage completes
  (continue with `--resume`). `--stop-after F2.5`, `F3` and `F3.5` are refused: they run inside the
  combined proof-review loop, which completes as F4 — stop after `F2` (before the loop) or `F4`.
  `--from-stage F3`, `F3.5` and `F4` are refused for the same reason: the loop starts at `F2.5`.
- `--targets` limits the run to the named results (and what they rest on).
- `--clear-gate <flag>` (with `--resume`) clears a resume-blocking cap gate that the halt message
  names; it is applied as the run is entered, whatever stage the resume starts at.
- `--auto` lets an orchestrating agent take checkpoint decisions itself; it persists across resumes.
- `--full-auto` (implies `--auto`; persists across resumes) delegates your own decisions as well: a
  repair that would weaken a main result, the promotion rounds, and any other ruling that would
  weaken a main result take the agent's recommendation. Once the agent has recommended on every item,
  the decision is carried out as "Accept all recommendations" would, and each one appears under
  "Review the agent's decisions" (Approve, or Reject with what to do instead). The page marks the run
  "full auto" and does not count these halts as waiting for you; you may still decide an item first.
- `--dry-run` walks every stage without model calls or Lean builds (a smoke test of the wiring). A
  dry-run state is marked as such: a live run refuses to continue it (re-run from `--from-stage V1`
  without `--dry-run`, or use a fresh slug), and a dry run never touches a live run's state.
- **Stopping a run.** `verify --stop --slug s` stops the run's runner and every worker it started.
  While it runs, the runner records itself and its live workers in `runs/<slug>/logs/children.json`
  (pid, kind, tag, start time). `--stop` sends the runner SIGTERM if it is still alive, then stops
  every recorded worker that is still the same process (its start time must match the record — a pid
  the system has since reused is reported and left alone) and any process still carrying the run's
  tag in its environment (`THEOREMCHECKER_RUN_TAG`), then deletes the file. It combines only with
  `--toolkit` and `--slug`, and leaves alone a run recorded on another machine of a shared mount:
  stop that one there. A runner that receives SIGTERM, SIGINT (Ctrl-C) or SIGHUP starts no new
  worker, sends SIGTERM to each worker's process group, SIGKILLs what is left after 2 s, logs
  `stopped N child process(es)` and exits (128 + the signal number); a second signal skips the grace
  period. The workers (codex, claude, lake, lean-lsp) run in their own process groups: a kill of the
  runner's group alone does not reach them, and a runner killed with SIGKILL leaves them running —
  `--stop` is what cleans up. By hand, only as a fallback: signal the `node … tsx …
  theoremchecker.ts verify` process itself, not the `npm exec` wrapper above it (which does not pass
  the signal on), then check with `ps` that nothing with its working directory in the run's folder
  is left. `--resume` continues from the last completed step.
- A live `--from-stage V1` or `V1.5` takes the paper out of `Papers.lean` until its F5 completes again.
- **Statements and proofs are whole TeX.** V1 stops at a checkpoint when a parsed statement or proof
  is cut inside math, a display or an environment (a parser defect), and sends a node whose text is
  so cut back to the transcriber.

What the flags that answer a halt, and the re-entry flags, do to the run:

| flag | in one line | the full account |
|---|---|---|
| `--from-stage <stage>`, `--fresh-review`, `--from-transcript` | re-enter a stage; grade every result again; restart from the finished transcription | "Re-entries and proposed rewinds" |
| (plain `--resume`), `--reject-rewind "<reason>"` | approve, or reject, a repair a reviewer of the Lean proposed | "Re-entries and proposed rewinds" |
| `--clear-patch-cap`, `--accept-cap` | at a patch cap: another window, or end the loop | "Patch caps" |
| `--accept-repair`, `--decline-repair`, `--redo-repair` | your ruling on a repair that weakens a main theorem | "Weakened repairs and owner readings" |
| `--reject-finding`, `--add-condition`, `--edit-reading`, `--remove-reading` | withdraw a finding that misreads the paper; add a side condition; change a reading on record | "Weakened repairs and owner readings" |
| `--umbrella` | turn a split repair into the umbrella form | "A repair may split a result" |
| `--defer-proposals` | skip promotion round A | "Promoting results into your toolkit" |

How the referee reads the paper (dependency order, symbols, what is graded again) is in "Reading a
run"; what a repair may and may not change in "Repairs are replacements" and "Weakened repairs and
owner readings"; the review of the Lean plan in "F stages: the plan review".

A good first run: `--stop-after V1.5`, read the findings on the paper's page (or
`discovery/v1_5_review.json`), then `--resume --stop-after F1.5`, then `--resume`.

## Run layout

    <toolkit>/runs/<slug>/
      state.json              stage cursor (`init → V1 → V1.5 → 1 … 5 → V6`), findings, flags, halt receipts
      pipeline.jsonl          one line per stage event, V and F (checkpoint lines carry next-step guidance)
      token_usage.jsonl       one line per model call: tokens in and out (the page sums them)
      graph.json              the formalization graph (declarations, edges, review receipts)
      review_basis.json       what each node was last reviewed against (F2.5 reviews once per basis)
      nl_links.json           each result linked to its Lean theorem row by row (F5)
      pipeline_issues.md      pipeline defects the agent met on this run and how it absorbed them
      orch.json               the attached agent session; orch_requests.json (its questions to you),
                              orch_decisions.json (its rulings, with your review), repair_recommendations.json
                              (its recommendation on a weakened repair) — written by `tools/scripts/orch.mjs`
      orch_messages.json      what you and the agent wrote to each other on the page; uploads/<message>/
                              holds the files you attached to one
      owner_objections.json   the issues you reported on a comment of the page ("Report an issue"), each
                              with the agent's mark once it has acted on it
      ui_math_overrides.json  formulas the page could not draw, with the replacement it draws instead
      source/                 the paper as given
      discovery/              flat.tex, envs.json, author_notes.json (the authors' note macros read
                              away, see "Authors' note macros"), segments.json (parser corrections,
                              hand-editable),
                              core_refs.json (V1's reference core: the one core edited by hand),
                              core.transcribed.json, patches.json, core.json, v1_5_review.json,
                              v1_5_symbols.json, v1_5_referee_metrics.json, v1_revise_directive.json,
                              v1_lint_warnings.json; cited_sources/ (the cited statements, see
                              "Cited sources"); prompts/ (every referee call's prompt)
      codex_raw/              every referee reply, by call tag (`v1_5_shard_*`, `v1_5_symbols_*`, `v1_5_global*`)
      formalization/          plan.json, formalization.md, crosswalk*.json, gates.json (substrate
                              gates the F4 reviewers flagged)
      proposals/              the promotion rounds: A.json / B.json (the batches), *.decisions.json,
                              *.recommendations.json (the agent's), apply_<A|B>.pid (while an apply runs),
                              move_journal.json / move_pending.json (a move not yet through its gate),
                              move and corollary logs; voided/ (receipts and rounds a re-entry set aside);
                              history/ (the files of a round re-opened with --reopen-deferred);
                              dry_run/ (a dry run's checklists and ledger)
      reviews/                review artifacts (`reviews.jsonl`, verdict files)
      logs/                   agent transcripts (`agent_calls.log`, `stages/`), the fixer's prompt and
                              reply per round (`v1_patch_<stamp>_round<N>.json`), `ui_<time>.log` (actions
                              started from the page), `ui_math_failures.json`, `annotated_compile.json`;
                              children.json (the runner's live worker processes, while it runs; read by `--stop`)
      _archive/               what a re-entry set aside (`from_transcript_<stamp>/`, …)
      SUBSTRATE_DEBT.md       gates registered with `bin/gate.ts`, if any
      MISSING_ARCHITECTURE.md infrastructure F2 found missing, if any
      report.md, report.json  the V6 report
      bundle/                 the corrected paper, ready to submit from (below)
      annotated/              the paper's source with every finding marked in place (below)
    <toolkit>/Papers/<Slug>/  the paper's Lean (modules `Papers.<Slug>.*`)
    <toolkit>/Papers/<Slug>.lean   the run's barrel
    <toolkit>/Papers.lean     gains `public import Papers.<Slug>` when the run's F5 completes
    <toolkit>/doc/proposals/<slug>.A.md   the round-A checklist: cited results to build (below)
    <toolkit>/doc/proposals/<slug>.B.md   the round-B checklist: proved results (below)
    <toolkit>/doc/proposals/garden-<stamp>.md   a gardening checklist (below)
    <toolkit>/runs/study_<slug>/          a study: its requirement, plan, rounds and agent transcripts
                                          (a promotion round's builds: `study_<paper>__<entry id>/`)
    <toolkit>/runs/_garden/verify/<stamp>/   the logs of a `garden --verify`
    <toolkit>/runs/toolkit_docstrings/    the records of `theoremchecker docstrings`
    <toolkit>/doc/ledger.json             every toolkit declaration's origin and every promotion decision
    <toolkit>/doc/statements.json         every scanned statement, for recurrence across your papers
    <toolkit>/doc/toolkit_graph.json      the toolkit dependency graph, derived from the Lean
    <toolkit>/doc/toolkit_reuse_history.jsonl   one line per round B: how reuse grew
    <toolkit>/doc/toolkit_index.json      the toolkit's declaration index (`lake exe toolkit_index`)
    <toolkit>/doc/base_index/<name>.json  the index `init` wrote for a base library that ships none

A dry run (`--dry-run`) writes only under `runs/<slug>/`.

## The report

Each result of the paper lands in one bucket:

| bucket | meaning |
|---|---|
| `verified` | proved in Lean as the paper states it, nothing added |
| `verified_with_bookkeeping` | proved, resting on an added regularity condition (listed) |
| `conditional` | proved, resting on a cited result or a deliberately assumed gate (listed) |
| `repaired` | false as printed; an independent referee confirmed the minimal patch that fixes it (once the run reaches Lean, Lean must also certify the corrected statement) — the original error and its witness are listed under "Errors found — repaired" |
| `unresolved` | neither proved nor refuted (no Lean evidence, a mismatched statement, a red build, unclean axioms) |
| `refuted` | shown false (a V1.5 error with a witness, or a counterexample from the F stages) and no confirmed repair |
| `not_determined` | could not be checked as printed: the statement does not say enough (an ambiguity the paper leaves open) and no reading or repair was adopted — nothing was shown false |
| `not_checked` | the run stopped before Lean |

A statement the paper left undetermined whose repair a referee confirmed is no error: it keeps the
bucket its Lean evidence gives it, and the report lists it under "Statements made precise".

The header verdict is `errors_found` when anything is refuted, else `not_determined` when a result
could not be checked as printed, else `incomplete` when anything is
unresolved or not checked, else `no_error_found`. "Unresolved" and "not determined" never mean "wrong", and "verified"
is always conditional on what the report lists. Only results of the paper are rows: a condition the
fixer added (`ass:patch-*`) is listed under its result's added conditions, with any objection the
referee made to it (for instance that a weaker condition suffices), never as a refuted row.

Under the verdict the report grades the paper itself, on its mathematics alone (Lean's progress is the
verdict's), with the reasons by result (`report.json` `paper_grade`; the page's headline of a finished
run names it):

- **major errors** — a main result (a theorem or corollary of the paper, or a result the fixer names
  as key; a block split off one counts with it) holds only weakened with its contribution lost (the
  referee does not find the key results kept), is false with no repair, is left out of the
  formalization, or rests on a result still false;
- **minor issues** — errors repaired without weakening a main result, a main result weakened only in
  its constants or corner cases (the referee finding the key results and the contribution kept), an
  intermediate result narrowed,
  an ambiguity settled by a pinned reading (the referee's or yours), a bookkeeping condition, a result
  not stated precisely enough to check, or a false side result no main result uses: no main result is
  shown false or weakened;
- **error-free** — none of these.

### The report and the corrected-paper bundle

`report.md` opens in plain language, naming results as your paper does: **what was wrong and what
was done** (for each finding: the claim as printed, what is wrong, the counterexample, the correction
— or the repair that was suggested and your decision on it — what the correction gives up, and
whether Lean proves it), **clarifications** (readings, side conditions, notation: not errors), and
**what was proved in Lean, and what was not** (proved, taken from the literature as cited, not
certified, not formalized; axioms). The technical appendix after it carries the same facts by the
run's identifiers.

V6 also writes `runs/<slug>/bundle/`, a self-contained directory:

- `corrected_paper/` — your paper as it reads after the corrections: your own class, preamble, bibliography,
  figures and file layout, with each corrected statement, proof step and proof written in place of
  the printed one. It is plain TeX you can keep editing: no TheoremChecker macro, colour or note. A
  reading a statement relies on appears as a remark at that statement. A condition added to a result
  beyond its printed text is the last paragraph of its statement ("Additional condition."), unless the
  statement already states it in the same words. A corollary or proposition a repair split off
  a result is a corollary or proposition of the paper (in your own environment of that kind when the
  paper has one), placed as you place that result: when its proof follows its
  statement, the corollary and its proof come after that proof; when you prove the result elsewhere
  (an appendix, a later section), the corollary's statement follows the result's and its proof
  follows the result's proof there ("Proof of Corollary N"). The PDF is compiled with the
  same compiler as the annotated paper.
- `corrected_paper/TODO.md` — what still stands between that PDF and a submission, each item with its file and
  line. Blocking: a compile error, a result the review refuted, or could not check as printed, that has no adopted repair (it is
  still printed as in the original — nothing is written into your paper about it), a correction whose
  place in the source was not found, a reference that no longer resolves, a corrected proof standing
  beside the printed one. To check: equation numbers a correction shifted, conditions no corrected
  result uses any more. An orchestrating agent settles the blocking items the pipeline caused before
  it counts the run finished (the watcher wakes it for them), and tells you those that lie in your own
  TeX. A paper that ships a `.bib` and no `.bbl` gets its bibliography built (BibTeX, or Biber for
  biblatex) between the compiler's passes.
- `MATCH.md` — each result beside its Lean declaration: the (corrected) statement, the declaration
  with file and line, whether it is proved, its axioms, and which phrase of the statement each Lean
  hypothesis and conclusion states.
- `lean/` — a standalone Lake project you can send to a third person, who builds it with
  `lake exe cache get` and `lake build`: the paper's Lean code, the modules of your toolkit it
  imports (and theirs — nothing else of your toolkit), a generated `lakefile.toml` that requires
  only the public base libraries the code imports (Mathlib and each catalogued library at its
  public git url and revision; a library the catalogue carries only under `third_party/` is copied
  into `lean/vendor/<name>/` with its licence), `lean-toolchain` at the pin, `Check.lean` (prints
  the axioms of every result: `lake env lean Check.lean`), and a README listing the results and
  where each library comes from. There is no `lake-manifest.json`: Lake writes it on the first
  command from the pinned revisions. Two checks are recorded in `bundle.json` and the README:
  - self-containment — every import resolves to a file of the bundle or a module of a required
    library, no lakefile path leaves the directory, no file names a path of your machine. A failure
    is a blocking item of `corrected_paper/TODO.md`.
  - what it was built against — you built against your local copy of each base library, which need
    not be the public repository. The files of it your paper reaches are recorded with their git
    blob hashes (`lean/built-against.json`). Offline nothing more is claimed (a note).
    `theoremchecker report <slug> --verify-public` compares those hashes with the public revision
    over the GitHub API (nothing is cloned; `GITHUB_TOKEN` is used when set): a file that differs is
    an item to check (not blocking), since the third person's build could then differ from yours.
  - the pin — a library your toolkit requires from its public repository is pinned at the commit your
    toolkit built on (its `lake-manifest.json`), not the catalogue's. When TheoremChecker pins a
    different one, the README and the V6 log say so and how to move to it; nothing is refused.
- `page/page.json` — the paper's page as the local UI draws it, as data: each result as corrected
  with its verdict, notes, Lean declaration and the links between its phrases and the Lean rows, the
  definitions those rows open, and the paper itself rendered with its margin notes (figures and the
  PDF are those of `corrected_paper/`). It holds nothing of a run at work (no decisions, questions or
  token counts) and no path of your machine, so the page can be drawn from the bundle alone.
- `REPORT.md` — the report.
- `f4_seal.json` — when the run has Lean: the verdict of each of the two Lean reviewers on every
  statement, bound to the statement Lean elaborated, with the hash of your source, under one `code`.
  `theoremchecker seal <bundle dir>` checks it anywhere (no toolkit, no model, no Lean): the code is
  the hash of the file's contents, and both reviewers passed every statement. It is a checksum, not a
  signature — it shows the bundle is consistent with a finished review, not who ran it.
- `f4_reviews.log` — what the two reviewers answered at each of those review passes, as the run
  logged it (earlier passes, with the findings since fixed, included), with the paths of your machine
  blanked. The seal holds its hash, so the check also confirms this file is the one it was written with.

  The seal also names every file of `lean/`, `corrected_paper/` and `page/` with its hash (the
  compiled PDF apart), so the check fails when one of them was changed or removed after
  the bundle was written; files added later, such as Lake's build outputs, are not its concern.
  (A bundle written before the corrected paper's folder was renamed holds it as `paper/`, and has
  no `page/`: its seal still checks.)
  `theoremchecker report <slug> --arxiv <id>` records the paper's arXiv identifier in the run and
  under the seal — as you declare it: nothing compares it with your source.

What the checks do and do not establish: every corrected statement and its proof was graded by the
referee, and every result that depends on a corrected one was graded again. TheoremChecker checks
the paper's results: the prose around them is yours, left as printed and not examined.

`theoremchecker report <slug> [--out <dir>]` writes the report and the bundle again from the run's
records — no stage runs, no model is called, Lean is not rebuilt (the evidence is the one the report
on file recorded). With `--out` both go to that directory and the run is left untouched.

### Sharing a finished paper

A finished paper can be published on the public site of shared papers
(<https://jiyuan-tan.github.io/TheoremCheckerPapers/>), at `papers/<slug>/` there. Sharing is your
decision, and it is public:

- **What it publishes**: the whole bundle — the corrected paper's TeX source and PDF, the findings
  and the referee's notes (the page snapshot), the Lean code and the report. There is no partial
  share. It cannot be fully undone once others have fetched it.
- **Under your name**: you confirm in your browser, signing in to GitHub. The sign-in asks for no
  permission: the share service learns your GitHub name and account, nothing else, and keeps no
  token. Nothing is installed or signed in on your machine; TheoremChecker never asks for a password
  or a token.

      theoremchecker share <slug> [--dry-run]

The command refuses a run that has not finished V6, a bundle of an older layout (write it again
with `theoremchecker report <slug>`), a bundle with blocking TODO items, and a bundle the registry
would refuse — it applies the registry's own rules first, one line per problem: a missing or broken
seal, a file outside the bundle's layout or one the seal does not name, a dotfile, a symbolic link,
an `.html`, `.xml`, `.js` or `.svg` file, a path over 255 bytes or whose last part is over 100
bytes (the archive's limits), a file over 24 MB or a bundle over
60 MB or 3000 files. Otherwise it prints what will be published and the warning, and asks you to
type the slug. **Only you can answer**: there is no flag that skips the question, and without a
terminal (a script, an agent) the command prints the summary and refuses; `--dry-run` prints the
same and stops. What is sent is what was shown: the bundle is read again at the send, and a file
changed in between is a refusal.

The bundle is then uploaded, and the command prints a link and a four-letter check code (and tries
to open the link in your browser). On that page you sign in to GitHub, check that the code matches,
and press **Share publicly**. The registry then checks the paper: if you are one of its trusted
sharers it is published at once, otherwise it waits for the registry owner's review. The command
waits (up to 20 minutes) and prints the outcome: the paper's public page, the pull request under
review, or what the registry refused. A link not confirmed within the hour expires.
`runs/<slug>/share.json` records the share and its outcome. It holds the share's poll token and
claim link: a new toolkit's `.gitignore` keeps it out of git (add `runs/**/share.json` to an older
one).

On the paper's page of the local UI, a finished run has a **Share** button: it shows the same
summary and warning, and sends only after you tick "I understand this publishes the paper's TeX
source and PDF". The confirmation is good once, for ten minutes, and for the bundle as the dialog
showed it. A new tab opens on the sign-in page (or use the "Open GitHub sign-in" link when the
browser blocked it); the paper's page shows the check code, then where the share stands, until it
is published or refused.

The share service is `THEOREMCHECKER_SHARE_URL`, else the default in `tools/src/verify/share.ts`
(`DEFAULT_SHARE_URL`).

### The annotated paper

V6 also writes `runs/<slug>/annotated/`: a copy of your source tree with each problem marked where
the paper states it. The wrong or ambiguous sentence is red, the corrected text follows in blue (a
corollary the repair splits off the result in a blue block of its own after it),
and an orange note beginning "TheoremChecker:" states the mistake plainly and only the mistake, in
labelled lines: **Claim** (what the printed statement asserts), **What is wrong** (the step of your
proof, quoted, what it silently uses and when that holds, closing with "Counterexample: …", one
instance where it fails),
**Proposed fix** (what the repair changes) and **Gives up** (what is lost, when anything is) — and,
only when the run recorded it, that the fix weakens the result. The repairer writes every note (the referee writes none), and
when the referee confirms a repair it also grades the note as you would read it — you can find
the step and see why it fails from it alone — (`explanation_clarity`
in `v1_5_review.json`: `ok` or `unclear`, with a reason). An unclear note goes back to the repairer
with the reason — the repair stays, only the note is rewritten — as a refinement round (it counts
toward the refinement cap of "Patch caps", never as an error of your paper), and the rewritten note is graded
again. A suggested weaker version of a main theorem is graded the same way before you see it. There
is no separate clarity command or waiver: `theoremchecker annotate <slug>` only rewrites the
annotated paper from the notes on record (no model call; `--compile-record <path>` names another
compile record than `logs/annotated_compile.json`). The annotated paper is also checked for raw TeX: a block the
checker could not typeset (text shown as escaped backslashes, a character shown as `[U+…]`, a formula
with an unmatched `$`) or a LaTeX error stops the run at a "render checkpoint" before anything is put
to you, listing each block. That is a defect of the checker, not of your paper, so there is nothing
for you to decide: once the renderer is fixed, `--resume` typesets the paper again and the run goes on.
`theoremchecker lint-annotated <slug>` runs the same check on the annotated paper as written and exits
with an error listing any such block. The note never mentions how the
checker works (no internal names, no talk of dependencies or transcription). Each result is
checked and marked as you print it — one result, one note — even when its parts or cases rest on
different hypotheses. Each marked block starts on its own line with its label above the indented text, numbered
clauses one per line, displays kept as displays. A corrected statement reads like your own: it
keeps your references to the results it cites and does not repeat a condition that a cited result,
once corrected, already carries. An error with
no accepted repair is red with a note (and any suggested weaker version, marked "not applied"); a
reading adopted for formalization gets a note after its statement ("Clarification:"), and a condition
the verified statement carries beyond the printed text gets a note at the end of every result carrying
it ("Bookkeeping condition:"). The paper's own text is never
changed, only wrapped: `\label`s stay where they were, and a span that would split math or an
environment is widened to the whole display. `annotated/ANNOTATIONS.md` lists every annotation
with its original `file:line` and anything that could not be placed. When `pdflatex` or `latexmk`
is on PATH the annotated main file is compiled; `report.md` names the `.tex` and the PDF.

The annotated paper shows every change the run made, proofs included. A repair revises your proof
step by step rather than rewriting it: in your proof itself (wherever it is, an appendix included),
each changed run of consecutive steps is red ("Original:") with its replacement right after in blue
("Corrected:", or "Corrected (for the proposed statement):" for a suggestion you have not ruled
on); a statement or proof rewritten whole reads as one red and one blue block. The amended proof is what gets checked and
formalized. A repair of a result you give no proof for shows its proof in one blue block ("Corrected
proof (confirmed):" / "Proof of the proposed statement:") at the end of the
section holding the result, saying the paper's proof could not be located.

**How the notes are produced.** Each note is generated from the fixer's `owner_explanation` fields
(on patches and on unfixable / suggestion entries), each field filtered so that no node id or
pipeline word (edge, wiring, core, node, transcription, referee, …) reaches the author; with the
structure on file the note opens at "Claim:". A rewritten note is graded again: its hash is part of
the result's verdict basis. The error ledger holds no notes: the annotated paper and the report show
the fixer's note, else the referee's plain finding (detail and the gist of the witness). A suggested
weaker version of a main theorem waits for a V1.5 pass that grades it as a repair (its weakening
accepted, its note graded); one the referee objects to leaves the receipt and goes back to the fixer.
One printed result is one statement node — its whole body, wired to every hypothesis any of its parts
or cases uses (lint rule (a) rejects a second node at an environment) — so it gets one annotation.

**Review the annotated paper at every halt.** The same tree is also written, for the run as it
stands, at the end of every V1.5 pass (so `--stop-after V1.5` leaves you a PDF) and whenever the
run stops for a ruling: a repair that would weaken a result, a proposed F-stage rewind, a patch
cap. A repair that would weaken a main result is yours to decide, on the paper's page, with the
attached agent's recommendation beside it; the agent makes the other rulings from this paper (see
"The local UI"). The pending item is marked where the paper states it — the printed sentence red, the
proposed repair in blue under "Proposed repair (awaiting your decision):", or a note "Proposed
correction (awaiting your decision):" / "Repair not settled (awaiting your decision):" — with the
finding, what the repair gives up, and what the decision is about, in plain words. The paper carries
no commands: the halt message lists the options that answer it (at a weakened repair:
`--accept-repair`, `--decline-repair`, `--redo-repair`, or `--reject-finding` when the finding misreads
the paper). The halt message and the V1.5 log line name
the PDF (the `.tex` when it did not compile); `ANNOTATIONS.md` lists the pending items as `awaiting
decision`. A ruling is read from the paper, not from `state.json`. The tree is rebuilt each time, so the
final V6 paper carries no "awaiting" block. A recompile of an identical tree whose last compile
failed on the paper's own TeX is skipped (`logs/annotated_compile.json`).
When the paper's own source does not compile on your TeX installation (an old paper on a newer
TeX Live), the annotated copy fails the same way: the run says so in a note and goes on — the
annotated TeX and the page do not need the PDF. The source is compiled once, in a scratch copy, to
tell its errors from those of the annotation (`logs/source_compile.json`).

## Promoting results into your toolkit

A run offers results to your toolkit twice, and stops each time for your decisions:

- **After F1 (round A)**: the results the paper cites without proving, in
  `<toolkit>/doc/proposals/<slug>.A.md`. An accepted one is built in your toolkit from scratch —
  proved and reviewed before the paper's proofs — and the paper then uses it instead of assuming it;
  a declined one stays an assumption of the paper. `--defer-proposals` skips this round.
- **After the report of a full F run (round B)**: the results the paper's Lean proved, in
  `<toolkit>/doc/proposals/<slug>.B.md`. An accepted one either moves into your toolkit as proved,
  or — when its Lean is stated over the paper's own setting — its general form is built in your
  toolkit and the paper's result becomes a corollary of it. Each entry says which.

Each entry is one main result — a statement a textbook would state; the helper lemmas proving it go
with it — written so you need not read Lean:

- **where it goes**, right under the title: Foundations (standard, textbook results in Mathlib's
  vocabulary) or Tricks (techniques reusable in your lines of work), the topic, and the bar it meets;
- a **title** and a **reference** (the standard source of a known result, or "new, from <paper> §…");
- the **content**: the statement in plain mathematical words (hypotheses, then conclusion);
- **why it is reusable**, and where else **your other papers** state it (the strongest evidence);
- the **closest existing results** in the libraries and your toolkit, and **where it attaches** in
  your toolkit;
- **if accepted**: how it enters your toolkit (built, moved as is, or built in general form);
- an **independent check** that the words say what they should (exactly what the Lean proves, a
  general form of it, or what the cited work states) and that it is not a duplicate (a duplicate is
  declined automatically and listed).

A "Lean details" block under each entry holds the names, the target module, the Lean statement and
what moves with it. The checklist opens with your toolkit's health. Edit each entry's `decision:`
line — `accept`, `accept_with_edits` (then `edits:` lines for division, target_module, proposed_name,
title, reference, content — `content` is refused on one of the paper's own stated results, which
keep what they prove), `generalize_first` (round B: build a general form even of an entry
proposed to move as is), `decline` or `defer`, optionally with a `note:` — then run

    npx tsx bin/theoremchecker.ts propose <slug> --round <A|B> --apply [--toolkit <path>] [--dry-run]

(`--round` defaults to the round awaiting decisions, else B; `--dry-run` is required for, and
only for, a run started with `--dry-run`: its checklist and ledger records stay under
`runs/<slug>/proposals/dry_run/`.) Nothing enters your toolkit without your decision. Every new toolkit module and every edited paper
file is checked (`lake build`, `#print axioms`, the layout lints, the index); a moved module imports
only what its declarations use. A move that does not pass its checks is left as written and handed
to the orchestrating agent, which repairs it and runs the checks again; entries applied before it
stay applied. A promotion never changes what your
paper claims, and Lean checks that it did not: every declaration of the paper and the toolkit must
state after the move exactly what it stated before (a moved result under its new name; a result
rebuilt in general form keeps its statement and gets a shorter proof). The reviews the paper's
statements had passed therefore stay valid. Every decision is recorded in
`doc/ledger.json`; round A then continues the run at F1.5, round B finishes it. A toolkit name must
be free and follow Mathlib's naming (a result about a type lives in that type's namespace).
`propose <slug> --round <A|B>` without `--apply` re-renders the checklist, keeping your decisions.
`--resume` on a run that finished before round B existed opens it from the report on file. Round B
needs the `candidate_scan` exe in your toolkit's lakefile (the template has it); so does F4's
review cache, which skips a target only while Lean still elaborates its statement and everything it
rests on to the same `closure_hash` (keep `CandidateScan.lean` in step with the template).
`propose <slug> --reopen-deferred` proposes again the entries you deferred for that paper (a deferred
entry also returns by itself when a later paper proves the same result).

Your toolkit's modules live under a **topic tree**, `doc/taxonomy.json` (Mathlib's top level:
Probability › Conditioning, Statistics › Design, …). An entry needing a topic the tree lacks comes
with a separate `## topic · <path>` item you accept or decline first. A result whose proof never
uses some of its hypotheses enters in general form without them.

**Building a toolkit module yourself.** `npx tsx bin/theoremchecker.ts study <slug> [--toolkit
<path>]` writes a requirement template at `runs/study_<slug>/requirement.md` on its first run; fill
it in (goal, the declarations to provide, the statement, a standard reference, the intended reuse,
what may be assumed) and run it again: it scaffolds, proves and reviews the module, then places it
in your toolkit through the same checks. `--resume` continues a study that was interrupted; a study halted
at its build, review or placement cap continues with `--resume --clear-build-cap`, `--resume
--clear-review-cap` or `--resume --clear-coordinate-cap` (each refused unless the study stopped at
that cap; the study prints the one that applies when it stops). `--dry-run` walks the
study without model calls or Lean builds.

**Docstrings.** Every declaration's docstring follows one contract
(`tools/src/shared/prompts/docstring_contract.txt`): its first paragraph translates the statement into
plain English, and each phrase links to the Lean hypothesis it states (`[phrase](hyp:name)`, the
conclusion as `[phrase](goal)`), as in Causalean — the paper page and the library show the two side by
side, row by row. F5 enforces it on a paper's modules and the study and promotion prompts state it;
`npx tsx bin/theoremchecker.ts docstrings [--toolkit <path>] [--modules M1,M2]` brings the toolkit's
existing docstrings to it (docstring edits only, validated by a build; review the diff and commit).
Run it when no verify run is building the toolkit: the edits rebuild every module importing them.
F5 also links each paper result to its Lean theorem row by row (`runs/<slug>/nl_links.json`): for
every Lean hypothesis, the sentences or formulas of the paper that state it, and the paper text no
Lean row carries. In a linked result's Lean statement on the page, the rows the paper states stay in
view and each run of three or more hypothesis rows it says nowhere (what Lean needs: types, instances,
measurability, …) is one closed line, "N rows Lean adds", that opens in place; the conclusions are
always shown. Links are kept only for the statement they were written for: a result whose Lean
changed since is drawn unlinked, with a notice. `npx tsx bin/theoremchecker.ts relink <slug>
[--only <node>,…]` runs that link step alone on the run as it stands (it calls the F5 model; no stage,
no Lean build) and writes `nl_links.json` again — `--only` for those results, the others kept.
A result linked from the same statement, Lean and prompts, whose links the audit returned whole, keeps them without a call; one whose
links still fit its statement and Lean is revised from them by the audit call alone; `--fresh`
links every result from nothing, as `--only` does the results it names.

**Toolkit health.** `npx tsx bin/theoremchecker.ts toolkit-health [--toolkit <path>] [--all] [--json]
[--no-rebuild]` re-derives `doc/toolkit_graph.json` from the Lean — declarations as nodes, "uses" as
edges, the base libraries' declarations as leaves (`--no-rebuild` reads the graph on file) — and
reports, on your main results (`--all`: helpers too): results nothing uses, results stated twice,
how many of your papers use the toolkit, modules that hold unrelated groups (split?) or lean on each
other heavily (merge?), the most reused results, results no paper has used for months, and how
reuse has grown paper by paper (`--json`: the same as JSON, with the reuse history).

**Gardening.** When the toolkit's health has findings, round B ends by writing
`doc/proposals/garden-<stamp>.md` — or run `npx tsx bin/theoremchecker.ts garden [--toolkit <path>]
[--no-rebuild] [--dry-run]` any time (after a Mathlib update it also flags results the base
libraries now state; `--dry-run` writes the list with no gardener call, every item recommended
`decline`). Each item says
what the graph shows, the suggested change (move a module to its topic, merge or split modules,
retire a result a library now states, remove an unused one) and a recommendation. The orchestrator
decides each item and carries out the accepted ones by editing the Lean (your toolkit committed first),
then `garden --verify <file>` checks the edits against the committed toolkit (builds, axioms, no paper
statement changed, lints, index, graph) and records them in the ledger; a failed item is reverted with git.
Gardening only reorganises what the toolkit holds; an item that would retire or remove a result is
the one kind put to you.

## Environment variables

| variable | effect |
|---|---|
| `THEOREMCHECKER_TOOLKIT` | toolkit root when `--toolkit` is not given |
| `THEOREMCHECKER_SHARE_URL` | the share service `theoremchecker share` (and the UI's Share button) uploads to |
| `THEOREMCHECKER_LEANLSP_WARMUP_MS` | cap on the pre-run `lake build` warm-up (default 10 min; `0` disables) |
| `THEOREMCHECKER_NOTE_MACROS` | `off`: a new run reads the paper as written, authors' note macros and all ("Authors' note macros") |
| `THEOREMCHECKER_STOP_AFTER` | `--stop-after`, for a run started without the flag (the flag wins; F2.5/F3/F3.5 refused) |
| `THEOREMCHECKER_LEAN_PROJECT_PATH` | legacy Lean project override; must be unset or equal the toolkit root |
| `THEOREMCHECKER_LEAN_LSP_MCP` | `lean-lsp-mcp` binary |
| `THEOREMCHECKER_VERIFY_MAX_MS` | cap on one build check of a toolkit promotion or a study build (default 1 h; `0` disables) |
| `THEOREMCHECKER_SHARED_LEAN_LSP_URL` | set by the runner for its workers (one shared lean-lsp server) |
| `THEOREMCHECKER_CODEX_SANDBOX` | `workspace-write` (default) or `danger-full-access` |
| `THEOREMCHECKER_CODEX_EFFORT_OVERRIDE`, `THEOREMCHECKER_CODEX_MULTI_AGENT` | codex tuning |
| `THEOREMCHECKER_AUTH_MODE`, `THEOREMCHECKER_ANTHROPIC_AUTH`, `THEOREMCHECKER_OPENAI_AUTH` | billing (below) |
| `THEOREMCHECKER_CODEX_HOME_API`, `THEOREMCHECKER_CLAUDE_CONFIG_DIR` | api-mode codex home; claude account dir |
| `THEOREMCHECKER_CLAUDE_ROLES` | `claude` or `codex`: the CLI that runs the claude roles (F1 plan, second F4 reviewer, curator, gardener, study coordinator; also `claudeRoles` of the local config). Unset: `claude` when it is installed and usable, else `codex` |
| `THEOREMCHECKER_PYTHON` | interpreter for the retrieval helpers |
| `THEOREMCHECKER_TRACE` | print the stack of an unexpected error |
| `THEOREMCHECKER_ORCH_TICK_MS` | how often `tools/scripts/orch.mjs watch` looks at the run (default 10 s) |
| `THEOREMCHECKER_ORCH_LOOP_PAUSE_MS` | how long `tools/scripts/orch_watch_loop.mjs` waits before re-arming a watch that failed (default 60 s) |
| `THEOREMCHECKER_NODE_BIN`, `THEOREMCHECKER_NODE_ENV_VERBOSE` | `scripts/node_env.sh` |
| `THEOREMCHECKER_MODEL_CODEX_KERNEL`, `THEOREMCHECKER_MODEL_CODEX_MECH`, `THEOREMCHECKER_MODEL_CODEX_VERIFY`, `THEOREMCHECKER_MODEL_CLAUDE_MAIN` | model ids per role (`tools/src/models.ts` says which calls each serves) |
| `MCP_TIMEOUT` | time allowed for the lean-lsp server to start (default 10 min; also `mcpTimeoutMs` of the local config) |
| `CLAUDE_CODE_GIT_BASH_PATH` | Windows: the Git Bash the `claude` CLI uses (also `gitBashPath` of the local config) |

## Billing

By default the workers use the machine's interactive `claude` / `codex` logins. To bill API keys
instead set `authMode` (or `anthropicAuth` / `openaiAuth`) and a key in `tools/config/local.json`,
or `THEOREMCHECKER_AUTH_MODE` with `ANTHROPIC_API_KEY` / `OPENAI_API_KEY`. API-mode codex runs in its
own `CODEX_HOME` (default `~/.codex-theoremchecker-api`) so the subscription login is never evicted.
On a machine with `codex` alone (no usable `claude`: absent, logged out, or API mode with no
Anthropic key) the claude roles run on `codex`, on the kernel model at high effort; `claudeRoles`
pins the choice, and the run's first log lines and its usage records name the CLI and model that ran them.

## Orchestrator reference

How a run works, stage by stage, and the detail behind the orchestrating agent's guide
(`.claude/skills/theoremchecker/SKILL.md`), which says what to run and what to do at each stop and
points here by heading. Each section opens with what happens; the rest is what the agent reads and
does. In this part "you" is the agent, and "the user" or "the owner" is the person whose paper and
toolkit it is. Nothing here repeats an earlier part: a section names the heading that says the rest.

### What the stages decide

| stage | decides | halts when |
|---|---|---|
| V1 | writes a REFERENCE core (`discovery/core_refs.json`: env ids, anchor slices, wiring — never paper text); the runner copies the text verbatim into `core.json` | gate/lint not clean after 3 rounds, or the builder refuses; a worker that could not read or write the run's files halts at once (an ENVIRONMENT checkpoint: the machine's, not the paper's) |
| V1.5 | per node: faithfulness ok/drift · ambiguity ok/pinned/unresolvable · correctness ok/bookkeeping/unclear/error(+witness; `minimality` when a patch part is only non-minimal; `weakens_contribution` when a repair holds but weakens the claim) | REVISE on drift (capped, then final); an error or unresolvable ambiguity on a faithful core → V1 patch mode; a round due at its cap halts for you (see "Patch caps") |
| V1 patch | the FIXER: the smallest repair of every finding that keeps the claim (`discovery/patches.json`); a fresh V1.5 pass confirms it | only a weaker version holds → `unfixable` + `suggested_repair`, halt for the owner; nothing true left on a key result's path → FAIL; patch file not clean after 2 rounds (a third runs when the violations fell between the two) → checkpoint; a consequential patch following only a suggested repair of a main theorem is held (`patches.json` `set_aside`) and applied with the suggestion the owner accepts, dropped with one declined or redone |
| F1–F5 | Lean plan, plan audit, scaffold, proofs, convergence review, docstrings | the F1.5 checkpoint is yours to review (plan fidelity, reuse, cited leaves) and resume; an F1.5 review F1 cannot act on halts for you with the reviewer's findings (see "F stages: the plan review"); an F2.5–F4 escalation on a paper statement (`fix-source` `[statement-wrong]`; `unclear` on the statement's wording), halts as a PROPOSED rewind on the statement it names — yours to approve or reject (see "Re-entries and proposed rewinds") |
| V6 | report: what was wrong and what was done, clarifications, what Lean proves (plain language), then the technical appendix (per-result buckets, errors by root cause, pinned readings as suggestions); `bundle/` = the corrected paper ready to submit (clean TeX + PDF, `TODO.md`, `MATCH.md`, `lean/`); `annotated/` = the source with each finding marked (red original, blue correction, "TheoremChecker:" note), compiled when a TeX compiler is on PATH | — |
| promotion A | after F1: which results the paper cites without proving are built in the toolkit (see "Promotion rounds: the orchestrator's procedure") | anything proposed → halts at `proposals_A` for the owner's decisions |
| promotion B | after V6 of a full F run: which proved results of the paper join the toolkit (see "Promotion rounds: the orchestrator's procedure") | anything proposed → halts at `proposals_B` for the owner's decisions |

The stage cursor (`state.json` `stage_completed`) runs `init → V1 → V1.5 → 1 … 5 → V6`;
`verify.phase` says which runner owns the next step. The F runner is entered only after V1.5
accepted a core, and refuses to run when `core.json` differs from the one V1.5 accepted.

### Verdict semantics

Verdict semantics the user fixed. Inferable ambiguity is PINNED — the most plausible reading
becomes an explicit `ass:pin-N` bookkeeping assumption and is reported as a suggestion to the
authors. A pinned reading BINDS the F stages: F1/F1.5/F2 see it under the node
(`pinned_readings_binding`), every F2.5–F4 reviewer target shows "Pinned readings (binding)", and an
ambiguity a pin settles is a Lean-side fix (re-scaffold to the pin), never a paper finding — only an
ambiguity no pin settles (the reviewer says why in `unpinned`) becomes a proposed rewind. Every
error (and every ambiguity the text cannot settle) on a faithful core is REPAIRED:
V1 in patch mode writes the minimal patch that keeps the key contribution, an independent V1.5 pass
confirms it, and the F stages formalize the CORRECTED paper. A repair never weakens the paper (see
"Weakened repairs and owner readings"); a result with nothing true left to suggest stops the run
when a key result rests on it, and is descoped and reported otherwise.

A result is only reported wrong on a counterexample that is a genuine instance of the paper's
setting. When the referee's counterexample lives only in a case every reader excludes (a functional
that is identically zero, zero variance, an empty class, equality at the edge of a strict
inequality), the exclusion is recorded as a side condition of the result (listed with the other
side conditions in the report, not marked in the annotated paper) and the result is graded under it.

### The core files of a run

Files: `discovery/core_refs.json` is V1's reference core (env ids, anchor slices, wiring — never
paper text) and the ONLY core edited by hand; `discovery/core.transcribed.json` is the
transcription V1 builds from it, the paper's text verbatim (a hand edit of it is refused at the next
V1 entry: V1 rebuilds it from `core_refs.json`); `discovery/patches.json`
the repairs (hand-editable; its corrected texts are derived from the ops on every read, and it is
re-applied at every V1 accept and V1.5 entry); `discovery/core.json`
= the transcription and the patches combined, the corrected paper F1 formalizes. V6 diffs the two into a "Corrected version"
change log and reports "errors found — repaired by minimal patches" when every error has a
confirmed repair (and Lean certifies every repaired result). `core.json` is the runner's — it is
rebuilt at every V1.5 entry, so hand-fix the TRANSCRIPTION in `core_refs.json` (then `--from-stage
V1`, which materializes the transcription with no agent call) and a repair in `patches.json` (then
`--from-stage V1.5`); delete `patches.json` to start the repair
over. `--from-stage V1`/`V1.5` resets both round counters and clears every earlier finding and
the accepted-core hash (V1.5 restates what still holds). A hand-edited
file that cannot be built checkpoints naming the file to fix; an invariant failure on consistent
inputs is a runner bug — report it (the orchestrator guide's "When the pipeline itself fails"), never mask it in the file.

### Cited sources

The V1.5 checkpoint "needs the source of N cited result(s)". Fetch each cited work
yourself before asking — the arXiv e-print, an open repository scan (e.g. real.mtak.hu for
Hungarian Academy journals), Project Euclid / the publisher via its DOI (look the DOI up on
Crossref; never guess it), Unpaywall, the Wayback Machine. Read the statement off the source
(render scanned pages and read them; OCR of old scans is unreliable) and write it verbatim, with
its equation numbers and a provenance header (citation, URL), to
`discovery/cited_sources/<key>.txt`; keep the fetched file beside it as `<key>.source.pdf`. A
work the user attaches on the page in reply to your request (the watcher prints its path) is
handled exactly so, its header saying the user supplied it; nothing places an upload there for
you. Never
write a statement from memory — the file is attested as copied from the cited work. Ask the user
only for the citations you could not access, naming each and what you tried (`orch.mjs ask`); resume once all are in.
A cited work nobody can access (the user cannot either): write what was tried to
`discovery/cited_sources/<key>.unavailable` (non-empty) and `--resume`. The citation is then taken
as printed and NOT checked: its verdict detail starts "[cited source unavailable — not checked …]"
(a witness refuting the quoted statement itself still stands), the ledger notes "cited source NOT
checked", and V6 lists every result resting on it as conditional with the reason. A `.txt` supplied
later wins and re-opens its verdict.

### Results a proof invokes by citation

A proof may invoke a published result by citation ("where we use [key, Theorem n] in the last inequality"). V1
lists each such place for its agent, which accounts for it in `discovery/core_refs.json`:
`proof_citations` registers it — a `cited` node with `cited_in: <the proof's result>`, whose text is
the proof's own passage (the citation and the step it gives) and on which that result depends — or
`dismissed_citations` reads it as a pointer, a borrowed method, a result proved here or a
definition (a V1 lint warning, which the referee may contest). What you see and do:
- the cited-source checkpoint asks for the source of each registered result, as for any cited
  node: fetch it as "Cited sources" says. One file per bibliography key serves every result cited from that work,
  so it must hold each statement; "the referee could not check … against the source shown" names
  the result and the file that lacks it.
- the node stands only for what the passage attributes to the cited result; a step the source does
  not give, or hypotheses the proof does not establish, is a finding on the proof's result (the
  runner moves an error graded on the node there), repaired like any other.
- `drift` on the node, or on the proof's result for a dismissed citation the proof relies on, is
  V1's reading of the citation and goes back to V1 (dismiss it, change its units, register it).
- round A lists a registered result among the cited results, once however many proofs invoke it.
- a warning "the proof of X invokes [key, Theorem n] …: a published result used inside the proof,
  with no cited node of its own" remains for what cannot be registered — a run transcribed before
  the accounting, a key missing from the parsed bibliography, the proof of a cited result. Settle
  each before the Lean stages: fetch the source and compare the step with the statement it invokes;
  then leave it to the prover (elementary, or in the libraries) or write it into the result's
  repair as an explicit assumption attributed to the source (key and locator).

### The watcher and the page

What the user sees and does on the page is in "The local UI" (Who acts on a run); what the agent
does with the watcher is in its guide ("Mechanics", "Who decides"). The rest:

- **Attaching.** `orch.mjs watch` records your session in `runs/<slug>/orch.json`, so the page shows
  "<agent> attached"; the record lapses when your session ends. The watcher looks at the run every
  10 s (`THEOREMCHECKER_ORCH_TICK_MS` changes that). The page resumes a run, and applies a promotion
  round, only while a session is attached (an apply resumes the run when it ends); with none, it
  tells the user to start one in this repository and ask it to orchestrate the run.
- **An apply of a promotion round the user started** has no heartbeat and writes no log line; when
  it ends without applying the round the watcher prints what it said — stopped part-way, or
  refused before anything was applied: what to do is under "Promotion rounds: the orchestrator's
  procedure" (Applying).
- **Messages.** "Reply" on a request of yours and "Message the agent", each with files attached if
  the user wishes, are stored in `runs/<slug>/orch_messages.json` and return your watcher — whatever
  the run is doing, and at once when one is already on file — with the id (`m<n>`), the request it
  replies to, their words and each file's path (`runs/<slug>/uploads/<m<n>>/<name>`, printed from the
  run directory and absolute, with its size and sha256). The page tells the user a message is
  delivered only while your watcher is armed (attached with none armed, it says you will read it
  when you next check). A finished run (phase `done`) is not watched: a message on its page waits
  until the user points you to it in the session. `orch.mjs reply` marks what it answers as handled. "Clear conversation"
  archives the thread (`orch_messages.archive.json`; ids count on, uploads stay): a message the user
  cleared before you acted on it is no longer reported. A file attached in answer to a cited-source
  request is the source ("Cited sources").
- **Reported issues.** "Report an issue" on a comment that asks no decision of the user is stored in
  `runs/<slug>/owner_objections.json` (optional) and wakes your watcher with the node, the comment
  and their words.
- **The page's math.** The page draws math with KaTeX, then MathJax; a formula neither reads is
  shown as source and listed in `runs/<slug>/logs/ui_math_failures.json` (rewritten as the run's
  files change). Each is fixed by an entry `"<tex>": "<replacement>"` (the listed source, the same
  math in commands KaTeX reads) in `runs/<slug>/ui_math_overrides.json`; the page picks it up.

### Unattended runs

`tools/scripts/batch_orch.mjs` (Linux, Codex) is the attached session of a few runs for a machine
where no interactive agent session stays open — a server, or a job of a scheduler. It keeps their
watches armed and, at each event, continues the run's own Codex conversation (`codex exec resume`, a
fresh one every 15 events) with the guide and that event; the agent acts and ends its turn, so nothing
spends tokens between events. It takes runs from a queue file (one per line: `<slug>` for a run on
file, `<slug>=<source>[::<main file>]` for a new paper; `#` comments) or from its arguments. What the
user starts on the page (a resume, their rulings, the apply of a round) is started by the driver
attached to that run: the page writes `runs/<slug>/start_request.json` and starts nothing itself.

    cd tools && source scripts/node_env.sh
    node scripts/batch_orch.mjs --toolkit <toolkit> --queue <queue file> --runs 2

| Flag | |
|---|---|
| `--toolkit <path>` | the toolkit (required) |
| `--queue <file>` | the queue file to take runs from; slugs may also be given as arguments |
| `--runs <n>` | runs at work at once (default 3); a finished run is replaced from the queue |
| `--batch` | take `--runs` runs, see them through and exit, instead of replacing each finished run |
| `--full-auto` | start the new runs it takes with `verify --full-auto` |
| `--hours <h>`, `--grace-min <m>` | a time budget: `--grace-min` (default 20) before it ends, stop the agents and runners, put the unfinished runs back at the head of the queue and exit 75, for a successor to take them |
| `--max-agents <n>` | agent turns at once (default 2) |
| `--brief <file>` | the owner's standing instructions, given to every agent |
| `--model <m>`, `--effort <e>`, `--sandbox <mode>` | the Codex agent's model (default `THEOREMCHECKER_MODEL_CODEX_VERIFY`), reasoning effort (default `high`) and sandbox (default `codexSandbox`, else `workspace-write`) |

It exits 0 when nothing is left, and 76 when the Codex login's usage limit is reached (the reason is
appended to `<queue>.stopped`). Each agent and run bills the Codex login of the driver's `CODEX_HOME`.
Logs: `runs/<slug>/logs/batch_*` and the driver's own output.

### Recommendations

The decision card shows your recommendation as your reply, above the buttons, and the status strip
names it; with `redo`, the card prints your `--guidance` and "Redo with guidance" starts from it,
for the user to edit. "Accept all recommendations" sends your recommendation for every repair the
user did not decide by hand — on a promotion checklist it enters it on every entry and new topic
left undecided and applies the round — and is disabled while one has none (a `redo` without
`--guidance` counts as none). A recommendation is on ONE proposal: `recommend … repair <node>` is
bound to the repair pending on that node now and is refused (exit 65) when none is pending; after a
redo, or a later round's new suggestion on the node, the earlier one is no longer shown (and is
dropped from the file). A promotion recommendation must name an entry of the batch on file (exit 65
otherwise), or a new topic by `topic:<path>` (kinds `accept` | `decline`). The user sees every
`ass:pin-owner-<n>` the annotated paper states as a margin card tagged "Author's reading", and the
weakening rulings recorded with `orch.mjs decided` under "Review the agent's decisions".

On a full-auto run (`verify --full-auto`) the recommendation that completes a decision carries it
out: on the repairs, `verify --resume` with the rulings recommended; on a round, `propose --round <R>
--apply --recommended`, which enters the recommendation (its reason as the note) on every item still
pending. Either is started detached by `orch.mjs` (output in `runs/<slug>/logs/full_auto_<time>.log`)
and recorded under "Review the agent's decisions": one entry per repair, one per round. `orch.mjs ask`
there needs `--owner-only`; a weakening ruling is the agent's, recorded with `orch.mjs decided`.

The page typesets what you write for it as TeX (the rules are in the orchestrator guide's "Reporting
to the user"); a flag or a command goes in `\verb|…|`, which is shown as typed, because `\texttt`
sets `--` as a dash.

### Reading a run

1. Parser warnings (`[verify] V1: parser: …` in the log, and `discovery/v1_lint_warnings.json`) say
   what the parser deliberately left out or bound by heuristic. A proof "attached to no result" or
   "bound … by proximity" is yours to check against the tex before V1 is trusted.
2. `discovery/v1_5_review.json`: `verdict`, `summary`, and one entry per node with `detail`,
   `witness` (for `error`, with `witness_regime` `in_scope` and `witness_instance`; a `degenerate`
   witness was turned into a `bookkeeping` grade whose condition excludes the degenerate case — its
   `detail` starts "[degenerate witness"), `reading` (for `pinned`), and `graded`: `fresh` (this pass graded it) or
   `carried` (a clean verdict an earlier pass gave on the same basis — what the node's referee was
   shown: the node, the text of what it uses directly, the verdict of each result it uses, the
   symbols those name; an edit deeper down re-opens it only when the verdict of a result it uses
   then reads otherwise, in the same pass — `delta review: … carried verdict(s) re-opened`; the
   `[verify] V1.5: delta review:` line says how many of each). Referee
   grades vary between passes on borderline items; the stable core (a witness you can run) is what
   you report.
   The referee reads every result closely, level by level, each under the final grades of the results
   it uses, and errors are fixed as they are found, so the results above a repaired one are read
   against its corrected version. In detail: the referee is always sharded (every call on `MODELS.codexVerify`): nodes are graded in
   DEPENDENCY ORDER — level 0 definitions and assumptions, level 1 results using no other result
   still to grade, … up to the main theorems — each node once, in one shard, and each shard sees the
   final verdicts of the results its nodes use as binding ("DEPENDENCY VERDICTS"); one global pass
   after the last level checks cross-node wiring, key results, patch consistency and the fixer's
   rejections — including that what a result's PROOF takes from the setup or from another result's
   hypotheses reaches that result (else a wiring fix: `add_depends_on`, `wire_into`, or a
   `new_assumption` wired into every user). A condition an earlier pass appended (`ass:bk-*`) is
   shown to the shard re-grading its node and is KEPT unless the referee drops it on purpose
   (`bookkeeping_dropped`, with why). On a delta pass it sees only the nodes graded, their
   neighbours and the key results
   (`global pass: delta scope — …` in the log), and the excerpts in place of the whole paper while
   `core.transcribed.json` is the one a global pass last read whole (`v1_5_review.json`
   `global_paper`). A result using a lemma graded `error` with no confirmed repair is `unclear` with
   detail "depends on <id>, graded error" (the fallback). FIX AS YOU GO: once a level settles, a
   refuting `error` with an in-scope witness (or a repair graded as weakening the claim) on it PAUSES
   the upward grading — no level above, no global pass; V1.5 returns `patch` (or halts for the owner's
   ruling on a weakened repair / at the cap, yours) with exactly those nodes, `state.verify.level_pause` records where, and
   `v1_5_review.json` carries `paused: {level, ids, ungraded}`. The next pass keeps every verdict the
   paused pass gave on an unchanged basis, grades the repair first (levels `fix-L<k>`), logs `level
   k: n error(s) → fixer round r → confirmed m/n; continuing`, then goes on
   upward with the corrected forms binding. The fallback `unclear` remains for an error nobody repairs
   (the owner withdrew or declined it, the fixer found it unfixable). Each interleaved round counts
   as an error round of its level; a paper assumption graded `error` goes to the fixer, who replaces
   its printed text (or, when it has no units of its own — running prose, or printed inside a
   result's environment — restates each result using it).
   An `error` the referee marks `follows_repair` (the node fails only because a repaired result it
   uses now states less), on a node not repaired itself that uses directly a restated repair, is
   marked `follows_repair_of` and goes to the fixer as a `consequence` finding — never an error of
   the paper; left over at the end it is reported
   unresolved. A grading that breaks the output contract twice sets that node (or symbol) aside:
   its verdict on file is kept, not confirmed, and it is graded afresh next pass.
   Shards are sized by content (`referee.shard_bytes`, default 70 KB of statement + proof excerpts)
   and per-kind ceilings (10 hypotheses / 6 lemmas / 3 theorems), at most `referee.max_concurrent`
   calls at once (default 6); a result longer than the byte budget is graded alone. The `referee` keys of
   `theoremchecker.json` (`max_concurrent`, `shard_bytes`, `shard_max_hypotheses`, `shard_max_lemmas`,
   `shard_max_theorems`, `symbol_effort`) are the only referee settings; there is no switch for the
   sharding. A fresh node carries `shards: ["L<k>-<i>"]`. The log line
   `sharded referee: levels: L0 n0 (…) · L1 n1 · …; K shard(s) (6+6+5 nodes), 1 global pass; prompt
   bytes X total (shards …, global …); C call(s) in Ts` is the pass's cost; `shard L1-2: <ids>` lines list each
   shard's nodes, `level L1 graded: …` each level, `<id>: unclear — depends on …` each result held
   back by an errored lemma. Per-call replies: `codex_raw/v1_5_shard_*`,
   `v1_5_global__*`; the prompt of each under the same tag in `discovery/prompts/`; totals in
   `discovery/v1_5_referee_metrics.json`.
   The SYMBOL referee runs first. Before any result is graded, the referee reads every symbol of the
   symbol table against the paper: where the paper introduces it (its first defining sentence —
   "where Δ = …", "let", "denote" — found by searching the flattened paper), any later sentence that
   defines it again, and one or two places it is used. For each symbol it checks that the recorded
   type and definition say what the paper's symbol is (a wrong or missing meaning is corrected in
   the table) and settles the conventions that live with the symbol: random or fixed, what it is
   conditional on (say, a training sample), its domain, index ranges, a meaning that changes later
   in the paper. A settled reading is binding: it is added to every result using the symbol, shown
   to the referees grading those results, and marked once in the annotated paper ("Clarification
   (symbol …):") after the sentence introducing the symbol. The symbols are graded in groups of
   about ten, one call per group. Symbol grades are kept in `discovery/v1_5_symbols.json`; a later
   pass re-grades only a symbol of which something its referee was shown changed: its entry (type,
   space, signature, role, definition, the symbols it refers to) or the entry of a symbol it refers
   to, the sampling model, the passages where the paper introduces it, defines it again or uses it,
   the results listing it, or what a repair's corrected statement now says of it (the sentences
   naming the symbol; the whole statement of a result the symbol's reading names). A symbol left
   open is kept with its wording while none of that changes (`--fresh-review` re-grades all). The
   symbol calls run at codex reasoning effort `"referee": { "symbol_effort": "low" | "medium" |
   "high" }` (default `"medium"`; the calls grading results always run at high). The log line
   `symbol referee: G of N graded (C carried), …; effort E` gives what was graded, its cost and the
   effort. In the files: `v1_5_review.json` `symbols` (and
   `discovery/v1_5_symbols.json`, the cache) holds one grade per symbol — `meaning` ok | drift (with
   `fix`, the corrected type / space / def the runner wrote into the table), `ambiguity` ok | pinned
   (with `reading`) | unresolvable, `redefined_at` — plus `introduced_at` (flat and original line). A
   pinned symbol reading is the symbol's entry in the table — never an assumption or a Lean hypothesis;
   every later stage reads the table. A reading has a GENERAL part (`reading.reading`, the entry's
   `def`: what the symbol means wherever it is used) and SCOPED clauses (`reading.scoped`, the entry's
   `scoped`: `{results, text}`, what additionally holds in those results). A result's referee and its
   verdict basis read the general part and only the clauses tagged with the result or one it rests
   on, so a clause reworded for one result re-grades that result and its users, not every user of the
   symbol; on a re-grade the referee keeps each part that still holds word for word (a clause it
   does not mention stays; only an explicit `drop` removes one). A symbol is graded afresh when its
   entry or introducing passage moved, when a corrected statement changed in a sentence naming it —
   or anywhere, for a result its reading names — when the results using it changed, or when a clause
   is tagged with a result that is gone (a re-keyed `*:cor-fix-*` block). The core carries the shape
   the F stages were built on: each symbol's `space` and `def`, and a `sampling_model` with one
   entry per setting the paper works in (V1 writes them; lint rule (s)). The log
   lines `symbol shard 1: <names>`, `symbol verdicts: …` and `symbol referee: G of N graded (C
   carried), …` (also the tail of the `sharded referee:` line) say what happened; per-call files are
   `codex_raw/v1_5_symbols*`. A misread symbol (random treated as fixed, a conditional probability
   read as unconditional) is the first thing to check when a result is refuted.
3. `report.md` and `bundle/` (after V6): what each holds is in "The report and the corrected-paper
   bundle". The report names results as the paper does ("Theorem 2", never a node id) in its
   plain-language part ("What was wrong and what was done", "Clarifications (not errors)", "What was
   proved in Lean, and what was not", "The corrected paper"); its "Technical appendix" carries, by the run's ids, the per-result buckets,
   "Errors by root cause" (downstream casualties grouped under the first false step), "Corrected
   version" and "Suggestions to the authors" (the pins). 
4. `annotated/ANNOTATIONS.md` (after V6, after every V1.5 pass, and at every owner halt): every
   annotation of the marked-up paper (repairs' proofs too: kind `corrected proof`, `\vsStep` on each
   printed step a repair replaces with `\vsCorrectedStep` after it, else one `\vsProof` block after
   the proof) and anything unlocated; check that each claimed error sits on
   the sentence you re-derived, and send the user `annotated/<main>.tex` (and the PDF when it
   compiled).

### F stages: the plan review

The review of the Lean plan (F1.5) proposes no repair of the paper: a plan it bounces goes back to F1
with its findings, and the run stops for the agent only when F1 cannot act on them.

The F1.5 checkpoint on the FIRST plan is yours (a re-plan of an approved plan, after a rewind,
continues into F2 when its F1.5 review passes; `--stop-after F1.5` still stops). Read `formalization/formalization.md` (the environment's Lean
encoding, then each node) and `formalization/plan.json` (`nodes[<id>]`: `disposition`, `reuse`,
`notes` — the planned statement and proof route). Check:

- depth: every result and step the paper owns is formalized (`define-local`); only a published,
  source-matched input may stay cited, and nothing hard is relabelled as cited or deferred;
- reuse: the world and constructions reuse the base libraries or the toolkit where one fits, and
  each bypass says why;
- fidelity: each planned statement is the corrected paper's, with the node's hypotheses (pins
  included) and nothing the paper does not grant; nested "Suppose also" parts keep their chains.

A defect is fixed by a rewind (`--from-stage F1`), never by editing the plan; then `--resume`.
An F1.5 review that bounces the plan goes straight back to F1 — the reviewer's findings are the
correction, the entries they name the scope of the re-plan — for up to 6 rounds per plan. The run
halts for you (`flags.general_review_halt`, the findings in the message) when that budget is spent,
when the review names no plan entry, or when the reviewer rejects the plan as rooted in the core.
Read the review (`reviews/stage_1.5_to_1_attempt<N>.json`) and rule: a paper error goes through
V1.5 (`discovery/patches.json`, `--from-stage V1.5`); a plan defect F1 did not fix gets your
directive in `flags.f1_revise_directive` and `--from-stage F1` (a fresh budget); a finding you rule
out, `--from-stage F2` past the review (a plain resume is refused while the gate is set, and one that
only clears it re-runs the reviewer on the same plan, with no record of your ruling) — each with
`--clear-gate general_review_halt`. The gate is cleared
as the run is entered, whatever stage the re-entry starts at; `--from-stage V1`/`V1.5` also starts
the F1↔F1.5 budget over (a new core is a new plan review). An F1 that answers `blocked` (the core
incoherent, a result outside Lean's reach) halts with its message and F1 not completed: rule as on a
rejected plan — a resume plans again.
An F2 that finds a definition or lemma the plan presupposes and no library holds halts `MISSING
ARCHITECTURE BLOCKED` (`flags.missing_architecture`, the items in `flags.missing_architecture_items`:
name, purpose, suggested location) and every resume is refused while one is unbuilt. Build each
under `Papers/<Slug>/` at its suggested location, check it, then `--resume`: the gate opens once
every name is found in the toolkit, the papers tree or a base library. An item F2 does not need:
delete it from `flags.missing_architecture_items` in `state.json` (an empty list opens the gate)
and say why in `flags.f2_scaffold_directive`.
A plan the plan gate refuses on the plan and the core alone (kind, members, coverage, hyps) never
halts F2: before the scaffolder is called, or after its sync-back wrote such a plan, F2 sends it
back to F1 through the F1.5 pre-lint, within the F1↔F1.5 budget. When that budget runs out on the
same entry, read the pending `flags.scaffold_redirect`: a finding that asks for a shape the gate
refuses is yours to rewrite into one inside the planned kind.

### F stages: the proof-review loop

F2–F4 run as one loop and route each blocker: hint · build-substrate · fix-source · unclear ·
bank-partial. A paper-statement finding halts as a proposed rewind ("Re-entries and proposed rewinds"). A Lean-side
escalation (`scaffold-mismatch`: the Lean says more or less than the frozen statement and its
binding readings) is yours to rule on: when the reviewer is right, write `flags.scaffold_redirect`
in `state.json` — the directive (what is wrong, the faithful form) followed by the line
`Declarations to edit (one obj_id per line, verbatim):` and one `- <node id>` per declaration — then
`--resume`: an F2 pass applies it before the review loop re-reviews. Giving the F stages such a
directive is the orchestrating agent's own action: writing
`flags.scaffold_redirect`, and `--clear-gate` on a cap gate once the root has changed, need no
confirmation — do them, then report them. Two more directives are yours the same way, both standing until you clear them
in `state.json`: `flags.f2_scaffold_directive` (a faithfulness constraint read by every F2 pass) and
`flags.f3_filler_directive` (a proof hint — lemma names, a tactic route, the Mathlib API — given to
every proof-filler call; a hint only: it never licenses a changed statement or an added hypothesis).
A sub-agent driving a run does not write them: it reports
the directive text and the orchestrator applies it. A Defer item
(a plan node `gate:true`) does not halt the run: it is scaffolded as an assumed gate and disclosed in
the report until discharged. To discharge one, build it under `Papers/<Slug>/` (never `Toolkit/`),
check it, and rewind F2.5 (`--from-stage F2.5`) to wire it in. A node is reviewed
once per basis (its Lean, NL, pins and rulings — `runs/<slug>/review_basis.json`); a `hint` halt
where a reviewer flags a node it graded `matched` before, on an unchanged statement, against a
binding reading it was shown, is a reviewer flip: `--resume` re-reviews it once (there is no
accept-review lever yet); a second flag on it is a real dispute to reproduce — a third review on the
same basis is never dispatched, and the run halts `[standing-drift]` until the Lean or a ruling
changes it. Never answer an F-stage flag with
`--reject-finding "<node>: …"` on a REPAIRED node: that withdraws the repair and reports the V1.5
finding as the owner's rejection. Green is not proved:
before reporting, a full build of the paper's modules, a source grep for `sorry|admit|axiom`, and
`#print axioms` on each key result. F5 writes the docstrings (the docstring contract: NL translation with a crosslink per hypothesis;
placeholder phrases such as "the stated condition" fail the gate) and `nl_links.json` (each paper
result linked to its Lean theorem row by row; advisory — its `uncovered` segments are paper text no
Lean row states, worth a look before reporting, and the `F5 nl-links: … WARNING:` line says when
results are unlinked, rows unanswered or many rows share one list: the page then shows those rows
as not linked row by row); V6 the report (see "Reading a run").

**The iteration budget.** A cap gate that blocks `--resume` names itself; clear it with `--resume --clear-gate <flag>` only
after something at the root has changed (a re-roll of a non-deterministic reviewer is not a retry).
The proof loop's iteration budget (F3) bounds a loop that is not progressing: before every pass
the runner counts the open `sorry`s and the proved declarations of the paper's Lean tree, and,
while a proof is open, halts after 20 iterations that beat neither record (fewer open `sorry`s
than ever, or more proved declarations than ever), or at 300 iterations in all. The halt states
the measure, which is the runner's and not the prover's summary. An F2 pass and `--clear-gate`
restart it; after a hand edit of the Lean at a halt that lowers the proved count, clear the gate.

### Promotion rounds: the orchestrator's procedure

What a round offers, what an entry shows and how the user decides it are in "Promoting results into
your toolkit". The agent's part and the mechanics:

**Promotion is always the owner's decision, in every mode, `--auto` included.** At both promotion
points present the checklist to the user: per entry its title, reference, content in words, why it
is reusable, the evidence (recurrence, closest existing results, the checker's verdict), and your
recommendation (accept, accept_with_edits, generalize_first, decline or defer) with its reason. Put
each recommendation on the paper's page as well (`orch.mjs recommend <slug> --toolkit <toolkit> <A|B>
<proposal id> <kind> "<why>"`; a new topic by its key `topic:<path>`, `accept` or `decline`): it is
shown beside its entry, and the user may decide and apply there. The checklist's "Accept all
recommendations" enters your recommendation on every entry and new topic the user left undecided and
applies the round; it is disabled while one has none, so record one for each. Then wait for the
user's decision on every entry; never decide or apply on your own, and never write a `decision:`
line into a promotion checklist yourself, not even for an item that changes nothing. A Tricks entry
qualifying by judgement alone is a first sighting: recommend `defer` — it returns when another paper
proves the same pattern. Gardening is different: it reorganises what is already in the toolkit, and
the owner does not decide it (see "Gardening: the procedure").

**The rounds.** Each stops the run with a checklist `<toolkit>/doc/proposals/<slug>.<A|B>.md` (a dry
run's under `runs/<slug>/proposals/dry_run/`).

- **Round A** (phase `proposals_A`, after F1). An accepted result is built by the study pipeline
  before the paper's proofs, and the F1 plan is pointed at it. `--defer-proposals` skips the round
  when given before it is proposed (once its checklist exists the flag says so and changes nothing:
  defer the entries there). A round already decided (applied or deferred) stands when the run is
  re-entered with `--from-stage V1.5|F1` — the cited results are the same — and is held again only
  after a new transcription (`--from-stage V1`); a run already past F1 is not sent back to it.
- **Round B** (phase `proposals_B`, after V6 of a full F run). An entry MOVES as proved with its
  helper lemmas, or — when its Lean is stated over the paper's own setting (its types, reading pins,
  assumptions: `paper_shaped`, detected mechanically) — its GENERAL form is built by the study
  pipeline and the paper's result is re-proved as its corollary (the paper keeps its statement;
  restored if the re-proof does not build). A classical or recurring result is proposed on that path
  rather than skipped for being paper-shaped; `generalize_first` asks for it on any entry. A verbatim
  move of a paper-shaped result is refused. Generality is enforced, not only judged: a paper-shaped
  result, or one whose proof never uses some of its hypotheses, takes the general path (built without
  them).

**An entry.** The helpers proving a result go with it and are never their own entry. The bar an
entry meets is stated under its title: Foundations (a standard, textbook result stated in the base
libraries' vocabulary — a domain library such as Causalean included — and other Foundations results)
or Tricks (reusable within the owner's lines of work: recurrence in ≥ 2 papers, an existing Tricks
topic, or the curator's written judgement), with the graph's signal when it disagrees. The statement
is given in words with Unicode math (the general statement only; how the paper's result relates to
it is its own line, "In the paper"). Recurrence in the owner's other papers counts identical
statements, and the same pattern over each paper's own definitions once the curator confirms it —
the main evidence; "deferred before in …" when it returns. A duplicate of an existing declaration is
declined automatically (round A points the plan at it). Every toolkit declaration lives in its
module's topic namespace, `<lib>.<Division>.<topic path>` (a name is put there automatically); a name
already declared is refused. A toolkit module imports what it uses (a study-built header is trimmed
after the build), never `Mathlib` / `Mathlib.Tactic`. Every module sits under a topic of the topic
tree (`doc/taxonomy.json`; the layout lint refuses others), and a new topic is its own checklist
item the owner decides before anything moves into it. The curator and the gardener run on Claude,
the checker on codex.

**Applying.** `accept_with_edits` may change placement and presentation (division, target_module,
proposed_name, title, reference) on any entry, the paper's own results included; a `content` edit is
refused on one of the paper's own stated results. Write the user's decisions into the checklist, then
`theoremchecker propose <slug> --round <A|B> --apply`. An apply refused before anything was applied
shows the user why on the page: an entry still undecided or a checklist that does not parse is
theirs to answer — tell them — and anything else (a lakefile, a batch that no longer matches the
Lean) is yours to settle before the round is applied again. Moves and builds go
through the toolkit gate (`lake build`, `#print axioms`, statement invariance, the layout lints, the
index). A move that fails its gate is NOT undone: every file stays as the move wrote it, the apply
stops with the failing step and its log, and it is yours to settle — repair the Lean by hand (the
target toolkit module, the paper files that used the result; never weaken a statement: the gate
compares them), then run `propose <slug> --round B --apply` again, which runs the gate on the files as
they stand and goes on with the rest. A cause that will recur is fixed in the mover as well, with a
test. To give a move up, put the files back from `runs/<slug>/proposals/move_journal.json` (each
file's original bytes), delete it and `move_pending.json`, and take the entry back to the user for
another decision. Statement invariance is Lean's own check that a promotion
changes no claim: `candidate_scan` hashes what every declaration of the paper and the toolkit states
(a theorem's type, a definition's type and value) before and after, under the move's new names, and
the hashes must agree — a move renames, a rebuild in general form changes one proof, neither changes
a statement. On the strength of it the run's current F4 receipts are carried to the new Lean, so a
run that later re-enters the F stages re-reviews only what really changed. The same exe keys those
receipts: each F4 entry and the F5 audit run `candidate_scan --fingerprints` once on the built tree,
and a target is skipped only while both reviewers' receipts match its declaration's `closure_hash`
— what Lean elaborated for its statement and for every toolkit or paper declaration the statement
reaches — so an added `open`, `variable`, option, import, comment or proof re-opens nothing. A
toolkit whose `CandidateScan.lean` predates a hash is not checked (the apply says so; F4 then
reviews every target and the F5 audit refuses, naming the scan): copy it from
`templates/toolkit/`. A moved module imports only what its declarations use (the source imports
are the logged fallback). The ledger records each decision and each new declaration (`tier: main`
for the result, `tier: aux` + `owners` for its helpers); round A resumes into F1.5, round B
finishes the run. Report what entered the toolkit, any corollary not kept, checker disagreements,
and any toolkit-graph regression the apply printed. `--resume` on a finished run without a round B
opens one from the report on file (V6 is not re-run). A round already held and settled — applied,
deferred, or with nothing to propose — is not held again when the run is re-entered
(`--from-stage V1.5` and later): only a round still waiting for decisions is set aside and proposed
afresh, and a new transcription (`--from-stage V1`) starts both rounds over. To propose a paper's
deferred entries again, `propose <slug> --reopen-deferred` — on a finished run only (phase done or
failed); on a re-entered run it is refused until the run finishes again.

Studies, the toolkit graph and `toolkit-health` are described in "Promoting results into your
toolkit". In addition: a study runs scaffold → fill → one review pass (all codex) → coordinate into
the toolkit (Claude) under the same gate; a study that stops prints its message and its exit, and a
plain `--resume` continues only one interrupted mid-phase (or a scaffolder escalation whose
requirement you corrected) — one halted at a cap needs the `--clear-…-cap` flag it names. The
promotion rounds build their accepted entries this way (`study_<paper>__<id>`). The toolkit graph is
derived from the Lean (`candidate_scan --graph`), never written by hand; its main view collapses
helpers into their main results.

### Gardening: the procedure

**Gardening.** The graph's findings on MAIN results (split, merge, unused, stale, duplicate, a result a
base library now states, a module outside the topic tree, a Foundations result using a Tricks one, a
declaration outside its topic namespace, an umbrella import, a module building on a more applied
topic — one finding per module) go to the gardener (one Claude call; none when nothing changed and
nothing is found) together with the main view and the full SOURCE of every module a finding names
or that changed since the last list; it also raises what it reads there (a result in the wrong
topic, one fact stated in two forms). The end of round B — or `theoremchecker garden` on demand —
writes `doc/proposals/garden-<stamp>.md`: per item what it shows, the change (relocate, merge,
split, retire, remove, rename, trim_imports, cross_reference — a split or relocate extends an
existing module of the target topic before it creates one) and a recommendation; findings left as
they are become one summary line. The procedure:

1. YOU decide each item — the owner cares what the toolkit holds, not how it is laid out. Read the
   item and the code it names, write its `decision:` line (accept / decline / defer) with a `note:`
   giving your reason, and do not ask the user. Exception: an item that RETIRES or REMOVES a result
   (the toolkit would no longer hold it) goes to the user in plain words — what the result says,
   why it would go — and waits for their decision. (`garden --dry-run` writes the list from the
   graph's findings with no gardener call, every item `decline`: a smoke test, not a round.)
2. The toolkit must be clean and committed before any edit (`git status` in the toolkit; commit or
   set aside unrelated changes first) — git is the undo.
3. Carry out each ACCEPTED item yourself, by editing the Lean as the item describes (lean-lsp,
   `lake build` of the module and its users): move declarations with what they need, follow every
   rename in the toolkit and the papers, keep `omit … in` / attribute prefixes with their
   declaration, change no paper statement (only proofs and imports of papers may change).
4. `theoremchecker garden --verify <file> [--items g-1,…]` checks the edits against the committed
   toolkit: only the toolkit's Lean, its barrels and `doc/` changed; toolkit and papers build;
   `#print axioms` standard; no sorry/admit/axiom; every paper theorem/lemma statement unchanged
   (renamed toolkit references followed); header and layout lints; the index regenerated; the graph's
   health against `HEAD` (regressions reported). Full logs: `runs/_garden/verify/<stamp>/`. On
   success it records the decisions, renames (`renamed_from`) and moves in the ledger.
5. Fix what it reports and verify again; when an item cannot be made to pass, revert it with git
   and record it as declined with the reason. When it passes, commit the toolkit and tell the user in
   a line or two what moved (topics and results in words, no Lean layout detail).

### Render and contract checkpoints

Two checkpoints, never an owner waiver, both before any owner decision and F1:

- RENDER CHECKPOINT (the renderer's defect): a block the renderer itself could not set (a proof-step
  fragment escaped, `\textbackslash` / `[U+XXXX]` / an odd `$` outside a verbatim print) or a pdflatex
  error. When the block comes from a text in the run's record (a transcription, a reading, a patch),
  correct it there; otherwise it is the renderer's — fix it with a test (`annotate_tex.ts` /
  `units.ts` / `annotated_paper.ts`) and record it.
  Once fixed, check with `theoremchecker annotate <slug>` then `theoremchecker lint-annotated <slug>
  --toolkit …`; `--resume` renders again and the run continues where it stopped.
- A model-written fragment that fails its compile check is the MODEL's, never the renderer's: the run
  routes it back to its producer (symbol referee or V1.5 referee: the verdict is graded afresh next
  pass with the compiler's line; fixer: a scoped fixer round) and continues into that producer's
  pass. No model re-typesets a text. Only when it still fails after
  that pass does the run halt at the CONTRACT CHECKPOINT, listing fragment, producer and compiler line:
  read the lines (a text no model re-writes — the owner's words, the transcription — is corrected in
  the run's record; a recurring prompt or contract gap is fixed in that producer), then `--resume`
  routes them again.

- NOT a checkpoint: a compile error the paper's own source has too (an old paper on a newer TeX
  installation). A failed compile is set against one of the unmodified `source/` (compiled once per
  source, `logs/source_compile.json`); the errors both have are reported as a note — in the log, the
  halt's "Review the annotated paper" line and `ANNOTATIONS.md` — and only an error the annotated
  copy alone has is a render checkpoint. The annotated TeX and the page do not depend on the PDF. If
  you want one, the smallest neutral edit in a COPY of the source (the `TC_EDITS.txt` procedure under
  "Parser gaps") is optional. In the bundle, such errors are listed in `TODO.md`
  under "The original source does not compile on this installation", apart from a correction's.

`annotate <slug>` exits non-zero listing both kinds (the PDF is still written).

### Re-entries and proposed rewinds

A re-entry never repeats work whose inputs did not change. `--from-stage V1` with the source
unchanged and `discovery/core_refs.json` present materializes `core.json` from the reference core +
`patches.json` with no agent call (`[verify] V1: entry: revise …`); only a changed source (or no
reference core) extracts cold — to force that, move `core_refs.json` aside. V1.5 grades only nodes
whose basis moved and carries the rest; `--fresh-review` (with `--from-stage V1` or `V1.5`) re-grades all (use it when you distrust an
earlier pass, not by habit). So for a patch-only change — a missing hypothesis, a corrected
statement — write or extend `discovery/patches.json` and `--from-stage V1.5`; never `--from-stage V1`
for it, and never hand-write a patch the fixer would write anyway.

To re-run an old run under the current design: `--resume --from-transcript` reuses the finished V1
transcription and redoes everything after it. `core.json` becomes `discovery/core.transcribed.json`
again; the patch file, the V1.5 review and its carried verdicts, the paper-error ledger, the findings
history, every pending or decided receipt, the counters, and all F-stage output (`formalization/`,
`proposals/`, `reviews/`, `graph.json`, the report) are moved under
`runs/<slug>/_archive/from_transcript_<stamp>/` (with the state as it stood) and cleared; the next
step is a fresh V1.5 that grades every result and symbol under the current referee configuration.
The owner's rulings stay: pinned readings (`--reject-finding`) and the findings they withdrew. It is
refused when there is no transcription, when V1 has not finished or is rewriting the transcription,
when the source files changed, or when the transcription differs from the one V1.5 accepted — then
use `--from-stage V1` (rebuilds the core from `core_refs.json`; re-extracts only when the source
changed) or `--from-stage V1.5 --fresh-review` (re-review as it stands).

When a reviewer of the Lean (F2.5, F3, F4) finds that the paper needs a hypothesis it does not
state, that a result is wrong as stated, or that its wording admits more than one reading, the run
stops and proposes a repair of the result it names; the agent approves or rejects it against the
paper. A proposed clarification lists the result's pinned readings, so that it can be rejected when
one settles it. A finding about the Lean code rather than the paper, or one that names nothing in
the paper, stops the run for the agent without a proposal.

An F2.5/F3/F4 `fix-source [statement-wrong]` or statement-wording `unclear` escalation is never
routed silently: the run halts (every mode,
`--auto` included — in auto mode YOU judge, without asking the user) and prints the finding — F
stage, route, statement, axis, the repair it would ask for — with the receipt in
`state.verify.cross_stage_rewind` (`pending`, `presented`). A finding may name an assumption or
definition of the core: the finding lands on that node, and the fixer replaces its printed text
(or, when it has no units of its own, restates each statement using it). All paper-statement findings of
ONE review pass arrive as one batch (`targets`), one decision and one round for all of them; to
approve only some, delete the others from `state.verify.cross_stage_rewind.targets`, then `--resume`.
A target naming no node of the core (a Lean declaration) is listed as left out. Check each finding
against the paper:

- it is right (a hypothesis the paper never states, a claim false as printed, a genuine second
  reading) → `--resume` approves it: V1 patch mode on the statements named, V1.5 grades what
  changed, F1 re-plans. A `clarify` finding is answered by writing the intended reading into the statement (a
  pinned reading is folded into the text) and reported as a clarification, not an error.
- the paper already grants it, or the reviewer misread the Lean → `--resume --reject-rewind "<where
  the paper grants it>"`: the reason goes into the receipt and onto the statement as a note, and the
  F stages continue from where they halted (for a batch: every finding). The same finding on the
  same node (same axis) is a note from then on, never another halt — for a clarification, any
  clarification on that node (the ruling says how it is meant); for an error, the same content.
- the reviewer misread the PAPER and only its author could say how it is meant → ask the user
  (`orch.mjs ask`); rule with their answer as `--resume --reject-finding "<the
  reading>"` (as below: pinned, binding, withdrawn).

The fixer may also reject an F-stage finding in patch mode (`rejected`, pointing to where the paper
grants it); the next V1.5 pass rules: upheld → a note, and F continues; overruled → the fixer must
patch it (a round). What halts at F2.5–F4 is Lean-side (a Lean declaration named,
`redo-math` on a helper, laundering, strikes): handle it, then `--resume`.

### Patch caps

Patch rounds are capped, and a cap never fails the run: it stops for the attached agent, which rules
on it. The constants are in `tools/src/verify/types.ts`. Two counters: `patch_rounds` (ERROR rounds
— a defect of a paper claim, capped at 3 PER DEPENDENCY
LEVEL (`MAX_PATCH_ROUNDS_PER_LEVEL`) — the level of the whole core the grading paused at, `global` for the final global pass and
F-stage rewinds — with a whole-run backstop of 3 × the core's level count, at least 6
(`MIN_PATCH_BACKSTOP`)) and
`refinement_rounds` (REFINEMENT rounds — a clarify rewind, a round whose only errors are repairs
graded correct but non-minimal, a note graded unclear, or a split remark; cap 3,
`MAX_REFINEMENT_ROUNDS`), plus one limit per node that spends no round: a suggested weakening the
referee rejects more than `MAX_SUGGESTION_REJECTIONS` (2) times goes back to the fixer no more
(`verify.suggestion_rejections`). The log names the counter that moved. A round due
at its cap never fails the run: it halts (every mode) with `state.verify.cap_reached` — the counter,
the rounds spent, the level and its nodes, the findings the round would carry, what the fixer's
patch file proposes; a halt on the suggestion limit alone says "SUGGESTION LIMIT" and carries
`suggestions` + `suggestions_only`. The log reads `error round k/3 at level Lx (total t/backstop)`. Judge
that receipt against the previous rounds: converging (fewer or narrower findings) →
`--resume --clear-patch-cap` (one more window; on the suggestion limit, the fixer answers those
nodes again); oscillating, or the same weaker-condition dispute
twice → `--resume --accept-cap`; a suggestion the referee keeps rejecting because the finding
misreads the paper → `--resume --reject-finding "<node>: <reading>"`. The loop ends: at the refinement cap the repair is accepted as
correct but non-minimal (the referee's weaker condition recorded on the patch) and the run
continues to F1, so Lean certifies it; at the error cap and on the suggestion limit V6 reports (a confirmed repair stays
repaired, an unrepaired error is refuted).
Each of `--clear-patch-cap` and `--accept-cap` is refused unless the run stopped at a cap.

### Repairs are replacements

A repair is one operation: REPLACE printed units (a statement's, an assumption's or definition's own
text, or proof steps) by new text. A hypothesis is added by restating the
statement with it; the note says which. A result that uses a repaired one and now needs its
hypothesis is restated too (a consequential patch, `consequence_of`, "Changed to follow the repair
of …"). An assumption or definition with no printed units of its own (running prose, or printed
inside a result's environment) is repaired by restating each result that uses it; a repair of an
assumption or definition needs no proof note. An algorithm (an `algorithm` float or `algorithmic`
block; also one no result refers to, transcribed from the running text) has units of its own, one
paragraph per step (`<label>/<step>/<unit>`), and is repaired in place, once: one op per step, the
step's command stays, a control line (`\IF{…}`) is replaced by a control line — the annotated paper
marks the step inside the float, a control line's replacement after it (the corrected paper lists
that one in `TODO.md`). algorithm2e or unknown markup is left uncut (a parser warning in
`v1_lint_warnings.json`) and repaired as a node with no printed units. Two repairs may replace overlapping printed text only
identically. The corrected texts and `supersedes` (the hypotheses whose printed text a replacement
rewrites) are derived from the ops on every read; a result's repair lists in `drops` the hypotheses
its corrected statement no longer uses. The build unwires the superseded and dropped hypotheses,
unwires a repaired hypothesis from a result restated to follow it (one with no printed units: from
the results its entry names in `consequence_of`, else from every restated result using it), and removes a repaired, superseded or dropped hypothesis
or definition no result uses. A `patches.json` that does not fit its schema (an op other than a
replacement, say) is the operator's input error: the stage checkpoints naming the path; fix the
file, then `--resume`.

### A repair may split a result

When what is true of a printed result is a general statement plus special cases, or several
conclusions resting on different conditions, the repair is written as an author would write it: the
theorem keeps what is not moved, and each case becomes a corollary or a proposition of its own,
checked by the referee and proved in Lean separately. Nothing is dropped by a split, and a statement
the paper prints correctly is never restructured.

When the true content of a printed result is several results, the fixer may return it as blocks,
the way an author would write it. Two cases: (1) a general statement mixed with special cases that
hold under their own conditions; (2) several conclusions bundled in one statement that do not rest
on the same conditions or the same results (a summary collecting results proved separately) — then
each conclusion, or each group resting on the same conditions and results, is a block. The node
keeps what is not moved to a block (its ops) and each block is an entry of the patch's
`corollaries` (`{title, statement, follows, adds}`). A block is one of two KINDS, derived from its
proof and never stored (the field, `split_from` and the `cor-fix` ids keep the word for both): a
**corollary** when `follows` cites the parent by `\ref` of its label — a
consequence of the corrected statement — and a **proposition** otherwise: a separate claim the
printed statement bundled in, resting on other results. (A parent without a label can be cited by
nothing: its blocks are corollaries.) The fixer does not write the label; it cites the corrected
statement exactly when the proof uses it, and the referee holds it to that (a citation that is
decoration, or a use without a citation, comes back as a `minimality` grade on the block: a
refinement round, never an error of the paper). The kind sets the name everywhere — "Corollary
5.1.1", "Proposition 5.2.1", one running number per parent across both kinds — and the dependency:
only a corollary block depends on its parent; a proposition block does not, so a later change of
the parent does not re-open it (it still carries the parent's readings, and `split_from` still
places it). Each block is a RESULT OF ITS OWN: a
statement node `<thm|lem|prop>:cor-fix-<hash>` of the parent's kind with `split_from: <parent>`
(the hash is of the parent and the statement by its meaning, so a re-run emitting it again keeps
its grades, plan and receipts), depending on its `adds`, the results it cites and — a corollary —
the parent, its proof the field `follows` (the block's complete proof, at the paper's own level of detail,
citing by `\ref` every result it uses; the referee grades it as that proof). The paper does not
print it, so it has no `tex_locator`: it is shown at
its parent — a blue block "Corollary of Theorem N" (`\vsCorollary`) or "Proposition stated in
Theorem N" (`\vsSplitProposition`) after the parent's environment (whose statement
is then one red block, the printed text, and one blue block, the corrected text) in `annotated/`
and on the page (its own Lean drawer once formalized), its proof inside the block ("Proof."); a row
after the parent's in the report. In the corrected paper (`bundle/corrected_paper/`) it is a corollary or a proposition of the
paper (in the paper's own environment of that kind when it has one) placed by the paper's convention
for the parent: after the parent's proof when that follows
the statement, else its statement after the parent's and its proof after the parent's proof where
the paper prints it ("Proof of Corollary N" / "Proof of Proposition N"). V1.5 grades it like any
repaired statement, its proof as written (it need not go through the parent); the F stages plan,
scaffold,
prove and review it as a separate Lean theorem. Every result that used the parent uses its
corollaries too (the printed result is the set). A finding on a corollary — the referee's, an
F-stage reviewer's — is answered on the PARENT (the fixer returns that entry whole; the directive
says which corollary); you never name a corollary in `--accept-repair` and its kin. A corollary
the fixer no longer emits (or rewords: a new id) leaves the core with every edge to it, and its
`-- @node:` declaration is reconciled away at the next F2 like a renumbered pin. A split never
hides a weakening: what a repair gives up is judged on the parent TOGETHER with its corollaries —
a conclusion moved to a corollary is kept, one in no block is given up — and a weakening grade on
the parent or on a corollary turns the whole repair into the suggestion the owner rules on, the
receipt (`weakening_repair.items[].corollaries`), the halt message and the page listing the
corollaries with the proposed statement. A split result reads `repaired` only once its corollaries
are certified in Lean too.

The referee also checks the FORM of a repair it confirms (`split: {why}` on the verdict): a
corrected statement the fixer wrote that mixes a general claim with case-by-case conclusions, or
that still bundles conclusions resting on different conditions or results, is
sent back ONCE to be re-emitted as a statement with blocks (a directive finding of axis
`split`). It is a remark, never a grade: the repair stays confirmed, the round is a REFINEMENT
round (no error round is spent; never asked at the refinement cap), nothing halts and nothing goes
to the owner. The fixer's answer stands (`state.verify.split_requests`); when it returns one
statement again the run goes on and the report carries the remark as a note. Never on a statement
the paper prints, on an accepted weakening, or for a "moreover" under the same hypotheses.

**The umbrella form.** When ONE printed theorem or proposition mixes several conclusions, each
holding under different assumptions, and nothing in it is the statement's own main claim, the split
form would leave the result an arbitrary fragment. The repair then says `umbrella: true` (no ops):
EVERY conclusion — or group resting on the same conditions and results — is a proposition block,
and the result is an umbrella over them. In `core.json` it keeps its id, kind, label and locator,
carries `umbrella: true`, its text is the pipeline's fixed sentence ("The following propositions
hold, each under the conditions stated in it." — shown to a reader as "Propositions 5.2.1–5.2.6
hold, …") and it DEPENDS ON its blocks; no block rests on it (a block whose proof cites it is a
fixer violation). It stays the paper's named result, a key result if it was. V1.5 grades the blocks
and, on the umbrella node, only whether they together cover the printed statement (what no block
keeps is given up — a weakening, routed as any). It has NO Lean declaration: the F stages read the
core without it (no plan entry, no `@node` tag, no graph node, no
review target; a plan entry or tag naming it is refused as naming no core node), and it is
established exactly when all its blocks are: the report derives its bucket (never better than its
worst block) and its axioms (the union) from their rows, MATCH.md lists it with them, the page
lists its propositions in its drawer and draws it above them in the proof map. A statement with a
main claim plus special cases or consequences keeps the split form. The referee's form remark
(`split`) runs both ways under the same bounds: a split parent left a mere fragment → asked once
for the umbrella; an umbrella over a statement that plainly has a main claim → asked once to
restore it.

To convert a split repair already on file WITHOUT a fixer round (yours to decide — nothing the
paper claims changes): `--resume --umbrella <node>` (or `--umbrella "<node>: <title>"`, the title of
the new block). What the corrected statement still states becomes one more proposition block
(appended; its proof the proof the patch holds for the node — the printed proof when the patch
left it as printed), the patch becomes the umbrella, `core.json` is rebuilt and the run re-enters
at V1.5, which grades what changed; F1 then re-plans. The result's plan entry is moved to the new
block (same Lean name), so F2's tag reconciliation retags its declaration instead of scaffolding a
new one. Refused, with the reason, when the node has no blocks, is an umbrella already, or has a
block that is a corollary of it (the statement then has a main claim). A referee pin on the result
is not carried: the re-grade of the new block states it again if it is still needed.

### Weakened repairs and owner readings

A repair never weakens the paper. When only a weaker version of a result holds, the strongest such
version is found: for a lemma or another intermediate result it is used at once and reported
"narrowed"; for a main theorem the run stops and the owner decides, on the paper's page (the
decision card offers the same choices as the flags below).

The fixer may only make an intended reading explicit, add a condition a competent reader treats as
implicit (finite moments, measurability, a density exists, sizes diverge), or tighten a HYPOTHESIS
to the paper's actual setting, null or framework — the conclusion unchanged. A different
conclusion, limit, rate, constant or object, a substantive hypothesis excluding cases the paper
claims, a narrower scope, or dropping the result is a WEAKENING: the fixer answers `unfixable` with
`suggested_repair` (the strongest true version, a full patch body; what it gives up in its note), and the referee
grades a weakening patch `error` + `weakens_contribution` (routed to the same place, never back to
the fixer). Only a MAIN THEOREM halts for an owner ruling (the user's, on the page — you recommend: the orchestrator guide's "Who decides"): a core
statement of kind `theorem` / `corollary` or a fixer `key_results` entry. On anything else (lemmas, propositions, definitions,
assumptions, clauses of non-theorems) the runner APPLIES the suggestion itself as a patch
(`accepted_weakening`, `narrowed_by: "runner"`, ledger `auto_narrowed`), logs one line per node, and
the next V1.5 pass confirms it; the report shows it `repaired` with "narrowed: …" and the annotated
paper as a normal repair whose note ends "This narrows the lemma: …". No halt. If a narrowed lemma
leaves a main theorem unprovable at full strength, that theorem's own halt is where it is ruled on
(fix as you go shows the narrowed lemma in its binding dependency verdicts). Only a pending
suggestion on a main theorem halts, in every mode, `--auto` included, with
`state.verify.weakening_repair` (node, printed claim, proposed claim, what is given up, witness) —
main theorems only. It is the user's decision, made on the paper's page: you
recommend, they rule, `--auto` included. `--resume --accept-repair` applies the
suggestions as patches (`accepted_weakening`; V1.5 confirms them; reported `repaired` with
"contribution narrowed: …"). `--resume --decline-repair "<reason>"` reports each result `refuted` (`not_determined` when the paper leaves its statement open)
(claim, witness, the declined suggestion) and descopes it from Lean with every result resting on
it, key results included; the run goes on. `--resume --reject-finding "<the owner's reading>"`
says the FINDING is wrong (a misreading of the paper — say, a probability the paper states
conditionally on the training sample, read unconditionally): the printed statement stands, the
reading becomes an owner-pinned reading `ass:pin-owner-<n>` wired into the node (binding for the
F stages like any pin; "Clarification (author):" in the annotated paper), the ledger entry says
`owner_decision: "finding rejected"`, the referee's error on the node is overruled (`ok`,
`owner_overruled`) and may not be raised again on it (the same finding on the same node and axis →
a note; at an F-stage presentation "the same finding" is matched by content, so a different finding
on that node still reaches you), and the report lists it under "Findings withdrawn by the owner";
V1.5 then grades what changed and F1 plans with the pin. A ruling has ONE record: its
`patches.json` `owner_readings` entry, whose `withdraws` lists the findings it withdrew; the ledger
stamp, the owner's `rejected_rewinds` entries and the withdrawal notes are derived from it at every
`verify` invocation. To revoke a ruling, `--resume --remove-reading <id>` (never edit the file and
plain-resume: only the flag rebuilds `core.json` and re-enters V1.5): the entry leaves the record with
its ledger stamp, ruled-out entry and withdrawal note; a finding it had withdrawn that no repair on
file addresses leaves the ledger, so the referee grades the node as printed and raises again an
error that still holds. `--resume --edit-reading "<id>: <new text>"` rewords one, keeping its id,
node, kind and `withdraws`. After either, V1.5 re-grades the nodes whose basis moved (the pinned
node and what depends on it; a mere re-typesetting of a reading moves none) and the F stages start
again at F1 on the new core. The owner sees every `ass:pin-owner-<n>` the annotated paper states as
a margin card tagged "Author's reading" and can edit or remove it there (the page runs these flags),
so a reading you entered on the owner's behalf is theirs to correct. A further `"<node>: <reading>"` on a node already ruled
on adds a second reading and withdraws nothing more. The same flag answers a proposed F-stage rewind. `--resume --redo-repair "<node>:
<guidance>"` (repeatable) discards that node's suggestion: the fixer repairs it again in V1 patch
mode with the owner's guidance as a binding OWNER GUIDANCE block (plus its SERVES block), follows it
or answers `unfixable` saying why; V1.5 confirms the result; a redo that again ends in a weakening
suggestion halts with the guidance shown; ledger `owner_decision: "redo"`, `guidance`. A bare answer
covers the batch; to rule item by item in ONE resume, name nodes — `--accept-repair thm:a`,
`--decline-repair "thm:b: <reason>"`, `--reject-finding "thm:c: <reading>"`, `--redo-repair
"thm:d: <guidance>"` — with at most one bare answer covering the items no other names; items no
answer names stay pending and are presented again (the receipt closes `ruled` when rulings differ).
To split a rewind, delete from its `targets` (the rest are presented again). At ANY halt you may
also withdraw the finding on one node that misreads the paper, an APPLIED repair included:
`--resume --reject-finding "<node>: <reading>"` (repeatable) removes the node's patch / unfixable
entry from `patches.json` (the printed statement stands), pins `ass:pin-owner-<n>`, marks the ledger
`finding rejected`, rules the finding out, withdraws every refutation recorded on the node, lifts a
pending cap halt, and re-enters V1.5; `"<node>: bookkeeping: <condition>"` records an
`ass:bk-owner-<n>` side condition instead (binding, listed with the bookkeeping conditions, and
written into the paper like every added condition). A node of the pending receipt takes the batch form. By hand: a patch in
`patches.json` with `accepted_weakening: true` (+ `given_up`) and `--from-stage V1.5` formalizes a
weaker version the owner chose; the referee then judges only whether it holds.

**A side condition that withdraws nothing** may be added at any stop: `--resume --add-condition
"<result id>: <condition>"` (repeatable) records a condition the paper takes for granted that the
checker does not carry on that result (a setup fact stated elsewhere, the well-definedness a lemma
presupposes); findings and applied repairs stay as they are, and V1.5 re-checks the result under
it. The condition is written into the paper handed back: a note at the result in `annotated/`, the
last paragraph of its statement in the corrected paper — so write it as TeX, in the paper's macros (a reading or condition that is not plain-ASCII TeX is refused when it is recorded: rewording it later changes the reviewed core and sends the run back to V1.5). Use this, not the `bookkeeping:` form of `--reject-finding`, when the finding should stand.

On the page a reading's Edit and Remove are shown while the run is stopped.

### Mechanical drift fixes

The model never types paper text: a statement's source is its env id (the whole body); a
premise's is an env id, a run of its NUMBERED SENTENCES, or an anchor slice for a clause inside a
sentence; a `(ref)` violation means an anchor did not cut and
names the node. Do not add text normalizations to the lint — a verbatim mismatch means the runner
or parser is wrong, not the model.

The transcription lint checks mechanical facts only — verbatim text, environment coverage, anchors
that cut, pointers quoted. Which `\ref` is a hypothesis, a proof use or a mention is NOT a lint
question: the referee grades drift and states the edge as a mechanical `fix`. Do not add wiring
heuristics to the lint; if the referee is wrong about an edge, that is a referee-prompt matter.

The same holds for every model text: only exact checks block it (schema,
compile, unclosed delimiter, missing field, node id, dropped unit). What a text says is the
referee's to judge. Never add a phrase list or wording heuristic; a wrong grade is a
prompt matter.

The referee states a drift correction as data when it is a structural edit (`fix` on the node:
`add_depends_on`, `remove_depends_on` on a result; `wire_into`, `unwire_from` on an assumption or definition; `extend_to`, `new_assumption`),
and the V1 runner applies it to `discovery/core_refs.json` itself before any agent round; when every
finding had a fix and the core checks clean, the round needs no agent ("core revised
mechanically"). Only findings without a fix, or whose fix the runner rejected (logged with the
reason), reach the transcriber. When you hand-patch, prefer the same edit shapes; a shape that
recurs and the referee cannot express goes into `directive_edits.ts` with a test.

### Drift

A referee verdict that still carries `drift` nodes (the revise cap was reached) is not a graded
paper: correctness grades on drifted nodes rest on text that is not the paper's. Do not report it
and do not move on. Either hand-patch the drifted nodes in `discovery/core_refs.json` (the
directive in `discovery/v1_revise_directive.json` and the referee's `detail` say what is wrong) and
`--resume --from-stage V1`, or re-enter at V1.5 so the loop gets more rounds. The revise cap is PER
DRIFTING NODE (`MAX_REVISE_ROUNDS_PER_NODE = 3` in `src/verify/types.ts`; drift repeated on a node
after a round stops at once, and the error rounds' backstop bounds the whole), so a node drifting
for the first time late in the loop still gets its own rounds — raise the constant only when the
same node's drift was still shrinking at its third round. Drift that
REPEATS between rounds on the same nodes is a structural block — a lint rule or prompt clause
forbidding the correct transcription — and is fixed in the pipeline (general rule + test) before
the paper is re-run. Only a drift-free verdict is reported. Drift on a REPAIRED node is the repair's
defect, not the transcription's: it goes back to the fixer as `patch rejected` ("the repaired text
does not fit the paper around it"). Drift with no edit named on an unrepaired assumption or
definition that a result's scoped symbol clause reaches is neither: its words are the paper's and
the referee held a result's reading of a symbol against them. The run checkpoints at once, with no
transcription round: if the reading and the repair stand, a plain `--resume` grades the node afresh
(`--from-stage V1.5` would set aside a pending owner receipt); else correct the reading
(`discovery/v1_5_symbols.json`) or the repair (`discovery/patches.json`) first.

### Authors' note macros

A draft often carries its co-authors' markup: a colour wrapper around an edited passage, comments.
A new run reads the plain cases away when it flattens the paper, so no sentence is cut inside a
wrapper — by fixed rules on the macro's DEFINITION in the paper, never by its name:

| class | a one-argument macro whose body is | what the run reads |
|---|---|---|
| K keep | exactly `#1` under colour, highlight or grouping (`{\color{c} #1}`, `\textcolor{c}{#1}`, `\hl{#1}`) | the argument in its group, `{…}`; without the braces when it spans several sentences |
| H hide | empty | nothing |
| C comment | `#1` handed to a note command (`\todo{#1}`, `\marginpar{#1}`, fixme's `\fxnote{#1}`) | nothing |

A macro is read only when every definition of its name (the paper's, and a `.sty` / `.cls` the
source ships) is such a definition, they agree, none sits in a conditional or a group and none
comes after `\begin{document}`. Eight package commands are read by name when the paper loads the
package and nothing it ships defines the name: changes' `\added` (K), `\deleted` (H), `\replaced`
(K, the new text); soul's `\hl` (K); ulem's `\sout` (H); todonotes' `\todo`, `\missingfigure` (C);
`\marginpar` (C). Everything else is left as written: a body that prints anything besides its
argument (a tag, a font, a strike), several arguments, a direct `\textcolor{c}{…}`.

Nothing is removed silently. Every removed or dropped text is in `discovery/author_notes.json`,
whole; the parse log and the report's parser notes say what the paper was read with ("K \lp (8),
\rj (28); C \todo (3) removed"); each removal inside a statement or proof is a parser note naming
the result — shown to the referee grading it — and saying when the text lost all, or more than half,
of what it had. Lines keep their numbers. The annotated paper keeps your wrappers (a mark inside
one closes it and opens it again); the corrected paper writes a file that held such a macro as it
was read, and says so in `TODO.md`.

What the reader declines and that matters is ONE parser note per macro, for the orchestrator: a
macro of the paper's it does not read whose argument spans several sentences (a unit cut inside it
is not balanced TeX), or a use it could not take (no braces, an argument that does not close or
holds part of an environment). The note gives the macro, its definition, the number of such uses
and the first one's file and line, and what to do: if it is a note macro, remove it by the
smallest neutral edit in the run's copy of the source (`runs/<slug>/source/`), record the edit in
`pipeline_issues.md`, and run it from V1 (a changed source is extracted cold).

The reading is recorded in `envs.json` (`note_macros`, with its version) and replayed from there: a
run on file from before it existed, or one started with `THEOREMCHECKER_NOTE_MACROS=off`, stays
read as written on every `--resume` and `--from-stage` (they revise the transcription against the
text it was cut from); a run whose replay would give another flat text keeps the text it has, with
a note. The reading takes effect when a paper is read cold: a new run, or a run whose source changed.

### Parser gaps

LaTeX has no grammar for "a theorem", so the parser cannot be finished: a construct it does not
cover is absorbed in the run's record (the order of steps is in the orchestrator guide's "When the
pipeline itself fails").

TeX the parser mis-cuts (a proof running on past its end, a result stated in prose, a cut inside
math, a label typo, a supplement in its own `\documentclass`): first `discovery/segments.json` (add
a missed result, attach a proof, extend a statement — re-applied on `--resume`); else a COPY of the
source directory with the smallest neutral edit (a missing `\end{proof}` or QED mark, an
environment around a result in prose, the label fixed, the supplement `\input` before
`\end{document}`) — never a change to mathematics — listed in `TC_EDITS.txt` in the copy, run from
V1. Proofs that are whole sections with no delimiter: `--targets` the results that have proofs and
note the rest as not checked.

On a V1 checkpoint the remaining violations say what to settle: a verbatim rule prints the first
differing character and the expected JSON spelling. Every stored statement, proof, condition and
construction is whole TeX ("`theoremchecker verify`", Statements and proofs are whole TeX): a parse
cut inside math is a parser gap, and lint rule (m) sends a node slice cut inside
math back to the agent.
