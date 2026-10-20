# LeanSmith

Verify a paper's mathematics in Lean. LeanSmith transcribes a LaTeX paper's results (V1),
referees them for faithfulness and correctness (V1.5), formalizes and proves them in Lean against
Mathlib, the domain libraries you chose and your personal toolkit (F1–F5), and reports what held,
what was wrong and how it was repaired (V6). Every run lives in your toolkit (`runs/<slug>/`, the
Lean under `Papers/<Slug>/`).

You run it through a coding agent (Claude Code or Codex) started in this
repository: the agent runs the pipeline, acts at each halt, and brings up a local web page where
you read the paper as the run marks it and make the decisions that are yours.

https://github.com/user-attachments/assets/1fa20ae4-cb9c-40d0-95f3-33fbb3904d35

*Install with your agent, ask it to verify a paper, and review the run on the local page. The run
shown is the built-in demo (`leansmith demo`, see "Try the demo" below).*

## Install

> **If you are a coding agent installing this for someone**, these rules come first:
>
> 1. After step 1 (which needs only git and Node), run the prerequisite check (step 2,
>    `leansmith doctor`) before anything else, show the user its output, and install nothing
>    it did not ask for.
> 2. **Ask the user, never choose for them:** (i) where their toolkit should live, and (ii) which
>    domain libraries they want. Ask first what kind of papers they will check, show them the
>    output of `init --list`, and say which domains fit that work, what each library covers and
>    what each costs in disk (rule 3) — then let them choose. "None" is a valid answer (Mathlib
>    only); a library can be added later. A library marked `not yet available` cannot be
>    installed.
> 3. **Ask before** any step that logs in to an account, installs system software (elan, Node,
>    TeX, pipx, zstd), or is long or large. Measured on a fast connection and a fast disk: a
>    Mathlib-only toolkit is about 8 GB and 5 minutes; with Causalean about 15 GB and a few
>    minutes more when its prebuilt cache is fetched (step 4), and a long compile from source
>    (about 2,600 Lean files, not timed) when it is not; StatLean adds about 3.5 GB (and about 45
>    minutes on 32 cores without its cache). So the statistics domain needs about 20 GB free:
>    tell the user the figure for their choice before starting. A real `verify` run spends the
>    user's model quota: never start one unasked.
> 4. Never edit the pinned versions (`tools/data/libraries.json`, a toolkit's `lean-toolchain`,
>    the Mathlib `rev` in its `lakefile.toml`) to make something build.
> 5. When the user wants a library that is not offered, or one marked `not yet available`, do not
>    improvise a `[[require]]`: it will not build or will not import. Follow `doc/PORTING.md`,
>    and tell the user first that a port is hours of work or more.
> 6. Before running a paper, read `.claude/skills/leansmith/SKILL.md` (Claude Code loads it
>    as the `leansmith` skill; Codex reads the file, as `AGENTS.md` says).

Installation has been exercised on Linux and Windows (Git Bash); the Windows check used an
existing Lean installation and shared Mathlib cache. macOS and a clean Windows prerequisite
installation have not yet been checked. On Windows, start with **Windows setup** below.

### What you need

| | What it is | Check | Install |
|---|---|---|---|
| git | | `git --version` | your package manager |
| Node ≥ 20.20.2 | runs the pipeline (`tools/package.json` `engines.node`) | `node -v` | [nvm](https://github.com/nvm-sh/nvm): `nvm install 22` |
| elan | the Lean toolchain manager; it fetches the pinned Lean by itself | `elan --version` | `curl https://elan.lean-lang.org/elan-init.sh -sSf \| sh`, then a new shell |
| `codex` CLI, logged in | most model calls: extraction, referees, Lean scaffold, proofs, reviews | `codex login status` | `npm install -g @openai/codex`, then `codex login` |
| `claude` CLI, logged in (recommended, optional) | the Lean plan, the second reviewer of the final Lean review and toolkit curation; with `codex` alone these roles run on `codex` | `claude auth status` | `npm install -g @anthropic-ai/claude-code`, then `claude` and `/login` |
| `lean-lsp-mcp` on `PATH` | lets the model workers query Lean | `lean-lsp-mcp --help` | `pipx install lean-lsp-mcp` (or `uv tool install lean-lsp-mcp`) |
| `pdflatex` (optional) | the annotated paper's PDF, and a check that repaired text compiles; without it both are skipped and you get the TeX only | `pdflatex --version` | TeX Live / MacTeX |
| `tar`, `unzip` | unpacking a paper given as an archive | | usually present |
| `curl`, `zstd` (Causalean, StatLean) | fetching a library's prebuilt cache (step 4) | `zstd --version` | your package manager |

You can do without a GPU and Python (see "Library search" below).

Disk a toolkit uses: about 8 GB with Mathlib only, about 15 GB with Causalean, about 19 GB with
StatLean as well; keep a few GB spare. Mathlib's downloader also keeps its compressed files in
`$XDG_CACHE_HOME/mathlib` (default `~/.cache/mathlib`), shared by every toolkit on the machine.

### Accounts and cost

A run is long and token-heavy: every result of the paper is transcribed, refereed, planned,
formalized and proved by model calls, with review passes between, and it stops for decisions on
the way. Time and cost vary widely from paper to paper: start with a short paper, or limit a run to a few
results with `--targets`. Each run records its usage (`runs/<slug>/logs/token_usage.jsonl`; the
paper's page sums it).

- **Which models** (`tools/src/models.ts`): on `codex`, `gpt-6.1-sol` for every role (V1 extraction and
  fixer, V1.5 referee, F1.5, F2 scaffold, proofs, F2.5–F4 reviews, F5); on `claude`,
  `opus` (F1 plan, curation). Your accounts must have access to them. To use other ids, set
  `LEANSMITH_MODEL_CODEX_KERNEL`, `LEANSMITH_MODEL_CODEX_VERIFY`,
  `LEANSMITH_MODEL_CODEX_MECH`, `LEANSMITH_MODEL_CLAUDE_MAIN`; the pipeline was tuned on
  the defaults.
- **Subscriptions (default).** The workers use the `codex` and `claude` logins already on the
  machine (a ChatGPT plan and a Claude plan that include the CLIs).
- **API keys instead.** In `tools/config/local.json` set `"authMode": "api"` (or only
  `"openaiAuth"` / `"anthropicAuth"`), and `"openaiApiKey"` / `"anthropicApiKey"` (or
  `…ApiKeyFile`); or set `LEANSMITH_AUTH_MODE=api` with `OPENAI_API_KEY` /
  `ANTHROPIC_API_KEY`. API mode requires the OpenAI key: lacking it, the run stops at start (a subscription is used only in
  subscription mode). With no Anthropic key the claude roles run on `codex` (next item).
- **With `codex` alone.** Two accounts are the default. When `claude` is absent, logged out, or in
  API mode with no key, its roles (F1 plan, second F4 reviewer, curator, gardener, study coordinator) run on `codex`, on the
  kernel model at high effort; the run's first log lines and `leansmith doctor` say which CLI
  runs them. To choose yourself, set `"claudeRoles"` to `"claude"` or `"codex"` in `local.json` (or
  `LEANSMITH_CLAUDE_ROLES`); a run keeps the CLI it started with across resumes unless you
  set one. The pipeline was tuned with `claude` in these roles; the `codex`-only path is new and
  has yet to be run on a real paper, and its two F4 reviewers are the same model. Under
  `codexSandbox: "danger-full-access"` the read-only roles (second F4 reviewer, curator, gardener)
  run with write access, as the `codex` referees do.
- **A second Claude account** for the workers: `claudeConfigDir` in `local.json` (or
  `LEANSMITH_CLAUDE_CONFIG_DIR`).

### Windows setup

Use **Git Bash** for the numbered steps below. `source scripts/node_env.sh` is a Bash command;
it does not run in PowerShell or Command Prompt. Install Windows programs, then close and reopen
Git Bash so it sees their updated `PATH`. WSL is a separate Linux installation: keep its tools
and paths separate from this Windows setup.

1. Install [Git for Windows](https://git-scm.com/downloads/win), including Git Bash, and a
   Windows [Node.js installer](https://nodejs.org/en/download) satisfying the version above.
   The `nvm-sh` link in the table is for Unix shells, not a native Windows Node installation.
2. When `doctor` reports elan missing, use the upstream
   [Windows elan instructions](https://github.com/leanprover/elan#installation). For Windows
   PowerShell 5.1, use `curl.exe` explicitly (bare `curl` is an alias):

   ```powershell
   curl.exe -fL -o elan-init.ps1 https://elan.lean-lang.org/elan-init.ps1
   powershell.exe -ExecutionPolicy Bypass -File .\elan-init.ps1
   Remove-Item -LiteralPath .\elan-init.ps1
   ```

   Reopen Git Bash afterward. The pinned Lean is downloaded when the toolkit first needs it.
   For Lean MCP, install [uv for Windows](https://docs.astral.sh/uv/getting-started/installation/)
   if neither uv nor pipx is available, then run `uv tool install lean-lsp-mcp` and follow any
   `PATH` instructions it prints. The optional Python embedding stack is not needed.
3. After cloning and installing npm dependencies (step 1 below), set `gitBashPath` in
   `tools/config/local.json` to your actual Git Bash executable. In Git Bash, discover it with:

   ```bash
   cygpath -m /bin/bash.exe
   ```

   Copy that result into the existing JSON field, for example:

   ```json
   "gitBashPath": "C:/Program Files/Git/bin/bash.exe"
   ```

   A custom Git installation may instead be under another drive. Use forward slashes in JSON;
   a single Windows backslash is an escape. `doctor` checks this executable before declaring
   the machine ready, and the library cache fetcher uses the same setting.
4. Continue with `doctor`, library selection and toolkit creation below. In Git Bash use paths
   such as `/d/research/my-toolkit`, or quote a Windows path with forward slashes:
   `"D:/My Research/my-toolkit"`. Quote paths containing spaces in every command.

If you run an individual npm command from PowerShell instead, `npm.cmd` and `npx.cmd` avoid
PowerShell's `.ps1` execution-policy restrictions. Return to Git Bash for the Bash command blocks.
For optional PDF output, add the Windows TeX distribution's executable directory to `PATH`;
both `doctor` and compilation recognize `pdflatex.exe`.

The measured Mathlib-only Windows setup took about 15 minutes, including repository checkout
and cache extraction, with Lean and compressed Mathlib archives already present. A first download
can take longer; the five-minute estimate above is for a fast Linux setup.

### Steps

Every command below runs in Bash (Git Bash on Windows), from `LeanSmith/tools` after
`source scripts/node_env.sh`.

**1. Clone and install the tools** (about a minute).

    git clone https://github.com/Jiyuan-Tan/LeanSmith.git LeanSmith
    cd LeanSmith/tools
    source scripts/node_env.sh
    npm install
    cp config/local.example.json config/local.json

An npm update notice does not prevent installation. Review dependency audit findings separately;
do not run `npm audit fix --force` as part of setup, since it can change dependency major versions.

- `node_env.sh` stays silent when a suitable Node is on `PATH` (or under nvm). If it prints
  `node_env: no Node >=20.20.2 found`, install Node and source it again.
- `config/local.json` holds this machine's settings (ignored by git). The copy works as it is on
  Linux and macOS; the defaults also apply when the file is absent. On Windows set `gitBashPath`.

**2. Check the prerequisites.**

    npx tsx bin/leansmith.ts doctor

It prints one line per item — `ok`, `MISSING` (required) or `absent` (optional) — with the install
command under each missing one, then the model ids your accounts need, and ends
`Ready: every required item is present.` (exit 0) or `Not ready: …` (exit 1). Fix what is missing
and run it again. It reads versions and login states only, free of model calls. Lines marked
`(optional)` are for information: with one missing the verdict is still `Ready`.

**3. Choose your libraries.**

    npx tsx bin/leansmith.ts init --list

Mathlib is always installed. **Every domain library is optional**: you choose.

| Domain (`--domains`) | Optional libraries it installs |
|---|---|
| `causal` — causal inference | Causalean |
| `statistics` — statistics and probability | Causalean, StatLean |
| `learning` — statistical learning theory | FoML |
| `optimization` — optimization | optlib |
| `general` — general mathematics | none (Mathlib only) |

Or pick libraries by name: `--libraries optlib,FoML`. Causalean already brings FoML and optlib.

A library is a help: a result absent from the installed libraries is proved inside the paper's
own Lean, at a cost in running time and model quota and with the same correctness. Rough guide — causal
inference, experimentation, panel and design-based work: Causalean; classical statistics
(estimation theory, hypothesis and multiple testing, asymptotics, time series): StatLean as well;
other mathematics: Mathlib alone.

**4. Create your toolkit** — a separate git repository of your own that holds your curated Lean
library, every paper's Lean and every run record. Choose where it lives (outside the LeanSmith
clone is simplest) and pass your choice from step 3:

    npx tsx bin/leansmith.ts init ~/my-toolkit --domains general

The build takes a while: meanwhile, take the tour of the page ("Try the demo" below; an agent
setting this up starts it for you and gives you its link).

On a terminal, `init` without `--domains` / `--libraries` asks; without a terminal it refuses and
prints the list. It

- copies `templates/toolkit/`, writes its `lakefile.toml` (the domain libraries, then Mathlib at the
  pinned revision) and `leansmith.json` (the base libraries retrieval searches);
- makes it a git repository with a first commit;
- downloads Mathlib's prebuilt cache (`lake exe cache get`) and each chosen library's own (see
  "Prebuilt caches" below), builds the toolkit, checks each fetched library by building it (it
  should only replay), and indexes each domain library that comes without an index (`--no-build` skips
  these).

`--owner "Name" --email you@example.org` set the owner recorded in `leansmith.json` and the
author of the toolkit's first commit (default: your git configuration).

Success ends with `[init] done. Use it with --toolkit <path> …`. The first `lake` call also makes
elan download the pinned Lean. Common failures:

- `lake exe cache get failed` — a network problem or a full disk. In the toolkit, run
  `lake exe cache get` again, then `lake build`.
- `git commit failed` — set `git config --global user.name` / `user.email`, then commit the
  toolkit yourself.
- `… exists and is not empty` — `init` only creates a new toolkit; give it a new directory.

Then commit what the build added (`git add -A && git commit -m "lake manifest"` in the toolkit),
and push the toolkit to a **private** repository of yours: it holds the run records of the papers
you check. Do not move the toolkit or the LeanSmith clone afterwards: the toolkit refers to
the clone by relative path (vendored libraries, retrieval notes).

**Prebuilt caches.** `init` fetches Mathlib's prebuilt cache (`lake exe cache get`) and, for a
library you chose that publishes its compiled files, that library's cache too. It then builds
each fetched library to check the cache: that build only replays (`Replayed …` lines, linter
warnings included) and `init` reports `N replayed, 0 compiled`. (`init`'s first `lake build` is
the toolkit's own three modules, which do compile.) Lake uses a cached file only when its inputs
match, so every cached file it uses is current. Needs `curl`, `tar`, `zstd` (`doctor` reports them).

- **Causalean** — about 500 MB to download, 6 GB unpacked, from its public repository.
- **StatLean** — about 290 MB to download, 3.4 GB unpacked, a release asset of this repository.

When a download fails `init` says so and goes on: Lake then compiles that library from source,
once and long (Causalean: about 2,600 files; StatLean: 1,143 files, about 45 minutes on 32
cores). To fetch afterwards instead, then build:

    (cd ~/my-toolkit && bash .lake/packages/Causalean/scripts/fetch_build_cache.sh && lake build Causalean)
    bash ../third_party/StatLean/port/build_cache.sh fetch && (cd ~/my-toolkit && lake build StatLean)

**5. Smoke-test the wiring** (a dry run, free of model calls).

    npx tsx bin/leansmith.ts verify test/verify/fixtures/paper/main.tex --toolkit ~/my-toolkit --slug smoke --stop-after V1.5 --dry-run

It should end `LeanSmith verify dry-run smoke finished in phase v1_5.`, then a line naming the
run directory it wrote (`~/my-toolkit/runs/smoke`): delete it afterwards.

### Library search

When the pipeline looks for existing results to reuse, it searches Mathlib through Loogle and
LeanSearch, and each domain library and your toolkit through their declaration
indexes, by keywords. A fresh install uses exactly this.

There is also an embedding tier (Python with `numpy` and `sentence-transformers`, which brings `torch`; CPU is enough).
It switches on for a library only when embedding files (`library_embeddings.f32`) sit beside its
index. It is reserved for a library that ships those files, and the libraries on offer ship
their indexes only (Causalean also publishes a fine-tuned encoder, its
`scripts/fetch_retrieval_models.sh`, about 1.2 GB). A fresh install therefore runs on keyword
search alone: skip Python and the models.

## Try the demo

Before your first paper, take the tour: a made-up paper goes through every stage on the real page,
and you make the decisions a run asks of you (a repair that would weaken a main result, the two
promotion rounds). It is a recorded run: no model call, no Lean, no account, and nothing is written
to your toolkit, so it runs as soon as step 1 above is done, while `init` is still building.

    npx tsx bin/leansmith.ts demo

Open the link it prints (`[demo] open: http://127.0.0.1:7342/?token=…`; from another computer,
forward the port first, as for the page below) and follow the box in the corner.

When you finish the guide, stop the demo server with **Ctrl+C in the terminal that started it**.
Closing the browser tab leaves the server running. Agents that start the demo in the background
must stop their demo process by its PID when the tour is finished.
`demo` again goes on where you left it, `demo --restart` begins again.

## First paper

Start your agent (Claude Code or Codex) in the LeanSmith clone and ask it, for example:
"Use LeanSmith to verify arXiv 2401.01234 with my toolkit at ~/my-toolkit." What the agent
then does, and what you can do yourself, from `tools/`:

**1. Get the LaTeX source** (never the PDF). For arXiv, the e-print:

    mkdir -p ~/papers/mypaper && cd ~/papers/mypaper
    curl -L -o src.tar.gz https://arxiv.org/e-print/<id> && tar -xzf src.tar.gz

Your own paper: its `.tex` file or its directory.

**2. Bring up the page** and open the link it prints after a few seconds
(`[ui] open: http://127.0.0.1:7341/?token=…`):

    npx tsx bin/leansmith.ts ui --toolkit ~/my-toolkit

It listens on this computer only. From another computer, forward the port first:
`ssh -L 7341:127.0.0.1:7341 <host>`. Ctrl+C stops the page; runs keep going.

**3. Run the first two stages**, then stop:

    npx tsx bin/leansmith.ts verify ~/papers/mypaper --toolkit ~/my-toolkit --slug mypaper --stop-after V1.5

(`--main <file>` when several files carry `\documentclass`.) The agent launches this detached and
arms the run's watcher, which returns at every halt, finish or crash (also from `tools/`; from the
repository root it is `node tools/scripts/orch.mjs …` — give `--toolkit` as an absolute path, so the
command means the same from either place):

    node scripts/orch.mjs watch mypaper --toolkit ~/my-toolkit

**4. Halts.** The run stops whenever a decision is needed and prints what it waits for and the
flags that answer it; each answer goes with `--resume`. The agent rules on most halts itself (a
reading that leaves the paper's claims intact, a rewind, a cap) and resumes. What changes what the paper claims is
yours: a repair that would **weaken a main result** (accept, decline, or redo with guidance, on the
paper's page — the agent puts its recommendation beside it); any other ruling, at any stage, that
would leave a main result weaker than printed, unless it is a bookkeeping assumption (the agent
asks you first); and the two **promotion rounds** that offer results to your toolkit. A lemma or
definition the agent left weaker is listed on the page for your review. To hand all of these to the agent as
well, start the run with `--full-auto`: each decision then takes the agent's recommendation and is
listed for your review afterwards. Every other halt the agent rules on itself, without asking you
(auto mode, the default); start the run with `--debug` to have it bring a hard call to you instead.
If a cited source cannot be
fetched, the agent asks you for it. You can write to the agent from the page at any time ("Message the
agent"), with files attached.

**5. Continue** stage by stage — `--resume --stop-after F1.5`, then on — to the report
(`runs/<slug>/report.md`) and the annotated paper.

`doc/USER_MANUAL.md` covers every stage, halt, option and file; `leansmith` alone prints all
commands (`propose`, `study`, `toolkit-health`, `report`, …). Here and in the manual,
`leansmith <command>` is short for `npx tsx bin/leansmith.ts <command>`, run from `tools/`
after `source scripts/node_env.sh`.

### Sharing

`leansmith share` (or Share on a finished paper's page) publishes a finished run on the public
site of shared papers, <https://jiyuan-tan.github.io/LeanSmithPapers/>, after you sign in to
GitHub in your browser — identity only, no permission. It is optional; `doc/USER_MANUAL.md`
("Sharing a finished paper") says what is published and how.

## What to expect

- **Time.** The referee stages (V1, V1.5) run without Lean and take an hour or a few on a typical
  paper; most findings come from them, and `--stop-after V1.5` gives a first report. The Lean stages
  (F1–F5) take many hours to days on a full paper. A run stops for rulings along the way: your agent
  makes most of them and asks you for the ones that are yours (with `--full-auto`, only for what it
  cannot get itself, such as a cited source it cannot fetch).
- **A finding is a claim to check.** The agent re-derives each one against your
  paper's text before reporting it; read the witness and decide for yourself.
- **LaTeX it reads:** the common ways of writing a paper. Plain authors' note macros (a colour
  wrapper around an edited passage, a hidden or to-do note) are read away; anything less plain is
  left as written with a warning, and the agent then makes the paper readable in the run's own copy
  of the source. A source your TeX installation fails to compile is still refereed: you get the
  annotated TeX in place of the PDF.
- **Cited results are checked against their sources.** The agent fetches each cited work; one it
  cannot obtain it asks you for. A result used beyond what its source states is reported.
- **Libraries are a help**, not a requirement: a result they lack is proved in the paper's own Lean.

When something goes wrong in the tool itself, the agent records it in the run's
`pipeline_issues.md`. Please open an issue on this repository with that file and the run's slug.

## One Mathlib, compatible libraries

Lean libraries only combine when they build against the same Mathlib, and a toolkit's files are
Lean *modules*, which can only import libraries that are modules too. LeanSmith pins one Lean
toolchain and one Mathlib revision (`tools/data/libraries.json`: Lean v4.33.0, Mathlib `db584cd`),
and every optional library it offers builds against exactly that pin as a module library:

| Library | Source | Notes |
|---|---|---|
| Causalean | [its repository](https://github.com/Jiyuan-Tan/CausalSmith), pinned commit | on the pin upstream; brings FoML and optlib with it |
| FoML | `third_party/lean-rademacher` | adapted copy of [lean-rademacher](https://github.com/auto-res/lean-rademacher) |
| optlib | `third_party/optlib` | adapted copy of [optlib](https://github.com/optsuite/optlib), KKT conditions only |
| StatLean | `third_party/StatLean` | adapted copy of [Stat-Lean](https://github.com/StatLean/Stat-Lean) (upstream is on Lean v4.29.1), converted to a module library; one theorem is renamed so that it imports beside Causalean (`UPSTREAM.md` lists every change). Its compiled files are published as a release asset (Install, step 4) |

An adapted copy keeps its upstream license and says in its `UPSTREAM.md` what changed and how to
re-sync. `doc/PORTING.md` is the procedure that makes one: (1) a workspace on the pin, (2) fixing
the build without changing any statement or adding a `sorry`, (3) converting it to the Lean module
system, (4) vendoring, (5) adding it to the catalog. It is also the procedure for a library that is
not offered: do not point a toolkit at an upstream repository directly.

To add an offered library to an existing toolkit, add its `[[require]]` between the
`# BEGIN/END domain libraries` markers of the toolkit's `lakefile.toml` (always before mathlib) and
its entry to `base` in `leansmith.json`, as `init` writes them for a new toolkit.

## Acknowledgements

LeanSmith builds on, and in three cases ships adapted copies of, other people's Lean
libraries. That code belongs to its authors.

- **[Mathlib](https://github.com/leanprover-community/mathlib4)**, by the Lean prover community
  (Apache-2.0). Required by every toolkit, fetched from its own repository at the pinned revision.
- **Causalean**, from [its own repository](https://github.com/Jiyuan-Tan/CausalSmith) (Apache-2.0).
  Fetched from its repository at the pinned commit.
- **FoML** — `third_party/lean-rademacher`, an adapted copy of
  [lean-rademacher](https://github.com/auto-res/lean-rademacher) (MIT, Copyright (c) 2025 AutoRes),
  the formalization behind "Lean Formalization of Generalization Error Bound by Rademacher
  Complexity and Dudley's Entropy Integral" (arXiv:2503.19605).
- **optlib** — `third_party/optlib`, an adapted copy of the KKT part of
  [optlib](https://github.com/optsuite/optlib) by OptSuite, Peking University (Apache-2.0; the
  authors are named in each file's header), the formalization behind "Formalization of Optimality
  Conditions for Smooth Constrained Optimization Problems" (arXiv:2503.18821).
- **StatLean** — `third_party/StatLean`, an adapted copy of
  [Stat-Lean](https://github.com/StatLean/Stat-Lean) by the StatLean contributors (Apache-2.0,
  Copyright 2024 Junwei Lu; it includes code from the formal-learning-theory kernel, Apache-2.0,
  Copyright (c) 2026 Dhruv Gupta, whose license is kept under `LICENSES/`).

Each adapted copy is changed only so that it builds against the pinned Lean and Mathlib and, where
converted, under the Lean module system; every statement stays as upstream wrote it. Its upstream `LICENSE` (and
`LICENSES/`) is kept unchanged in the copy, the authors' headers stay in the files, and its
`UPSTREAM.md` records the upstream commit and every kind of change made.

## License

LeanSmith's own code and documents are under the MIT License (`LICENSE`). The adapted
libraries under `third_party/` keep their own licenses, each in its directory; Mathlib and
Causalean are fetched from their repositories under theirs (Acknowledgements above).

## Documentation

- `doc/USER_MANUAL.md` — running and reading a verification.
- `doc/PORTING.md` — porting a library that is not offered to the pin and the module system.
- `.claude/skills/leansmith/SKILL.md` — the orchestrator guide (how to run the pipeline and
  what to do at each stop): what your agent reads before it runs a paper.
- `AGENTS.md` — for the coding agent that installs and runs LeanSmith for you.
