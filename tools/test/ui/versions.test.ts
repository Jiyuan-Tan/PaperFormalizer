// A paper's earlier versions (`verify --revise` freezes the one that stood under runs/<slug>/versions/v<n>/):
// addressed `<slug>@v<n>`, shown read only by the run's own views, listed in the page's version picker and
// never as runs, and compared with the run as it stands.
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, renameSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { compareRows, compareView, outcomesOf } from "../../src/ui/compare.js";
import { listRunSlugs, runDir, runExists, validSlug, versionRef } from "../../src/ui/run_model.js";
import { startUiServer, VERSION_READ_ONLY } from "../../src/ui/server.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";
import { VERSION_FROZEN } from "../../src/verify/revision.js";

const PAPER = (thm: string, sym = "A") => String.raw`\documentclass{article}
\newcommand{\mysym}{\mathsf{${sym}}}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\begin{document}
\begin{theorem}\label{thm:a}
${thm}
\end{theorem}
\begin{lemma}\label{lem:b}
For every $n \ge 1$, $n^2 \ge n$ and $\mysym$.
\end{lemma}
\end{document}`;

const write = (file: string, text: string) => { mkdirSync(path.dirname(file), { recursive: true }); writeFileSync(file, text); };
const json = (file: string, value: unknown) => write(file, JSON.stringify(value, null, 2));
const record = (n: number, frozen_at: string, phase: string) => ({ version: n, input: `/src/v${n}`, main_file: "m.tex", source_sha256: `sha${n}`, stage_completed: phase === "done" ? "V6" : "2", phase, core_sha256: null, frozen_at });
const stmt = (id: string, kind: string, label: string, statement: string) => ({ id, kind, statement, depends_on: [], tex_locator: { file: "m.tex", from: 1, label } });

/** Every file under `dir` with its size and mtime: what a request may not change. */
const snapshot = (dir: string): string[] => readdirSync(dir, { recursive: true, withFileTypes: false }).map(String).sort().map((f) => { const st = statSync(path.join(dir, f)); return `${f}:${st.isDirectory() ? "d" : st.size}:${st.mtimeMs}`; });

/**
 * Run `p1`, now version 3 (a report, a revision record); v1 frozen with its report and its bundle's Lean,
 * v2 frozen mid-run (its report.json is v1's, left over: not its own); a fix-in-place snapshot (no version);
 * the toolkit's Lean, newer than v1's.
 */
function fixture() {
  const root = mkdtempSync(path.join(tmpdir(), "tc-ui-versions-"));
  const run = path.join(root, "runs", "p1");
  const v = (n: number) => path.join(run, "versions", `v${n}`);
  const thmOld = "Old wording: if $x \\ge 0$ then $x^2 \\ge 0$.", thmNew = "New wording: if $x$ is real then $x^2 \\ge 0$.";
  // the run as it stands
  write(path.join(run, "source", "m.tex"), PAPER(thmNew, "NEWSYM"));
  json(path.join(run, "state.json"), {
    stage_completed: "V6", lean_subdir: "Papers/P1",
    verify: { phase: "done", source: { main_file: "m.tex", input: "/src/v3", sha256: "sha3" }, version: 3, versions: [record(1, "2026-11-14T19:24:47.072Z", "done"), record(2, "2026-11-15T01:13:42.404Z", "formalization")],
      revision: { from_version: 2, started_at: "x", transcribed: true, reanchor: { same: 5, changed: ["thm:a"], broken: [], renamed: {}, cold: false }, patches: { kept: ["lem:b"], adopted: [], set_aside: [] } } },
  });
  json(path.join(run, "discovery", "core.json"), { statements: [stmt("thm:a", "theorem", "thm:a", thmNew), stmt("lem:b", "lemma", "lem:b", "For every $n \\ge 1$, $n^2 \\ge n$ and $\\mysym$."), stmt("cor:c", "corollary", "cor:c", "$0 \\le 1$.")] });
  json(path.join(run, "report.json"), { verdict: "no_error_found", paper_grade: { grade: "minor", major: [], minor: [{ node: "lem:b", what: "condition added" }] }, summary: { verified: 3 }, results: [{ node_id: "thm:a", bucket: "verified", lean: { file: "T.lean", decl: "Papers.P1.a", line: 1 } }, { node_id: "lem:b", bucket: "verified_with_bookkeeping", lean: null }, { node_id: "cor:c", bucket: "verified", lean: null }] });
  write(path.join(run, "report.md"), "# Report v3\n");
  // version 1: finished, with its bundle's Lean
  write(path.join(v(1), "source", "m.tex"), PAPER(`${thmOld} $\\zzundefold x$.`, "OLDSYM"));
  write(path.join(v(1), "source", "fig.png"), "png");
  json(path.join(v(1), "state.json"), { stage_completed: "V6", lean_subdir: "Papers/P1", verify: { phase: "done", source: { main_file: "m.tex", input: "/src/v1", sha256: "sha1" }, weakening_repair: { status: "pending", items: [{ node: "thm:a", printed: "P", proposed: "Q", given_up: "R", detail: "", witness: null }] } } });
  json(path.join(v(1), "version.json"), record(1, "2026-11-14T19:24:47.072Z", "done"));
  json(path.join(v(1), "discovery", "core.json"), { statements: [stmt("thm:a", "theorem", "thm:a", thmOld), stmt("lem:b", "lemma", "lem:b", "For every  $n \\ge 1$,\n$n^2 \\ge n$ and $\\mysym$."), stmt("lem:gone", "lemma", "lem:gone", "$1 = 1$.")] });
  json(path.join(v(1), "report.json"), { verdict: "errors_found", paper_grade: { grade: "major", major: [{ node: "thm:a" }], minor: [] }, summary: { refuted: 1, verified: 2 }, results: [{ node_id: "thm:a", bucket: "refuted", lean: { file: "T.lean", decl: "Papers.P1.a", line: 1 } }, { node_id: "lem:b", bucket: "verified", lean: null }, { node_id: "lem:gone", bucket: "verified", lean: null }] });
  write(path.join(v(1), "report.md"), "# Report v1\n");
  write(path.join(v(1), "bundle", "lean", "Papers", "P1", "T.lean"), "namespace Papers.P1\n\ntheorem a (x : Nat) : x * x = x * x := rfl\n\nend Papers.P1\n");
  // version 2: frozen mid-run, the report on file v1's
  write(path.join(v(2), "source", "m.tex"), PAPER(thmOld));
  json(path.join(v(2), "state.json"), { stage_completed: "2", lean_subdir: "Papers/P1", verify: { phase: "formalization", version: 2, source: { main_file: "m.tex", input: "/src/v2", sha256: "sha2" } } });
  json(path.join(v(2), "version.json"), record(2, "2026-11-15T01:13:42.404Z", "formalization"));
  json(path.join(v(2), "discovery", "core.json"), { statements: [stmt("thm:a", "theorem", "thm:a", thmOld), stmt("lem:b", "lemma", "lem:b", "For every $n \\ge 1$, $n^2 \\ge n$ and $\\mysym$.")] });
  write(path.join(v(2), "report.json"), readFileSync(path.join(v(1), "report.json"), "utf8"));
  // a fix-in-place snapshot is no version
  json(path.join(run, "versions", ".inplace", "state.json"), { verify: { phase: "v1" } });
  // the toolkit's Lean: the run's as it now stands, newer than version 1's
  write(path.join(root, "Papers", "P1", "T.lean"), "namespace Papers.P1\n\ntheorem a (x : Int) : 0 ≤ x * x := by positivity\n\nend Papers.P1\n");
  const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
  return { root, run, v, cfg };
}

describe("versions: a frozen version is addressed <slug>@v<n>", () => {
  it("resolves to its frozen copy only when that copy holds its version.json and its run is one", () => {
    const { run, v, cfg } = fixture();
    expect(versionRef("p1@v2")).toEqual({ base: "p1", n: 2 });
    for (const bad of ["p1@v0", "p1@v", "p1@2", "../p1@v1", "p1@v1@v2", "@v1", "p1@v.inplace"]) expect(versionRef(bad)).toBe(null);
    expect(validSlug("p1@v1")).toBe(true);
    expect(validSlug("../x@v1")).toBe(false);
    expect(runDir(cfg, "p1@v1")).toBe(v(1));
    expect(runDir(cfg, "p1")).toBe(run);
    expect(runExists(cfg, "p1@v1")).toBe(true);
    expect(runExists(cfg, "p1@v2")).toBe(true);
    // the version the run now is, and one never frozen, are no versions on disk
    expect(runExists(cfg, "p1@v3")).toBe(false);
    expect(runExists(cfg, "p1@v9")).toBe(false);
    // a copy without its version.json is none
    json(path.join(run, "versions", "v5", "state.json"), {});
    expect(runExists(cfg, "p1@v5")).toBe(false);
    expect(runExists(cfg, "nope@v1")).toBe(false);
    expect(listRunSlugs(cfg)).toEqual(["p1"]);
  });

  it("the F5 Lean Proof in English is frozen with a version", () => {
    expect(VERSION_FROZEN).toContain("lean_proof_english.json");
  });
});

describe("versions: an earlier version's page acts on nothing", () => {
  it("its margin cards offer no report of an issue and no edit of a reading; its page's posts are refused before they are sent", () => {
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const line = (start: string) => js.slice(js.indexOf(start), js.indexOf("\n", js.indexOf(start)));
    const cardHTML = (isFrozen: boolean) => new Function("esc", "envOf", `const SNAP = null;\nconst frozen = () => ${isFrozen};\n${line("const KIND_TAG")}\n${line("const CHIP")}\n${js.slice(js.indexOf("function cardHTML("), js.indexOf("/* Edit / Save / Cancel / Remove"))}; return cardHTML;`)(
      (x: string) => String(x).replace(/&/g, "&amp;").replace(/</g, "&lt;"), () => null,
    ) as (c: unknown, r: unknown, o?: unknown) => string;
    const own = [{ id: "ass:pin-owner-1", node: "thm:a", kind: "reading", text: "x", withdraws: 0 }];
    for (const kind of ["note", "reading", "reading-owner", "reading-symbol"]) {
      const c = { id: "c1", key: "k", kind, label: "PaperFormalizer", html: "x" };
      expect(cardHTML(false)(c, null, { own, atRest: true, draft: null })).toContain(`data-flag="open"`);
      const html = cardHTML(true)(c, null, { own, atRest: true, draft: null });
      expect(html).not.toContain("data-flag");
      expect(html).not.toContain("data-reading");
    }
    // the page's one way to post: refused on a version's page
    expect(js.slice(js.indexOf("async function post("), js.indexOf("let toastT"))).toMatch(/if \(frozen\(\)\) throw/);
  });
});

describe("versions: the compare view as the page draws it", () => {
  it("one row per result with the change and each version's outcome, typeset statements, and no outcomes for a version without a report", async () => {
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const line = (start: string) => js.slice(js.indexOf(start), js.indexOf("\n", js.indexOf(start)));
    const esc = (x: unknown) => String(x ?? "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/"/g, "&quot;");
    const app = { innerHTML: "" };
    const draw = async (c: unknown) => {
      const S = { view: "compare", slug: "p1", with: 1 };
      const nav = { hidden: true, textContent: "", href: "" };
      const $ = (sel: string) => (sel === "#nav-paper" ? nav : { addEventListener: () => {} });
      const show = new Function("esc", "S", "api", "app", "$", `${line("const bucketWord")}\n${line("const bucketPill")}\n${line("const dayOf")}\n${line("const versionName")}\n${line("function proseHeading")}\n${js.slice(js.indexOf("const CMP = { only: false };"), js.indexOf("/* The status of an earlier version"))}; return showCompare;`)(esc, S, async () => ({ data: c }), app, $) as (slug: string, n: number) => Promise<void>;
      await show("p1", 1);
      return app.innerHTML;
    };
    const side = (statement: string, bucket: string | null) => ({ statement, outcome: bucket ? { bucket, grade: null } : null });
    const rows = [
      { id: "thm:a", kind: "theorem", label: "thm:a", heading: "Theorem 1", headingBefore: "Theorem 4", change: "changed", proofChanged: false, before: side("OLD", "refuted"), now: side("NEW", "verified") },
      { id: "lem:b", kind: "lemma", label: "lem:b", heading: null, change: "unchanged", proofChanged: true, before: side("SAME", "verified"), now: side("SAME", "verified") },
      { id: "cor:c", kind: "corollary", label: null, heading: null, change: "added", proofChanged: false, before: null, now: side("ADDED", "verified") },
    ];
    const html = await draw({ slug: "p1", title: "A <b>Paper</b>", before: { n: 1, frozenAt: "2026-11-14T19:24:47.072Z", report: true, verdict: "errors_found", grade: "major" }, now: { n: 3, frozenAt: null, report: true, verdict: "no_error_found", grade: "minor" }, earlier: [{ n: 2, frozenAt: "2026-11-15T01:13:42.404Z", report: false }, { n: 1, frozenAt: "2026-11-14T19:24:47.072Z", report: true }], revision: { from: 2, transcribed: true, cold: false, coldReason: null, same: 5, changed: ["thm:a"], relocated: [], kept: ["lem:b"], adopted: [], setAside: [] }, rows, texHtml: { before: { OLD: "<i>old</i>" }, now: { NEW: "<i>new</i>" } } });
    // its own picker of the earlier version to compare
    expect(html).toMatch(/<select id="cmp-with"[^>]*><option value="2">2 — frozen [^<]*<\/option><option value="1" selected>1 — frozen [^<]*2026[^<]*<\/option><\/select>/);
    expect(html).toContain("<th>Version 3 (current)</th>");
    expect(html).toContain("<i>old</i>");
    expect(html).toContain("<i>new</i>");
    expect(html).toContain("statement changed");
    expect(html).toContain("statement unchanged; proof changed");
    expect(html).toContain("new in version 3");
    expect(html).toContain("Not in version 1.");
    expect(html).toContain("Lemma (b)");
    expect(html).toContain("refuted");
    expect(html).toContain("changed by the revision, checked again: Theorem 1");
    expect(html).toContain("1 kept");
    expect(html).toContain("Theorem 4 in version 1");
    // the open revision not yet read: no rows, and why
    const unread = await draw({ slug: "p1", title: null, before: { n: 2, frozenAt: null, report: true, verdict: "no_error_found", grade: null }, now: { n: 3, frozenAt: null, report: false, verdict: null, grade: null }, revision: { from: 2, transcribed: false, cold: false, coldReason: null, same: 0, changed: [], relocated: [], kept: [], adopted: [], setAside: [] }, unread: true, rows: [], texHtml: { before: {}, now: {} } });
    expect(unread).toContain("The revision has not been read yet: the comparison is shown once V1 has read it.");
    expect(unread).not.toContain("cmp-table");
    // a version frozen before its run finished: no outcomes, said so
    const none = await draw({ slug: "p1", title: null, before: { n: 2, frozenAt: null, report: false, verdict: null, grade: null }, now: { n: 3, frozenAt: null, report: true, verdict: "no_error_found", grade: null }, revision: null, rows: rows.map((r) => ({ ...r, before: r.before && { ...r.before, outcome: null } })), texHtml: {} });
    expect(none).toContain("No report yet (frozen before the run finished).");
    expect(none).toContain("no report yet (frozen before the run finished)");
    expect(none).not.toContain("How the run read");
  });
});

describe("versions: the picker in the paper page's header", () => {
  it("names each version — the current one, each frozen one with its date and whether it has a report — and links the comparisons from the current page", () => {
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const line = (start: string) => js.slice(js.indexOf(start), js.indexOf("\n", js.indexOf(start)));
    const esc = (x: unknown) => String(x ?? "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/"/g, "&quot;");
    const draw = (viewing: number) => {
      const host = { innerHTML: "", dataset: {} as Record<string, string> };
      const $ = (sel: string) => (sel === "#versions" ? host : { addEventListener: () => {} });
      const P = { detail: { versions: { base: "p1", current: 3, viewing, list: [{ n: 3, current: true, frozenAt: null, report: true }, { n: 2, current: false, frozenAt: "2026-11-15T01:13:42.404Z", report: false }, { n: 1, current: false, frozenAt: "2026-11-14T19:24:47.072Z", report: true }] } } };
      new Function("esc", "$", "P", "SNAP", `${line("const dayOf")}\n${line("const versionName")}\n${js.slice(js.indexOf("function drawVersions()"), js.indexOf("/* An earlier version of a paper beside"))}; return drawVersions;`)(esc, $, P, null)();
      return host.innerHTML;
    };
    const cur = draw(3);
    expect(cur).toContain(`<label>Version <select id="version-pick"`);
    expect(cur).toContain(`<option value="p1" selected>3 (current)</option>`);
    expect(cur).toMatch(/<option value="p1@v2">2 — frozen [^<]*2026[^<]*, no report<\/option>/);
    expect(cur).toMatch(/<option value="p1@v1">1 — frozen [^<]*2026<\/option>/);
    // one link, to the version before the current one
    expect(cur).toContain(`<a href="#/compare/p1/2">Compare with an earlier version</a>`);
    expect(cur).not.toContain(`#/compare/p1/1`);
    const old = draw(1);
    expect(old).toContain(`<option value="p1@v1" selected>`);
    expect(old).not.toContain("#/compare/");
  });
});

describe("versions: the compare rows", () => {
  it("match results by node: unchanged (spacing aside), changed, added, removed, each with its outcome", () => {
    const s = (id: string, statement: string, proof_tex = "By induction.") => ({ id, kind: "lemma", statement, proof_tex, tex_locator: { label: id } });
    const out = outcomesOf({ paper_grade: { major: [{ node: "a" }], minor: [{ node: "b" }] }, results: [{ node_id: "a", bucket: "refuted" }, { node_id: "b", bucket: "verified" }] });
    const rows = compareRows([s("a", "A."), s("b", "B  holds."), s("gone", "G.")], [s("b", "B holds.", "By  a new\nargument."), s("a", "A'."), s("new", "N.")], out, null);
    expect(rows.map((r) => [r.id, r.change, r.proofChanged])).toEqual([["b", "unchanged", true], ["a", "changed", false], ["new", "added", false], ["gone", "removed", false]]);
    expect(rows[1]!.before).toEqual({ statement: "A.", outcome: { bucket: "refuted", grade: "major" } });
    expect(rows[1]!.now).toEqual({ statement: "A'.", outcome: null });
    expect(rows[0]!.before!.outcome).toEqual({ bucket: "verified", grade: "minor" });
    expect(rows[3]!.now).toBe(null);
  });
});

describe("server: an earlier version is shown read only, from its frozen copy", () => {
  it("lists no version as a run, offers the versions on the page, renders a version's page and paper, refuses every change, and writes nothing into versions/", async () => {
    const { run, v, cfg } = fixture();
    const before = snapshot(path.join(run, "versions"));
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = (p: string) => fetch(`${base}${p}`, { headers: { Cookie } });
      const getJson = async <T>(p: string): Promise<T> => { const r = await get(p); expect(r.status, p).toBe(200); return (await r.json()) as T; };
      // the toolkit lists the paper once
      const tk = await getJson<{ runs: Array<{ slug: string }> }>("/api/toolkit");
      expect(tk.runs.map((r) => r.slug)).toEqual(["p1"]);
      // the current page carries the picker: newest first, the current version, then the frozen ones and whether each has a report
      type Page = { summary: { slug: string; live: boolean; status: string; headline: string; orch: unknown; verdict: string | null; pending: { weakening: number } }; versions: unknown; repairs: unknown[]; results: Array<{ id: string; bucket: string | null }>; texHtml: Record<string, string> };
      const now = await getJson<Page>("/api/runs/p1");
      expect(now.versions).toEqual({ base: "p1", current: 3, viewing: 3, list: [
        { n: 3, current: true, frozenAt: null, report: true },
        { n: 2, current: false, frozenAt: "2026-11-15T01:13:42.404Z", report: false },
        { n: 1, current: false, frozenAt: "2026-11-14T19:24:47.072Z", report: true },
      ] });
      // version 1's page: its own results and report, not running, nothing waiting on anyone (its frozen receipt included)
      const v1 = await getJson<Page>(`/api/runs/${encodeURIComponent("p1@v1")}`);
      expect(v1.summary).toMatchObject({ slug: "p1@v1", live: false, status: "done", orch: null, verdict: "errors_found", pending: { weakening: 0 } });
      expect(v1.repairs).toEqual([]);
      expect((v1.versions as { viewing: number }).viewing).toBe(1);
      expect(v1.results.map((r) => [r.id, r.bucket])).toEqual([["thm:a", "refuted"], ["lem:b", "verified"], ["lem:gone", "verified"]]);
      // version 2 was frozen before its run finished: the report on file is not its own
      const v2 = await getJson<Page>("/api/runs/p1@v2");
      expect(v2.summary).toMatchObject({ status: "idle", verdict: null, headline: "no report yet (frozen before the run finished)" });
      expect(v2.results.every((r) => r.bucket === null)).toBe(true);
      // its paper, from the frozen source
      const paper = await getJson<{ html: string; from: string }>("/api/runs/p1@v1/paper");
      expect(paper.from).toBe("source");
      expect(paper.html).toContain("Old wording");
      expect(paper.html).not.toContain("New wording");
      expect((await getJson<{ md: string; path: string }>("/api/runs/p1@v1/report")).md).toBe("# Report v1\n");
      expect((await get("/api/runs/p1@v2/report")).status).toBe(404);
      // the Lean of a version is its bundle's copy, never the toolkit's newer one; with no copy, none
      type Drawers = { results: Record<string, { rows: Array<{ lean: string }> | null; leanMissing?: true }> };
      const d1 = await getJson<Drawers>("/api/runs/p1@v1/drawers");
      const lean1 = JSON.stringify(d1.results["thm:a"]!.rows);
      expect(lean1).toContain("Nat");
      expect(lean1).not.toContain("Int");
      const dNow = await getJson<Drawers>("/api/runs/p1/drawers");
      expect(JSON.stringify(dNow.results["thm:a"]!.rows)).toContain("Int");
      // no such version: refused as no run
      for (const s of ["p1@v3", "p1@v9", "p1@v0", "p1@v.inplace"]) expect((await get(`/api/runs/${encodeURIComponent(s)}`)).status, s).toBe(404);
      // every change asked of a version is refused, whatever it is, before it is read
      const posts = ["action", "preview", "message", "message-clear", "message-seen", "review", "objection", "upload", "dismiss", "promotion", "share", "nope"];
      for (const sub of posts) {
        const r = await fetch(`${base}/api/runs/p1@v1/${sub}?draft=abcdefgh1&name=x.txt`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify({ action: { kind: "resume" }, text: "hi", id: "d1", verdict: "approve", comment: "c", round: "A", understood: true }) });
        expect([sub, r.status]).toEqual([sub, 409]);
        expect(((await r.json()) as { error: string }).error).toBe(VERSION_READ_ONLY);
      }
      expect((await get("/api/runs/p1@v1/share")).status).toBe(409);
      expect((await get("/api/runs/p1@v1/share-status")).status).toBe(409);
      expect((await get("/api/runs/p1@v1/compare?with=2")).status).toBe(409);
      // (the run itself still takes them: a message, say)
      expect((await fetch(`${base}/api/runs/p1/message`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify({ text: "hi" }) })).status).toBe(200);
      // nothing was written into a frozen version
      expect(snapshot(path.join(run, "versions"))).toEqual(before);
      // a version whose bundle holds no Lean shows none (not the toolkit's, of another version)
      renameSync(path.join(v(1), "bundle", "lean"), path.join(v(1), "bundle", "lean.aside"));
      const d1bare = await getJson<Drawers>("/api/runs/p1@v1/drawers");
      expect(d1bare.results["thm:a"]!.rows).toBe(null);
    } finally { await ui.close(); }
  }, 60_000);

  it("compares an earlier version with the current one: each result's statement in both, typeset, and its outcome in each — or that a version has no report", async () => {
    const { cfg } = fixture();
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = (p: string) => fetch(`${base}${p}`, { headers: { Cookie } });
      type Cmp = { slug: string; before: { n: number; report: boolean; verdict: string | null; grade: string | null }; now: { n: number; report: boolean }; revision: Record<string, unknown> | null; unread: boolean; earlier: unknown[]; rows: Array<{ id: string; heading: string | null; change: string; before: { statement: string; outcome: { bucket: string; grade: string | null } | null } | null; now: { statement: string; outcome: { bucket: string } | null } | null }>; texHtml: { before: Record<string, string>; now: Record<string, string> } };
      const c1 = (await (await get("/api/runs/p1/compare?with=1")).json()) as Cmp;
      expect(c1.before).toMatchObject({ n: 1, report: true, verdict: "errors_found", grade: "major" });
      expect(c1.now).toMatchObject({ n: 3, report: true });
      expect(c1.rows.map((r) => [r.id, r.change])).toEqual([["thm:a", "changed"], ["lem:b", "unchanged"], ["cor:c", "added"], ["lem:gone", "removed"]]);
      const a = c1.rows[0]!;
      expect(a.heading).toBe("Theorem 1");
      expect(a.before!.outcome).toEqual({ bucket: "refuted", grade: "major" });
      expect(a.now!.outcome).toMatchObject({ bucket: "verified" });
      // both statements typeset by the page's renderer
      expect(c1.texHtml.before[a.before!.statement]).toContain("katex");
      expect(c1.texHtml.now[a.now!.statement]).toContain("katex");
      // a statement worded alike in both, under a macro the revision redefined: each under its own version's macros
      const b = c1.rows[1]!;
      expect(b.before!.statement.replace(/\s+/g, " ")).toBe(b.now!.statement.replace(/\s+/g, " "));
      expect(c1.texHtml.before[b.before!.statement]).toContain("OLDSYM");
      expect(c1.texHtml.now[b.now!.statement]).toContain("NEWSYM");
      expect(c1.texHtml.now[b.now!.statement]).not.toContain("OLDSYM");
      expect(c1.unread).toBe(false);
      expect(c1.earlier).toEqual([{ n: 2, frozenAt: "2026-11-15T01:13:42.404Z", report: false }, { n: 1, frozenAt: "2026-11-14T19:24:47.072Z", report: true }]);
      expect(c1.revision).toMatchObject({ from: 2, transcribed: true, cold: false, same: 5, changed: ["thm:a"], kept: ["lem:b"] });
      // version 2 has no report of its own: no outcomes on its side
      const c2 = (await (await get("/api/runs/p1/compare?with=2")).json()) as Cmp;
      expect(c2.before).toMatchObject({ n: 2, report: false, verdict: null });
      expect(c2.rows.every((r) => r.before === null || r.before.outcome === null)).toBe(true);
      for (const w of ["3", "9", "0", "x", ""]) expect((await get(`/api/runs/p1/compare?with=${w}`)).status, w).toBe(404);
    } finally { await ui.close(); }
  }, 60_000);
});

describe("versions: what the compare reads, and what viewing a version leaves alone", () => {
  it("an open revision V1 has not read yet gives no rows, and says so; a result only the transcription holds is matched, not removed", async () => {
    const { run, cfg } = fixture();
    // a result awaiting a ruling, out of the corrected core of the current version but in its transcription
    json(path.join(run, "discovery", "core.transcribed.json"), { statements: [stmt("lem:gone", "lemma", "lem:gone", "$1 = 1$.")] });
    const c = (await compareView(cfg, "p1", 1))!;
    expect(c.rows.find((r) => r.id === "lem:gone")?.change).toBe("unchanged");
    expect(c.unread).toBe(false);
    // the authors' revision recorded, V1 not through it: the core on file is still the version before's
    const state = JSON.parse(readFileSync(path.join(run, "state.json"), "utf8"));
    state.verify.revision.transcribed = false;
    json(path.join(run, "state.json"), state);
    const open = (await compareView(cfg, "p1", 1))!;
    expect(open.unread).toBe(true);
    expect(open.rows).toEqual([]);
    expect(open.revision).toMatchObject({ transcribed: false });
    // a fix in place open over it is no revision: the comparison stands, with the revision before it
    const earlier = { ...state.verify.revision, transcribed: true };
    state.verify.revision = { from_version: 3, started_at: "y", in_place: { sha: "s", previous: earlier } };
    json(path.join(run, "state.json"), state);
    const fixing = (await compareView(cfg, "p1", 1))!;
    expect(fixing.unread).toBe(false);
    expect(fixing.rows.length).toBeGreaterThan(0);
    expect(fixing.revision).toMatchObject({ from: 2, transcribed: true });
  });

  it("the version's figures are served from its frozen copy (none for a version not on disk); opening it, its drawers and the compare put nothing of it on the current run's records", async () => {
    const { run, v, cfg } = fixture();
    const records = [path.join(run, "logs", "ui_math_failures.json"), path.join(run, "logs", "ui_render_problems.json")];
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = (p: string) => fetch(`${base}${p}`, { headers: { Cookie } });
      const fig = await get("/api/runs/p1@v1/asset/fig.png");
      expect(fig.status).toBe(200);
      expect(await fig.text()).toBe("png");
      expect((await get("/api/runs/p1@v9/asset/fig.png")).status).toBe(404);
      expect((await get("/api/runs/p1@v1/asset/..%2Fstate.json.png")).status).toBe(404);
      // version 1's paper holds a formula no renderer reads: its own, never put on the run's record
      const paper = (await (await get("/api/runs/p1@v1/paper")).json()) as { health: { mathFailures: Array<{ tex: string }> } };
      expect(paper.health.mathFailures.map((f) => f.tex).join(" ")).toContain("zzundefold");
      for (const sub of ["", "/drawers", "/report"]) await (await get(`/api/runs/p1@v1${sub}`)).text();
      for (const f of records) expect(existsSync(f), f).toBe(false);
      // the compare renders the current paper (its records are its own) and version 1's: nothing of version 1 on them
      await (await get("/api/runs/p1/compare?with=1")).text();
      for (const f of records) if (existsSync(f)) expect(readFileSync(f, "utf8")).not.toContain("zzundefold");
      expect(existsSync(path.join(v(1), "logs"))).toBe(false);
      // a version whose bundle kept no Lean says so (its drawers show none of the toolkit's)
      expect(((await (await get("/api/runs/p1@v2")).json()) as { leanNotKept?: true }).leanNotKept).toBe(true);
      expect(((await (await get("/api/runs/p1@v1")).json()) as { leanNotKept?: true }).leanNotKept).toBeUndefined();
      expect(((await (await get("/api/runs/p1")).json()) as { leanNotKept?: true }).leanNotKept).toBeUndefined();
    } finally { await ui.close(); }
  }, 60_000);
});
