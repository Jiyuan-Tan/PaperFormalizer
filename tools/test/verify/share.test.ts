// `theoremchecker share`: a finished run's bundle sent to the share service — here an in-memory
// stand-in for the registry's Worker; nothing leaves this machine.
import { existsSync } from "node:fs";
import { DIRECTORY_LINK, FILE_SYMLINKS } from "../platform.js";
import { appendFile, readFile, rename, rm, symlink, writeFile } from "node:fs/promises";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { sha256 } from "../../src/verify/f4_seal.js";
import { bundleArchive, paperUrl, pollShare, readShare, runShareCli, shareOutcome, sharePaper, sharePlan, shareRecordView, shareSummary, ustarName, type ShareDeps, type ShareRecord } from "../../src/verify/share.js";
import { fakeService, finishedRun, readArchive, SERVICE, SLUG, tmpDirs } from "./share_fake.js";

afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});
const NOW = () => new Date("2026-10-09T12:00:00Z");
const BUNDLE = ["MATCH.md", "REPORT.md", "bundle.json", "corrected_paper/TODO.md", "corrected_paper/main.pdf", "corrected_paper/main.tex", "f4_reviews.log", "f4_seal.json", "lean/Papers/APaper/Main.lean", "lean/lakefile.toml", "page/page.json"];

describe("share: what is sent, and how", () => {
  it("sends the manifest, then the whole bundle as one archive of the bytes read, every file 0644 and sorted; records the share, waiting for the sign-in", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch, now: NOW };
    const { root, run, bundle } = await finishedRun();
    const plan = await sharePlan({ toolkitRoot: root, slug: SLUG, deps });
    expect(plan).toMatchObject({ title: "A Paper on Bounds", authors: "A. Author and B. Author", arxiv: "2105.15197", service: SERVICE });
    expect(plan.parts).toEqual(["MATCH.md", "REPORT.md", "bundle.json", "corrected_paper/ (3 files)", "f4_reviews.log", "f4_seal.json", "lean/ (2 files)", "page/ (1 file)"]);
    const record = await sharePaper(plan, deps);
    expect(svc.calls).toEqual(["POST /api/uploads", `PUT /api/uploads/${record.id}`]);
    expect(record).toMatchObject({ slug: SLUG, service: SERVICE, claim_url: `${SERVICE}/claim/${record.id}`, check_code: "K7PQ", status: "awaiting_sign_in", started_at: "2026-10-09T12:00:00.000Z", expires_at: "2026-10-09T13:00:00.000Z" });
    expect(JSON.parse(await readFile(path.join(run, "share.json"), "utf8"))).toEqual(record);
    expect(shareRecordView(record)).not.toHaveProperty("poll_token");

    const up = svc.uploads.get(record.id)!;
    expect(up.manifest).toMatchObject({ v: 1, slug: SLUG, title: "A Paper on Bounds", authors: "A. Author and B. Author", arxiv: "2105.15197" });
    expect(up.manifest.files.map((f) => f.path)).toEqual(BUNDLE);
    // byte for byte the bundle's files, in order, each a regular file of mode 0644 (main.tex is 0755 on disk)
    const entries = readArchive(up.archive!);
    expect(entries.map((e) => e.path)).toEqual(BUNDLE);
    for (const e of entries) {
      expect(e).toMatchObject({ mode: "0000644", type: "0" });
      expect(e.bytes.equals(await readFile(path.join(bundle, e.path)))).toBe(true);
      expect(up.manifest.files.find((f) => f.path === e.path)).toEqual({ path: e.path, size: e.bytes.length, sha256: sha256(e.bytes) });
    }
    // the same files make the same archive
    expect(sha256(bundleArchive(new Map(entries.map((e) => [e.path, e.bytes])))) ).toBe(up.manifest.archive.sha256);
  });

  it("a path over 100 bytes is split at a / into ustar's prefix and name; one that cannot be is none of the archive's", () => {
    const long = `lean/${"Deep/".repeat(20)}Statement.lean`;
    const entries = readArchive(bundleArchive(new Map([["b.md", Buffer.from("b")], [long, Buffer.from("theorem")], ["a.md", Buffer.alloc(700, 1)]])));
    expect(entries.map((e) => e.path)).toEqual(["a.md", "b.md", long]);
    const deep = entries[2]!;
    expect(deep.prefix.length).toBeLessThanOrEqual(155);
    expect(deep.name.length).toBeLessThanOrEqual(100);
    expect(deep.prefix).not.toBe("");
    expect(deep.bytes.toString()).toBe("theorem");
    expect(entries[0]!.bytes.equals(Buffer.alloc(700, 1))).toBe(true);
    expect(ustarName("a/".repeat(128))).toBeNull();
    expect(ustarName(`lean/${"x".repeat(101)}`)).toBeNull();
  });

  it("a last part over 100 bytes goes in a pax header's path record, right before its file; a path over 255 bytes is none of the archive's", () => {
    const fig = "corrected_paper/synthetic_experiment_pareto_20250516_50_2.5_2_5_30_1.0_adaptive__1000,_2000,_3000,_4000,_5000__othres.png";
    const entries = readArchive(bundleArchive(new Map([["a.md", Buffer.from("a")], [fig, Buffer.from("png")], ["z.md", Buffer.from("z")]])));
    expect(entries.map((e) => [e.path, e.type, e.bytes.toString()])).toEqual([["a.md", "0", "a"], [fig, "0", "png"], ["z.md", "0", "z"]]);
    expect(() => bundleArchive(new Map([[`lean/${"x/".repeat(130)}A.lean`, Buffer.from("x")]]))).toThrow(/too long for the archive/);
  });

  it("refuses, in one line, a run that is not finished, a bundle of an older layout, a broken seal and a blocking item — nothing is sent", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch };
    const { root, run, bundle } = await finishedRun();
    const refusal = async (p: Promise<unknown> = sharePlan({ toolkitRoot: root, slug: SLUG, deps })): Promise<string> => p.then(() => "(no refusal)", (e: Error) => e.message);
    const put = (file: string, change: (v: Record<string, unknown>) => unknown) => readFile(file, "utf8").then((t) => writeFile(file, JSON.stringify(change(JSON.parse(t) as Record<string, unknown>))));

    expect(await refusal(sharePlan({ toolkitRoot: root, slug: "no_run", deps }))).toMatch(/no such run/);
    expect(await refusal(sharePlan({ toolkitRoot: root, slug: "Bad Slug", deps }))).toMatch(/lower-case letters, digits, _ and -/);
    await put(path.join(run, "state.json"), (s) => ({ ...s, stage_completed: "5" }));
    expect(await refusal()).toBe("cannot share a_paper: the run is not finished (its last completed stage is 5, not V6)");
    await put(path.join(run, "state.json"), (s) => ({ ...s, stage_completed: "V6" }));

    await put(path.join(bundle, "bundle.json"), (b) => ({ ...b, todo_items: [{ group: "compile", text: "pdflatex failed:\n  Undefined control sequence" }, { group: "numbering", text: "a new number" }] }));
    expect(await refusal()).toBe("cannot share a_paper: 1 blocking item(s) in corrected_paper/TODO.md — pdflatex failed: Undefined control sequence");
    await put(path.join(bundle, "bundle.json"), (b) => ({ ...b, todo_items: [] }));

    await appendFile(path.join(bundle, "lean", "lakefile.toml"), "# changed\n");
    expect(await refusal()).toBe("cannot share a_paper: f4_seal.json: changed after the seal was written: lean/lakefile.toml");
    await writeFile(path.join(bundle, "lean", "lakefile.toml"), 'name = "p"\n');
    expect(await refusal()).toBe("(no refusal)");

    await rm(path.join(bundle, "f4_seal.json"));
    expect(await refusal()).toBe("cannot share a_paper: f4_seal.json: missing");
    await rm(path.join(bundle, "page"), { recursive: true });
    expect(await refusal()).toMatch(/no page\/page\.json \(an older layout.*`theoremchecker report a_paper`$/);
    expect(svc.calls).toEqual([]);
  });

  it("refuses, one line per problem and before anything is shown, what the registry's check would: a file outside the layout, a dotfile, a type a browser runs, an SVG, a path too long for the archive, a file the seal does not name, a share.json, a link, a file too large", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch };
    const { root, bundle } = await finishedRun();
    const refusal = async (): Promise<string> => sharePlan({ toolkitRoot: root, slug: SLUG, deps }).then(() => "(no refusal)", (e: Error) => e.message);
    const only = async (rel: string, text = "x"): Promise<string> => {
      await writeFile(path.join(bundle, rel), text);
      const r = await refusal();
      await rm(path.join(bundle, rel));
      return r;
    };
    expect(await only(".env", "TOKEN=1")).toBe('cannot share a_paper: ".env": a dotfile is not part of a bundle');
    expect(await only("x.html")).toMatch(/^cannot share a_paper: the registry would refuse the bundle:\n {2}- "x\.html": outside the layout of a paper folder\n {2}- "x\.html": a \.html file is not part of a bundle$/);
    expect(await only("NOTES.md")).toBe('cannot share a_paper: "NOTES.md": outside the layout of a paper folder');
    expect(await only("lean/Extra.lean")).toBe('cannot share a_paper: "lean/Extra.lean": not named by the seal');
    expect(await only("corrected_paper/fig.XML")).toMatch(/a \.xml file is not part of a bundle/);
    expect(await only("corrected_paper/fig.svg")).toMatch(/"corrected_paper\/fig\.svg": an \.svg file is not part of a bundle — the site cannot keep one from running a script; give the figure as PDF or PNG/);
    expect(await only(`corrected_paper/${"f".repeat(240)}.png`)).toMatch(/the path is too long for the archive \(at most 255 bytes\)/);
    // the share writes share.json: one in the bundle would stand in for it
    expect(await only("share.json", JSON.stringify({ shared_by: "someone-else", shared_at: "2020-01-01", arxiv: null }))).toBe("cannot share a_paper: share.json: a bundle holds none — the share writes it");
    expect(await only("README.md", Buffer.alloc(24 * 1024 * 1024 + 1).toString())).toBe('cannot share a_paper: "README.md": 25165825 bytes, over the limit of 25165824 for one file');
    // no link is read through: a file that is one, and the bundle folder itself
    await rm(path.join(bundle, "REPORT.md"));
    if (FILE_SYMLINKS) {
      await symlink(path.join(root, "theoremchecker.json"), path.join(bundle, "REPORT.md"));
      expect(await refusal()).toMatch(/^cannot share a_paper: the registry would refuse the bundle:\n {2}- "REPORT\.md": a symbolic link \(a bundle holds regular files only\)\n {2}- REPORT\.md: missing$/);
      await rm(path.join(bundle, "REPORT.md"));
    }
    await writeFile(path.join(bundle, "REPORT.md"), "# Report\n");
    expect(await refusal()).toBe("(no refusal)");
    await rename(bundle, `${bundle}-real`);
    await symlink(`${bundle}-real`, bundle, DIRECTORY_LINK);
    expect(await refusal()).toBe("cannot share a_paper: runs/a_paper/bundle is a symbolic link — a bundle is the folder the run wrote");
    expect(svc.calls).toEqual([]);
  });

  it("what is sent is what was shown: a file changed, added or replaced by a link after the plan is a refusal, and nothing is sent", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch };
    const { root, run, bundle } = await finishedRun();
    const secret = path.join(root, "secret.txt");
    await writeFile(secret, "# Report\n");
    const plan = await sharePlan({ toolkitRoot: root, slug: SLUG, deps });
    const send = (): Promise<string> => sharePaper(plan, deps).then(() => "(sent)", (e: Error) => e.message);
    const report = path.join(bundle, "REPORT.md");
    // a link to a file elsewhere, even one of the same bytes
    await rm(report);
    if (FILE_SYMLINKS) {
      await symlink(secret, report);
      expect(await send()).toBe('not shared: the bundle of a_paper changed after it was shown ("REPORT.md": a symbolic link (a bundle holds regular files only), and 1 more) — share again to see what would be sent');
      await rm(report);
    }
    await writeFile(report, "# Another\n");
    expect(await send()).toBe("not shared: the bundle of a_paper changed after it was shown (its files are not the ones that were shown) — share again to see what would be sent");
    await writeFile(report, "# Report\n");
    await writeFile(path.join(bundle, "README.md"), "added\n");
    expect(await send()).toMatch(/its files are not the ones that were shown/);
    await rm(path.join(bundle, "README.md"));
    await rename(bundle, `${bundle}-real`);
    await symlink(`${bundle}-real`, bundle, DIRECTORY_LINK);
    expect(await send()).toMatch(/changed after it was shown \(bundle\/ is not a folder, and \d+ more\)/);
    expect(svc.calls).toEqual([]);
    expect(existsSync(path.join(run, "share.json"))).toBe(false);
    await rm(bundle);
    await rename(`${bundle}-real`, bundle);
    expect(await send()).toBe("(sent)");
  });

  it("the service's refusal, its silence and an address of elsewhere are refusals: nothing is recorded, and no archive goes to another address", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch };
    const { root, run } = await finishedRun();
    const send = async (): Promise<string> => sharePaper(await sharePlan({ toolkitRoot: root, slug: SLUG, deps }), deps).then(() => "(sent)", (e: Error) => e.message);
    svc.answer.refuse = "too many uploads from this address; try again in a minute";
    expect(await send()).toBe("not shared: the share service answered 400: too many uploads from this address; try again in a minute");
    svc.answer.refuse = undefined;
    svc.answer.down = true;
    expect(await send()).toBe(`not shared: the share service at ${SERVICE} could not be reached (fetch failed)`);
    svc.answer.down = false;
    svc.answer.claimUrl = "https://elsewhere.test/claim/x";
    svc.calls.length = 0;
    expect(await send()).toBe(`not shared: the share service gave a sign-in address that is not on ${SERVICE}: "https://elsewhere.test/claim/x"`);
    expect(svc.calls).toEqual(["POST /api/uploads"]);
    expect(existsSync(path.join(run, "share.json"))).toBe(false);
  });

  it("the share's status is asked of the service until it is final, and written to share.json when it moved", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch, now: NOW };
    const { root, run } = await finishedRun();
    let r: ShareRecord = await sharePaper(await sharePlan({ toolkitRoot: root, slug: SLUG, deps }), deps);
    expect(await pollShare(run, r, deps)).toBe(r);
    svc.confirm(r.id, "alice");
    r = await pollShare(run, r, deps);
    expect(r).toMatchObject({ status: "submitted", login: "alice" });
    expect(await readShare(run)).toEqual(r);
    svc.finish(r.id, { kind: "review", pr_url: "https://github.com/Jiyuan-Tan/TheoremCheckerPapers/pull/3" });
    r = await pollShare(run, r, deps);
    expect(shareOutcome(r)).toBe("sent for review: the registry's owner reviews the paper before it is published — https://github.com/Jiyuan-Tan/TheoremCheckerPapers/pull/3");
    svc.calls.length = 0;
    expect(await pollShare(run, r, deps)).toBe(r);
    expect(svc.calls).toEqual([]);
    expect(shareOutcome({ ...r, status: "published", url: "https://site/papers/a_paper/" })).toBe("published: https://site/papers/a_paper/");
    expect(shareOutcome({ ...r, status: "refused", problems: ["the slug a_paper is taken by @bob"] })).toBe("not published: the registry refused the paper\n  - the slug a_paper is taken by @bob");
  });

  it("keeps only the registry's own links and the service's text without control characters; a share the service no longer knows is over", async () => {
    const svc = fakeService();
    const deps: ShareDeps = { service: SERVICE, fetch: svc.fetch, now: NOW };
    const { root, run } = await finishedRun();
    const sent = await sharePaper(await sharePlan({ toolkitRoot: root, slug: SLUG, deps }), deps);
    svc.confirm(sent.id, "alice");
    svc.finish(sent.id, { kind: "published", url: "https://evil.example/papers/a_paper/" });
    let r = await pollShare(run, sent, deps);
    expect(r.status).toBe("published");
    expect(r.url).toBeUndefined();
    expect(shareOutcome(r)).toBe(`published: ${paperUrl(SLUG)}`);
    const other = await sharePaper(await sharePlan({ toolkitRoot: root, slug: SLUG, deps }), deps);
    svc.confirm(other.id, "alice");
    svc.finish(other.id, { kind: "refused", pr_url: "https://github.com/someone/else/pull/1", problems: ["bad\u001b[2Jname\u0007"] });
    r = await pollShare(run, other, deps);
    expect(r.pr_url).toBeUndefined();
    expect(r.problems).toEqual(["bad [2Jname "]);
    const gone = await sharePaper(await sharePlan({ toolkitRoot: root, slug: SLUG, deps }), deps);
    svc.uploads.delete(gone.id);
    r = await pollShare(run, gone, deps);
    expect(r).toMatchObject({ status: "expired", note: "the share service no longer knows this share" });
    expect(shareOutcome(r)).toBe("not shared: the share service no longer knows this share — share again");
    expect(await readShare(run)).toEqual(r);
  });

  it("the command prints what will be published, then asks: it sends only when the slug is typed at a terminal, then prints the sign-in page and its code and waits for the outcome", async () => {
    const svc = fakeService();
    const { root, run } = await finishedRun();
    const lines: string[] = [];
    const asked: string[] = [];
    const opened: string[] = [];
    // the person signs in and confirms while the command waits; the registry then publishes
    let polls = 0;
    const sleep = async () => {
      polls += 1;
      const [id] = [...svc.uploads.keys()];
      if (polls === 1) svc.confirm(id!, "alice");
      if (polls === 2) svc.finish(id!, { kind: "published", url: paperUrl(SLUG) });
    };
    const cli = (flags: string[], answer = "", tty = true) => runShareCli([SLUG, "--toolkit", root, ...flags], { service: SERVICE, fetch: svc.fetch, now: NOW, sleep, open: (u) => opened.push(u), tty, log: (m) => lines.push(m), ask: async (q) => { asked.push(q); return answer; } });
    await cli(["--dry-run"]);
    expect(lines.join("\n").replace(/\d+ kB/, "N kB")).toBe([
      "Share a_paper: this will be PUBLISHED",
      "",
      "  paper      A Paper on Bounds",
      "  slug       a_paper",
      "  files      11 files, N kB",
      "  parts      MATCH.md, REPORT.md, bundle.json, corrected_paper/ (3 files), f4_reviews.log, f4_seal.json, lean/ (2 files), page/ (1 file)",
      "  public at  https://jiyuan-tan.github.io/TheoremCheckerPapers/papers/a_paper/",
      "",
      "You confirm in your browser: sign in to GitHub — the share service learns your name and account, nothing else, and asks for no permission — and press \"Share publicly\". The paper is attributed to that account. Unless you are one of the registry's trusted sharers, its owner reviews the paper before it is published.",
      "",
      "WARNING: Sharing publishes the corrected paper's TeX source and PDF, the findings and the referee's notes, the Lean code and the report on a public site, under your GitHub account. It cannot be fully undone once others have fetched it.",
      "",
      "dry run: nothing was sent.",
    ].join("\n"));
    expect(asked).toEqual([]);
    await expect(cli([], "yes")).rejects.toThrow(/not shared: the answer was not the slug/);
    await expect(cli([], "")).rejects.toThrow(/not shared/);
    expect(asked[0]).toBe("\nType the slug (a_paper) to share it: ");
    // no terminal (an agent, a pipe): the summary, then a refusal — the question is not even put
    lines.length = 0;
    await expect(cli([], SLUG, false)).rejects.toThrow("not shared: sharing asks for confirmation at a terminal or on the paper's page.");
    expect(lines[0]).toMatch(/^Share a_paper: this will be PUBLISHED/);
    expect(asked).toHaveLength(2);
    await expect(cli(["--yes"], SLUG)).rejects.toThrow(/unknown flag --yes/);
    await expect(cli(["--registry", "x"], SLUG)).rejects.toThrow(/unknown flag --registry/);
    expect(svc.calls).toEqual([]);
    expect(existsSync(path.join(run, "share.json"))).toBe(false);

    lines.length = 0;
    await cli([], SLUG);
    const [id] = [...svc.uploads.keys()];
    const out = lines.join("\n");
    expect(out).toContain(`Sent. To finish, open this page, sign in to GitHub and press "Share publicly":\n  ${SERVICE}/claim/${id}\nCheck code: K7PQ (the page you open shows the same code; continue only if it does).`);
    expect(out).toContain("confirmed by @alice: the registry is checking the paper …");
    expect(lines.at(-1)).toBe("published: https://jiyuan-tan.github.io/TheoremCheckerPapers/papers/a_paper/");
    expect(opened).toEqual([`${SERVICE}/claim/${id}`]);
    expect(await readShare(run)).toMatchObject({ status: "published", login: "alice", url: paperUrl(SLUG) });
    await expect(runShareCli([SLUG, "--force"])).rejects.toThrow(/unknown flag --force/);
    await expect(runShareCli([])).rejects.toThrow(/Usage: theoremchecker share/);
  });

  it("a refused share ends the command with the registry's problems", async () => {
    const svc = fakeService();
    const { root } = await finishedRun();
    const sleep = async () => { const [id] = [...svc.uploads.keys()]; svc.finish(id!, { kind: "refused", problems: ["the slug a_paper is taken by @bob"] }); };
    await expect(runShareCli([SLUG, "--toolkit", root], { service: SERVICE, fetch: svc.fetch, sleep, open: () => {}, tty: true, log: () => {}, ask: async () => SLUG })).rejects.toThrow("not published: the registry refused the paper\n  - the slug a_paper is taken by @bob");
  });

  it("the summary counts megabytes", () => {
    expect(shareSummary({ slug: "s", title: "T", authors: "", runDir: "", bundleDir: "", service: SERVICE, arxiv: null, files: [{ rel: "a", bytes: 3 * 1024 * 1024, sha256: "" }], bytes: 3 * 1024 * 1024, parts: ["a"] })).toContain("1 files, 3.0 MB");
  });
});
