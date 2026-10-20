// Shared toolkit fixtures for tests (not a test file itself).
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { toolkitConfigFromJson, type ToolkitConfig } from "../../src/toolkit/config.js";

export const TOOLKIT_JSON = {
  version: 1,
  owner: { name: "Test Owner", email: "owner@example.org" },
  toolkit: { lib: "Toolkit", papers_lib: "Papers", divisions: ["Foundations", "Tricks"] },
  base: [
    { name: "Mathlib", kind: "transitive", search: ["loogle", "leansearch"] },
    { name: "Base", kind: "path", path: "../base", index: "../base/doc/library_index.json", alias_file: null },
  ],
  lean: { toolchain: "leanprover/lean4:v4.33.0" },
};

/** A config for `root` without touching the filesystem. */
export function tk(root: string): ToolkitConfig {
  return toolkitConfigFromJson(root, TOOLKIT_JSON);
}

export const BARREL = (name: string, imports: string[] = []): string =>
  ["module", "", ...imports.map((m) => `public import ${m}`), ...(imports.length ? [""] : []),
    `/-!\n# ${name}\n\nBarrel.\n-/`, "", "public section", ""].join("\n");

/** Barrel/config files of a fresh toolkit, keyed by absolute path (`/`-separated). */
export function skeletonFiles(root: string): Record<string, string> {
  const j = (...p: string[]) => path.join(root, ...p).split(path.sep).join("/");
  return {
    [j("leansmith.json")]: JSON.stringify(TOOLKIT_JSON, null, 2),
    [j("lakefile.toml")]: 'name = "t"\n\n[[lean_lib]]\nname = "Toolkit"\n',
    [j("Toolkit.lean")]: BARREL("Toolkit", ["Toolkit.Foundations", "Toolkit.Tricks"]),
    [j("Toolkit", "Foundations.lean")]: BARREL("Toolkit.Foundations"),
    [j("Toolkit", "Tricks.lean")]: BARREL("Toolkit.Tricks"),
    [j("Papers.lean")]: BARREL("Papers"),
    [j("doc", "ledger.json")]: JSON.stringify({ version: 1, declarations: [], decisions: [] }, null, 2),
  };
}

/** Write a fresh toolkit skeleton to disk and return its config. */
export async function writeSkeleton(root: string): Promise<ToolkitConfig> {
  for (const [p, text] of Object.entries(skeletonFiles(root))) {
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, text, "utf8");
  }
  return tk(root);
}

/** A well-formed theorem-only toolkit module. */
export function leanModule(opts: { imports?: string[]; doc?: string; body: string; expose?: boolean }): string {
  const imports = (opts.imports ?? []).map((m) => `public import ${m}`);
  return [
    "module", "", ...imports, ...(imports.length ? [""] : []),
    `/-!\n# ${opts.doc ?? "Module"}\n\nOverview.\n-/`, "",
    opts.expose ? "@[expose] public section" : "public section", "",
    opts.body, "",
  ].join("\n");
}
