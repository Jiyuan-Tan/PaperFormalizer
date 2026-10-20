// Toolkit layout lints: pure functions over module text and import lists (no filesystem).
//
// Hard rules (every finding is an error):
//   layering     `<lib>.*` never imports `<papers_lib>.*`; a division imports only itself and
//                earlier divisions (Foundations never imports Tricks); nothing but staging
//                imports `<lib>.Staging.*`; a toolkit module never imports the root barrel;
//                one paper's modules never import another paper's.
//   size         a module has at most `maxLines` (600) lines.
//   header       `module`, then a contiguous sorted block of `public import`s, then the
//                `/-! -/` overview, then exactly one `public section` / `@[expose] public section`,
//                with no other code in between.
//   run-token    module path segments and declaration-name components carry none of the
//                literal tokens `_Verify`, `_Research`, `verify_`, and none equals the staging
//                segment (`Staging`) outside `<lib>/Staging/`. Nothing else: whether a name
//                such as `LeeBounds` is a paper name or a standard result is the curator's and
//                the owner's judgment, not the lint's.
//   topic        with a topic tree (`doc/taxonomy.json`), a toolkit module lives at
//                `<lib>/<Division>/<topic path>/<File>.lean` for a topic path of the tree.
// `bin/lint_toolkit_layout.ts` collects the files; this module only judges them.
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { LEAN_DECL_HEADER_RE, LEAN_MODULE_LINE_RE, parseLeanImport } from "../shared/lean_syntax.js";
import { TOOLKIT_STAGING_SEGMENT } from "./config.js";
import { declaredNames, leanImports } from "./lean_source.js";
import { namesOutsideTopic, topicNamespace, umbrellaImports } from "./namespaces.js";

export const TOOLKIT_MAX_MODULE_LINES = 600;
export const RUN_TOKENS = ["_Verify", "_Research", "verify_"] as const;

export interface LayoutFinding {
  path: string;
  /** 1-based line (1 for whole-file findings). */
  line: number;
  rule: "layering" | "size" | "header" | "run-token" | "topic" | "namespace" | "imports";
  message: string;
  /** Reported, never failing the lint: `garden` turns it into an item (a namespace outside the
   *  topic, an umbrella import). */
  advisory?: boolean;
}

export interface ToolkitModuleSource {
  /** `/`-separated path relative to the toolkit root. */
  path: string;
  module: string;
  text: string;
}

export interface LayoutLintOptions {
  lib: string;
  papersLib: string;
  divisions: readonly string[];
  maxLines?: number;
  stagingSegment?: string;
  /** Topic paths of the toolkit's tree; set, every division module must sit under one. */
  topics?: readonly string[];
}

export type ModuleArea =
  | { area: "lib-root" }
  | { area: "division-barrel"; division: string; rank: number }
  | { area: "division"; division: string; rank: number }
  | { area: "staging" }
  | { area: "lib-other" }
  | { area: "papers-root" }
  | { area: "paper"; paper: string }
  | { area: "external" };

/** Where a module sits in the toolkit layer stack. */
export function classifyModule(module: string, opts: LayoutLintOptions): ModuleArea {
  const parts = module.split(".");
  const staging = opts.stagingSegment ?? TOOLKIT_STAGING_SEGMENT;
  if (parts[0] === opts.lib) {
    if (parts.length === 1) return { area: "lib-root" };
    if (parts[1] === staging) return { area: "staging" };
    const rank = opts.divisions.indexOf(parts[1]);
    if (rank < 0) return { area: "lib-other" };
    return parts.length === 2
      ? { area: "division-barrel", division: parts[1], rank }
      : { area: "division", division: parts[1], rank };
  }
  if (parts[0] === opts.papersLib) {
    return parts.length === 1 ? { area: "papers-root" } : { area: "paper", paper: parts[1] };
  }
  return { area: "external" };
}

/** Layering findings for one module's imports (`imports` = imported module names). */
export function lintImportLayering(
  module: string,
  imports: ReadonlyArray<{ module: string; line: number }>,
  opts: LayoutLintOptions,
  path = module,
): LayoutFinding[] {
  const self = classifyModule(module, opts);
  const out: LayoutFinding[] = [];
  const add = (line: number, message: string) => out.push({ path, line: line + 1, rule: "layering", message });
  const inLib = self.area !== "papers-root" && self.area !== "paper" && self.area !== "external";
  for (const imp of imports) {
    const target = classifyModule(imp.module, opts);
    if (target.area === "staging" && self.area !== "staging") {
      add(imp.line, `imports study staging module ${imp.module}; staging is never imported`);
    }
    if (inLib && (target.area === "papers-root" || target.area === "paper")) {
      add(imp.line, `${opts.lib} module imports paper module ${imp.module}; nothing in ${opts.lib} imports ${opts.papersLib}`);
    }
    if (self.area === "paper" && target.area === "paper" && target.paper !== self.paper) {
      add(imp.line, `paper ${self.paper} imports another paper's module ${imp.module}`);
    }
    if ((self.area === "division" || self.area === "division-barrel") && target.area === "lib-root") {
      add(imp.line, `imports the ${opts.lib} root barrel; import the specific module instead`);
    }
    if (
      (self.area === "division" || self.area === "division-barrel") &&
      (target.area === "division" || target.area === "division-barrel") &&
      target.rank > self.rank
    ) {
      add(imp.line, `${self.division} module imports ${target.division} module ${imp.module}; ${self.division} may import only ${opts.divisions.slice(0, self.rank + 1).join(", ")}`);
    }
  }
  return out;
}

/** Size finding when `text` exceeds `maxLines` lines. Import lines are not counted: the import
 *  block is generated (an umbrella import expanded into the modules used), not content. */
export function lintModuleSize(path: string, text: string, maxLines = TOOLKIT_MAX_MODULE_LINES): LayoutFinding[] {
  const masked = maskLeanCommentsAndStrings(text);
  const all = masked.endsWith("\n") ? masked.slice(0, -1).split("\n") : masked.split("\n");
  const lines = all.filter((l) => !parseLeanImport(l)).length;
  return lines > maxLines
    ? [{ path, line: 1, rule: "size", message: `${lines} lines besides imports; toolkit modules have at most ${maxLines} (split by topic)` }]
    : [];
}

const BLANKET_SECTION_RE = /^[ \t]*(?:@\[expose\][ \t]+)?public[ \t]+section[ \t]*$/;

/** Module-system header contract: `module` → sorted `public import` block → `/-! -/` → section. */
export function lintModuleHeader(path: string, text: string): LayoutFinding[] {
  const out: LayoutFinding[] = [];
  const add = (line: number, message: string) => out.push({ path, line: line + 1, rule: "header", message });
  const lines = text.split("\n");
  const masked = maskLeanCommentsAndStrings(text).split("\n");
  const firstCode = masked.findIndex((l) => l.trim() !== "");
  if (firstCode < 0 || !LEAN_MODULE_LINE_RE.test(masked[firstCode])) {
    add(Math.max(firstCode, 0), "first command must be `module`");
    return out;
  }
  const imports = masked.flatMap((l, i) => (parseLeanImport(l) ? [i] : []));
  for (const i of imports) {
    const imp = parseLeanImport(masked[i])!;
    if (!imp.isPublic || imp.importAll) add(i, `import must be \`public import\`: ${lines[i].trim()}`);
  }
  if (imports.length > 0) {
    const first = imports[0];
    const last = imports[imports.length - 1];
    if (masked.slice(firstCode + 1, first).some((l) => l.trim() !== "")) {
      add(first, "the import block must directly follow `module`");
    }
    for (let i = first; i <= last; i++) {
      if (!parseLeanImport(masked[i])) {
        add(i, "the import block must be contiguous (no blank, comment or code lines inside it)");
        break;
      }
    }
    const names = imports.map((i) => parseLeanImport(masked[i])!.module);
    for (let k = 1; k < names.length; k++) {
      if (names[k - 1] >= names[k]) {
        add(imports[k], `imports are not sorted: ${names[k]} after ${names[k - 1]}`);
        break;
      }
    }
  }
  const afterImports = imports.length > 0 ? imports[imports.length - 1] + 1 : firstCode + 1;
  const docLine = lines.findIndex((l, i) => i >= afterImports && l.includes("/-!"));
  const sections = masked.flatMap((l, i) => (BLANKET_SECTION_RE.test(l) ? [i] : []));
  const firstDecl = masked.findIndex((l) => LEAN_DECL_HEADER_RE.test(l));
  if (docLine < 0 || (firstDecl >= 0 && docLine > firstDecl)) {
    add(afterImports, "missing the `/-! -/` module overview after the imports");
  } else if (masked.slice(afterImports, docLine).some((l) => l.trim() !== "")) {
    add(afterImports, "code between the imports and the `/-! -/` overview");
  }
  if (sections.length !== 1) {
    add(sections[1] ?? afterImports, `expected exactly one blanket \`public section\`, found ${sections.length}`);
  } else if (docLine >= 0) {
    const sec = sections[0];
    if (sec < docLine) add(sec, "the blanket `public section` must follow the `/-! -/` overview");
    else if (masked.slice(docLine, sec).some((l) => l.trim() !== "")) {
      add(sec, "code between the `/-! -/` overview and the blanket `public section`");
    }
  }
  return out;
}

/**
 * Why `identifier` (a module segment or a declaration-name component) is a run token; null when
 * clean. Flags a literal `RUN_TOKENS` entry, or an identifier equal to the staging segment (the
 * callers skip `<lib>/Staging/` itself). Nothing else.
 */
export function runTokenIn(identifier: string, stagingSegment: string = TOOLKIT_STAGING_SEGMENT): string | null {
  for (const t of RUN_TOKENS) if (identifier.includes(t)) return `contains "${t}"`;
  if (identifier === stagingSegment) return `is the reserved staging segment "${stagingSegment}"`;
  return null;
}

/** Run-token findings for a module's path segments and its declaration names. */
export function lintRunTokens(
  path: string,
  module: string,
  declNames: ReadonlyArray<{ name: string; line: number }>,
  stagingSegment: string = TOOLKIT_STAGING_SEGMENT,
): LayoutFinding[] {
  const out: LayoutFinding[] = [];
  for (const seg of module.split(".")) {
    const why = runTokenIn(seg, stagingSegment);
    if (why) out.push({ path, line: 1, rule: "run-token", message: `module segment ${seg} ${why}` });
  }
  const segs = new Set(module.split("."));
  for (const d of declNames) {
    for (const part of d.name.split(".")) {
      if (segs.has(part)) continue; // namespace mirrors the path; already judged above
      const why = runTokenIn(part, stagingSegment);
      if (why) {
        out.push({ path, line: d.line + 1, rule: "run-token", message: `declaration ${d.name} ${why}` });
        break;
      }
    }
  }
  return out;
}

/**
 * Lint a set of modules. Toolkit modules (outside staging) get every rule; paper modules get
 * the layering and header rules; staging modules are skipped (they are temporary and named for
 * their study by design) except that importing them from anywhere else is a layering error.
 */
export function lintToolkitLayout(modules: readonly ToolkitModuleSource[], opts: LayoutLintOptions): LayoutFinding[] {
  const out: LayoutFinding[] = [];
  for (const m of modules) {
    const area = classifyModule(m.module, opts).area;
    if (area === "staging" || area === "external") continue;
    out.push(...lintImportLayering(m.module, leanImports(m.text), opts, m.path));
    out.push(...lintModuleHeader(m.path, m.text));
    if (area === "papers-root" || area === "paper") continue;
    out.push(...lintModuleSize(m.path, m.text, opts.maxLines));
    out.push(...lintRunTokens(m.path, m.module, declaredNames(m.text), opts.stagingSegment));
    if (area === "division" && opts.topics) out.push(...lintTopic(m.path, opts));
    if (area === "division") out.push(...lintConventions(m.path, m.module, m.text));
  }
  return out;
}

/** The toolkit's conventions (`namespaces.ts`), advisory: every declaration in the module's topic
 *  namespace, and no umbrella import. */
export function lintConventions(path: string, module: string, text: string): LayoutFinding[] {
  const out: LayoutFinding[] = [];
  const outside = namesOutsideTopic(module, text);
  if (outside.length) {
    out.push({ path, line: 1, rule: "namespace", advisory: true,
      message: `declared outside the topic namespace ${topicNamespace(module)}: ${outside.join(", ")}` });
  }
  for (const m of umbrellaImports(text)) {
    out.push({ path, line: 1, rule: "imports", advisory: true, message: `imports the umbrella ${m}; import the modules it uses` });
  }
  return out;
}

/** A division module outside the topic tree: `<lib>/<Division>/<topic path>/<File>.lean`. */
export function lintTopic(rel: string, opts: Pick<LayoutLintOptions, "lib" | "divisions" | "topics">): LayoutFinding[] {
  const parts = rel.split("\\").join("/").replace(/\.lean$/, "").split("/");
  const topic = parts[0] === opts.lib && opts.divisions.includes(parts[1] ?? "") && parts.length >= 4 ? parts.slice(2, -1).join("/") : null;
  if (topic !== null && (opts.topics ?? []).includes(topic)) return [];
  return [{
    path: rel, line: 1, rule: "topic",
    message: topic === null
      ? `a toolkit module lives at ${opts.lib}/<Division>/<topic>/<File>.lean`
      : `"${topic}" is not a topic of doc/taxonomy.json; move the module under a listed topic, or add the topic through a new_topic decision`,
  }];
}

export function formatLayoutFinding(f: LayoutFinding): string {
  return `${f.path}:${f.line}: ${f.rule}${f.advisory ? " (advisory)" : ""}: ${f.message}`;
}
