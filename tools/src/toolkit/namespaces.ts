// The toolkit's naming and import conventions.
//
// Namespace: every declaration of a toolkit module lives in the namespace of the module's topic,
// `<lib>.<Division>.<topic path>` (`Toolkit/Foundations/Probability/Independence/X.lean` →
// `Toolkit.Foundations.Probability.Independence`), so nothing the toolkit declares collides with
// Mathlib or a base library, and module, topic and namespace agree.
//
// Imports: a toolkit module imports the modules it uses, never an umbrella (`Mathlib`,
// `Mathlib.Tactic`); the minimal set is the modules of the constants its declarations use.
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { LEAN_DECL_HEADER_RE, LEAN_MODULE_LINE_RE, parseLeanImport } from "../shared/lean_syntax.js";
import { declarationSpans, leanImports } from "./lean_source.js";

/** The topic namespace of a dotted toolkit module (`<lib>.<Division>.<topic…>.<File>`): the module
 *  without its file segment; null for a module that is not under a topic. */
export function topicNamespace(module: string): string | null {
  const parts = module.split(".");
  return parts.length >= 4 ? parts.slice(0, -1).join(".") : null;
}

/** The topic namespace of a module path (`Toolkit/Foundations/…/File.lean`). */
export function topicNamespaceOfPath(rel: string): string | null {
  return topicNamespace(rel.split("\\").join("/").replace(/\.lean$/, "").split("/").join("."));
}

/** `name` in namespace `ns`: unchanged when it already lives there, else `ns.<leaf>`. */
export function inNamespace(name: string, ns: string | null): string {
  if (!ns || name === ns || name.startsWith(`${ns}.`)) return name;
  return `${ns}.${name.slice(name.lastIndexOf(".") + 1)}`;
}

/** Declarations of a module whose name is not in its topic namespace (`[]` when none or no topic). */
export function namesOutsideTopic(module: string, text: string): string[] {
  const ns = topicNamespace(module);
  if (!ns) return [];
  return declarationSpans(text).map((s) => s.name).filter((n) => !n.startsWith(`${ns}.`));
}

export const UMBRELLA_IMPORTS: ReadonlySet<string> = new Set(["Mathlib", "Mathlib.Tactic"]);
/** What replaces `Mathlib.Tactic` when the modules of the used constants miss a tactic. */
export const COMMON_TACTICS = "Mathlib.Tactic.Common";

/** The umbrella imports of `text`. */
export function umbrellaImports(text: string): string[] {
  return leanImports(text).map((i) => i.module).filter((m) => UMBRELLA_IMPORTS.has(m));
}

/** The modules the declarations of `module` use (scan constants of their types and bodies), less
 *  `Init`, the module itself, paper modules and toolkit staging. */
export function usedModules(
  decls: ReadonlyArray<{ module: string; type_constants: ReadonlyArray<{ module: string }>; body_constants: ReadonlyArray<{ module: string }> }>,
  module: string,
  opts: { papersLib: string; lib: string; stagingSegment?: string },
): string[] {
  const out = new Set<string>();
  for (const d of decls) {
    if (d.module !== module) continue;
    for (const c of [...d.type_constants, ...d.body_constants]) {
      const parts = c.module.split(".");
      if (!c.module || c.module === module || parts[0] === "Init" || parts[0] === opts.papersLib) continue;
      if (parts[0] === opts.lib && parts[1] === (opts.stagingSegment ?? "Staging")) continue;
      out.add(c.module);
    }
  }
  return [...out].sort();
}

/** The header variants to try for a module trimmed to what it uses, in order: the used modules;
 *  then, when the module imported `Mathlib.Tactic`, the used modules with the common tactics. */
export function trimmedImportSets(text: string, used: readonly string[]): string[][] {
  const had = new Set(leanImports(text).map((i) => i.module));
  const sets = [[...used].sort()];
  if (had.has("Mathlib.Tactic") && !used.includes(COMMON_TACTICS)) sets.push([...used, COMMON_TACTICS].sort());
  const current = [...had].sort().join(",");
  return sets.filter((s) => s.join(",") !== current);
}

/** `text` with its import block replaced by `public import` lines of `modules` (sorted). */
export function withImportBlock(text: string, modules: readonly string[]): string {
  const lines = text.split("\n");
  const masked = maskLeanCommentsAndStrings(text).split("\n");
  const importIdx = masked.flatMap((l, i) => (parseLeanImport(l) ? [i] : []));
  const block = [...new Set(modules)].sort().map((m) => `public import ${m}`);
  if (importIdx.length === 0) {
    const mod = masked.findIndex((l) => LEAN_MODULE_LINE_RE.test(l));
    const at = mod >= 0 ? mod + 1 : 0;
    return [...lines.slice(0, at), ...(block.length ? ["", ...block] : []), ...lines.slice(at)].join("\n");
  }
  const first = importIdx[0]!;
  const last = importIdx[importIdx.length - 1]!;
  return [...lines.slice(0, first), ...block, ...lines.slice(last + 1)].join("\n");
}

/**
 * Move every declaration of `text` (the module `module`) that is outside its topic namespace into
 * that namespace: the declarations are cut and re-emitted, in source order, in one
 * `namespace <topic> … end` block at the end of the file, each with the context commands it had
 * (`open`/`variable`/…; linter options dropped) and an `open` of the namespace it left when that
 * namespace keeps declarations (`keepsDecls`) — so short names still resolve. Scopes left empty
 * are removed. Returns the new text and the renames (old full name → new full name); references in
 * other files are rewritten by the caller.
 */
export function renamespace(
  text: string,
  module: string,
  keepsDecls: (ns: string) => boolean = () => false,
): { text: string; renames: Map<string, string> } {
  const ns = topicNamespace(module);
  const renames = new Map<string, string>();
  if (!ns) return { text, renames };
  const spans = declarationSpans(text).filter((s) => !s.name.startsWith(`${ns}.`));
  if (spans.length === 0) return { text, renames };
  const ctx: string[] = [];
  const blocks: string[] = [];
  for (const s of spans) {
    const relative = s.written.startsWith("_root_.") ? s.written.slice("_root_.".length) : s.written;
    renames.set(s.name, `${ns}.${relative}`);
    let body = text.slice(s.from, s.to).replace(/\n*$/, "");
    if (s.written !== relative) body = body.replace(s.written, () => relative);
    blocks.push(body);
    for (const c of s.context) if (!/^set_option\s+linter\./.test(c) && !ctx.includes(c)) ctx.push(c);
    const left = s.namespaces.join(".");
    if (left && left !== ns && keepsDecls(left) && !ctx.includes(`open ${left}`)) ctx.push(`open ${left}`);
  }
  let out = text;
  for (const s of [...spans].sort((a, b) => b.from - a.from)) out = out.slice(0, s.from) + out.slice(s.to);
  out = dropEmptyScopes(out).replace(/\n{3,}/g, "\n\n").replace(/\n*$/, "\n");
  out += `\nnamespace ${ns}\n\n${ctx.length ? `${ctx.join("\n")}\n\n` : ""}${blocks.join("\n\n")}\n\nend ${ns}\n`;
  return { text: out, renames };
}

const SCOPE_OPEN_RE = /^[ \t]*(?:namespace[ \t]+\S+|(?:noncomputable[ \t]+)?section\b)/;
const BLANKET_RE = /^[ \t]*(?:@\[expose\][ \t]+)?public[ \t]+section[ \t]*$/;
const SCOPE_END_RE = /^[ \t]*end\b/;

/** Remove `namespace … end` / `section … end` blocks that declare nothing (their context commands
 *  go with them). The file's blanket `public section` is never removed. */
export function dropEmptyScopes(text: string): string {
  let lines = text.split("\n");
  for (let changed = true; changed;) {
    changed = false;
    const masked = maskLeanCommentsAndStrings(lines.join("\n")).split("\n");
    const stack: Array<{ line: number; hasDecl: boolean }> = [];
    for (let i = 0; i < masked.length; i++) {
      const l = masked[i]!;
      if (BLANKET_RE.test(l)) continue;
      if (SCOPE_OPEN_RE.test(l)) {
        stack.push({ line: i, hasDecl: false });
        continue;
      }
      if (SCOPE_END_RE.test(l) && stack.length > 0) {
        const open = stack.pop()!;
        if (!open.hasDecl) {
          lines = [...lines.slice(0, open.line), ...lines.slice(i + 1)];
          changed = true;
          break;
        }
        if (stack.length) stack[stack.length - 1]!.hasDecl = true;
        continue;
      }
      if (LEAN_DECL_HEADER_RE.test(l) || /^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:noncomputable[ \t]+)?instance\b/.test(l)) {
        for (const s of stack) s.hasDecl = true;
      }
    }
  }
  return lines.join("\n");
}
