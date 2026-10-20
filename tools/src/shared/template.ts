// Literal text substitution for prompt templates and messages.
//
// `String.prototype.replace`/`replaceAll` with a STRING replacement reads `$$`, `$&`, `` $` `` and
// `$'` in it as patterns, so paper TeX (`$$ a = b $$`, `$\beta$'s`) or model output spliced in that
// way is rewritten. fillTemplate substitutes values literally in one pass.

/** `tpl` with every `{{KEY}}` of `vars` replaced by `vars[KEY]`, verbatim, in one pass: a value that
 *  holds a token (`{{assignment}}` in a paper's text) is not expanded again. Other tokens stay. */
export function fillTemplate(tpl: string, vars: Record<string, string>): string {
  return tpl.replace(/\{\{([A-Za-z_][\w.]*)\}\}/g, (m, k: string) => (Object.hasOwn(vars, k) ? vars[k]! : m));
}
