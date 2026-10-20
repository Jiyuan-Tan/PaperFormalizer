// Prompt substitution is literal: paper TeX and model output carry `$$`, `$'`, `$&`, `` $` ``, which a
// string replacement would read as patterns (`$$ a = b $$` sent as `$ a = b $`, `$'` splicing in the
// rest of the template).
import { describe, expect, it } from "vitest";
import { fillTemplate } from "../../src/shared/template.js";

const HAZARDS = "We have $$ a = b $$; under $\\beta$'s law; cost 5\\$& more; a $`x$ tick.";

describe("fillTemplate", () => {
  it("substitutes text holding $$, $', $&, $` verbatim", () => {
    const tpl = "head\n{{items}}\nmiddle\n{{assignment}}\ntail";
    const out = fillTemplate(tpl, { items: HAZARDS, assignment: `{"a": "$'$&$$"}` });
    expect(out).toBe(`head\n${HAZARDS}\nmiddle\n{"a": "$'$&$$"}\ntail`);
  });
  it("never expands a token inside a substituted value, and leaves unknown tokens", () => {
    expect(fillTemplate("{{items}} / {{assignment}} / {{other}}", { items: "paper says {{assignment}}", assignment: "A" })).toBe("paper says {{assignment}} / A / {{other}}");
  });
});
