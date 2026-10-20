import { describe, expect, it } from "vitest";
import { assertOwnerTex, ownerReadingsFor } from "../../src/verify/owner_rulings.js";

// An owner reading or condition is printed into the corrected paper as TeX and held by the reviewed
// core as written: Unicode prose is refused when it is recorded (a later rewording would change the
// reviewed core, which V6 refuses).
describe("owner readings are recorded in TeX", () => {
  it("refuses a condition in Unicode, naming the characters", () => {
    expect(() => ownerReadingsFor(null, ["lem:a"], "m(W, γ) = ∂_d γ(W_1) for every γ in Γ", "bookkeeping")).toThrow(/must be written in TeX: a non-ASCII character U\+03B3 \(γ\)/u);
  });
  it("records one written in TeX", () => {
    expect(ownerReadingsFor(null, ["lem:a"], "$m(W,\\gamma)=\\partial_d\\gamma(W_1)$ for every $\\gamma\\in\\Gamma$", "bookkeeping")).toEqual([
      { id: "ass:bk-owner-1", node: "lem:a", reading: "$m(W,\\gamma)=\\partial_d\\gamma(W_1)$ for every $\\gamma\\in\\Gamma$", kind: "bookkeeping" },
    ]);
    expect(() => assertOwnerTex("``quoted'' text, $x\\leq y$")).not.toThrow();
  });
});
