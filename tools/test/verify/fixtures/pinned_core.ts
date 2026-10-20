import type { Core } from "../../../src/core/schema.js";

/** The live shape: a hypothesis whose wording is ambiguous, settled by a pin on the result using it. */
export const PINNED_CORE = {
  qid: "q",
  symbols: [],
  assumptions: [
    { id: "ass:cdf-regularity", kind: "regularity", condition: "F_1 and F_0 are continuous, strictly increasing CDFs.", novel: { flag: true, justification: "stated" } },
    { id: "ass:other", kind: "regularity", condition: "E|Y| < ∞.", novel: { flag: true, justification: "stated" } },
    {
      id: "ass:pin-1", kind: "regularity",
      condition: "F_1(y) < F_0(y) at every finite interior point; the quantile relation is for 0<p<1.",
      bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of thm:scale: the proof works on the interior of the supports." },
    },
    {
      id: "ass:pin-2", kind: "regularity",
      condition: "E|Y| < ∞ under the treated law.",
      bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of ass:other: the moment is taken under the treated law." },
    },
    { id: "ass:bk-1", kind: "regularity", condition: "g is Borel measurable.", bookkeeping: { flag: true, added_by: "V1.5", reason: "measurability the proof uses" } },
  ],
  definitions: [],
  statements: [
    { id: "thm:scale", kind: "theorem", statement: "Under strictly increasing CDFs, a transformation g exists.", depends_on: ["ass:cdf-regularity", "ass:pin-1", "ass:bk-1"], status: "to-prove" },
    { id: "lem:plain", kind: "lemma", statement: "A plain lemma.", depends_on: ["ass:other", "ass:pin-2"], status: "to-prove" },
    { id: "lem:unpinned", kind: "lemma", statement: "An unpinned lemma.", depends_on: [], status: "to-prove" },
  ],
  target_estimand: "t",
  bibliography: [],
} as unknown as Core;
