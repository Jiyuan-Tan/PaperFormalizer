Proof automation of the Causalean layer (full reference: `doc/TACTICS.md` at the Causalean
package root):

- Side-condition goals (Measurable/Integrable/AEMeasurable/StronglyMeasurable/Continuous, incl.
  `Measurable[m]`) on Causalean constructions: try bare `fun_prop` FIRST; cite names only after it
  fails (MemLp/IntegrableOn not covered; analytic Integrable content rightly stays name-called).
- `integral_linearity` replaces `rw [integral_add/sub/...]` + hand-named integrability witnesses;
  `condexp_linearity` (witness brackets `[w₁, w₂]`) proves `=ᵐ[μ]` condExp-linearity goals.
- Simp sets: `causal_defs_simps` replaces `unfold`; `condexp_simps` unwraps wrappers;
  `sum_algebra_simps` distributes ∑; `indicator_simps` for indicators.
- Tag side-condition lemmas you author `@[fun_prop]` at birth, subject to every never-tag rule in
  TACTICS.md.
- Statement shape follows the paper, never the automation.
