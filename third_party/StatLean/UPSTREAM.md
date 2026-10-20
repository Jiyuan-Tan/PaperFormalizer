# StatLean — vendored, adapted copy

- **Origin:** https://github.com/StatLean/Stat-Lean
- **Upstream commit:** `86b3823f77fc2b0f5a9923f85b588a4f8a65f94c`
  (upstream pins Lean `v4.29.1` and Mathlib `v4.29.1` = `5e932f97dd25535344f80f9dd8da3aab83df0fe6`)
- **License:** Apache License 2.0. Upstream's `LICENSE` and `LICENSES/` are copied
  unchanged beside this file. Every file here is a modified version of the upstream file
  with the same name. The modifications are the Lean/Mathlib and module-system adaptations listed below.

## Why vendored

Upstream is pinned to Lean v4.29.1 and Mathlib 5e932f97. This copy is adapted to build against:

- **Lean:** `leanprover/lean4:v4.33.0` (`lean-toolchain`)
- **Mathlib:** `db584cd6d46c92f209a44c0f1c829460d327499d` (`lakefile.toml`)

All 1,142 submodules and `StatLean.lean` build with no errors (`lake build`), including
when imported from a Lean module alongside the pinned Causalean modules (see below).

## Initial Lean/Mathlib adaptation

- Before the module-system port, only `StatLean/**/*.lean` was touched;
  `StatLean.lean` was byte-identical to upstream.
- The build files are new:
  - `lakefile.toml` replaces upstream's `lakefile.lean`. It has the same `leanOptions`,
    no doc-gen4 and no `deps` exe.
  - `lean-toolchain` is new.
- At that stage, 427 of the 1,142 submodule files differed from upstream
  (about 1.7k lines changed). The module-system port below changes every file header.
- No theorem, lemma or definition changed its mathematical meaning. The only edits inside
  statements are renames to the new Mathlib spelling with the same meaning:
  - `NoAtoms μ` → `NullSingletonClass μ`. Mathlib renamed the class; the field is still
    `measure_singleton : ∀ x, μ {x} = 0`.
  - `⟨x, h⟩ : ℝ≥0` → `NNReal.mk x h` (a definitionally equal term) in the gaussianReal
    variances in `HypothesisTesting/Randomization/{SignChange,TwoSamplePermutation}.lean`.
    In the new elaborator the anonymous constructor gets the subtype type
    `{r // 0 ≤ r}` and breaks instance search.
  - `s.toSet` → `(s : Set α)` in `DKWUniform.dkwPass_disjoint`, because `Finset.toSet`
    was removed (it was an abbrev for the coercion).
  - `instance isProbabilityMeasure_vecRootLaw` → `theorem` (same type) in
    `BivariateEdgeworth.lean`. Lean now rejects instances that have an explicit,
    non-inferable hypothesis; every use already passed the argument explicitly.
  - `deriving Fintype` on the enum `ComplianceType` (`CausalInference/IV/Defs.lean`) →
    `instance : Fintype ComplianceType := derive_fintype% _`. Mathlib's enum handler for
    `deriving Fintype` fails at this revision.
  - The body of the private def `halfGeometricP` (`ScoreOperatorDenseRange.lean`) is
    respelled for the new `geometricMeasure (p : unitInterval)` signature. It is the same
    measure.
  - Two private helper instances were added:
    - `ChangingClassMarginal.lean`: `IsProbabilityMeasure (multivariateGaussian μ S)` for a
      raw lambda covariance.
    - `NondominatedOperationalEfficiencyAnalytic.lean`:
      `IsProbabilityMeasure (gaussianReal μ ⟨x, h⟩)`.
- No `sorry`, `admit`, `axiom` or new `set_option` was introduced.
  - The `set_option` lines are identical to upstream: the same 194 lines, including
    upstream's own `maxHeartbeats` raises.
  - `grep -rnE "\bsorry\b|\badmit\b|^\s*axiom\b" StatLean` gives 182 hits, the same as
    upstream. All of them, upstream's and ours, are in comments or docstrings; neither has a
    `sorry`, `admit` or `axiom` in code.

## Initial adaptation categories (approximate site counts)

Mechanical, applied by script:

| Category | Sites |
|---|---|
| `simpa … using h` → `simpa … using! h`. Lean core: `simpa` now closes at reducible transparency; `using!` is the old default-transparency behaviour. | ~556 |
| `zero_le _` → `zero_le` / `zero_le (a := x)`. The argument is now implicit. | ~450 |
| `mul_le_mul_left'` → `mul_le_mul_right` and `mul_le_mul_right'` → `mul_le_mul_left`. The names were swapped; the primed ones were removed. | 73 |
| `ENNReal.mul_le_mul_left/right` → `ENNReal.mul_le_mul_iff_right/left` | 10 |
| `NoAtoms` → `NullSingletonClass`, `noAtoms_gaussianReal` → `nullSingletonClass_gaussianReal` | 76 |
| No-op `dsimp only` / `simp only … at h` removed. The goal is now already beta-reduced. | ~45 |

Hand fixes:

| Category | Sites |
|---|---|
| `.fun_*` lemma variants. `Measurable/AEMeasurable/Integrable/Continuous….mul/add/sub/smul/div/inv/pow/const_smul` now state the Pi-operation form `(f * g)`; the old lambda form is `.fun_mul` etc. This mostly affects `rw [lintegral_const_mul … (hf.mul hg)]`, `lintegral_add_left`, `integral_map`, and similar. | ~132 |
| `convert` → `convert!`. `convert` no longer closes defeq/instance side goals. | ~95 |
| Anonymous-constructor `ℝ≥0` literals typed as the subtype. Fixed with `NNReal.mk`, `change`/`rfl` steps, `NNReal.eq`, or `exact` instead of `rw`. | ~60 |
| `rw [iff_lemma]` → `refine (iff_lemma).mpr ?_` / `.mp h`. Rewrites fail on goals that are not type-correct at implicit transparency. | ~15 |
| Beta-reduction changes. Added `beta_reduce`, or rewrote with the beta-reduced form. | ~10 |
| Removed or renamed Mathlib lemmas and changed signatures. | ~40 |
| Simp-set adjustments: lemmas that lost `@[simp]`, defs unfolded inside `if`/`filter` decidability instances, eta-expanded equation lemmas (`simp [f]` no longer unfolds a partial application `f n` → `unfold f`), `↓reduceIte`, and EuclideanSpace inner-product simp loops. | ~30 |
| Miscellaneous. Each item applies to a few sites. | — |

Removed or renamed Mathlib lemmas and changed signatures (from the hand-fix table above):
- `Nat.succ_mul_choose_eq` → `Nat.add_one_mul_choose_eq`
- `Finset.filter_card_add_filter_neg_card_eq_card` → `Finset.card_filter_add_card_filter_not`
- `measureReal_univ_eq_one` → `probReal_univ`
- `EuclideanSpace.measurableEquiv` → `(MeasurableEquiv.toLp 2 _).symm`
- `PosDef.posDef_sqrt` → `isStrictlyPositive.sqrt`
- `Integrable.bdd_mul'` → `bdd_mul`
- `InnerProductSpace.toDual_apply` → `toDual_apply_apply`
- `innerSL_apply` → `innerSL_apply_apply`
- `tendsto_inverse_atTop_nhds_zero_nat` → `tendsto_inv_atTop_nhds_zero_nat`
- `LowerSemicontinuous.comp_continuous` → `.comp`
- `Set.Ici_diff_left` → `Set.Ici_sdiff_left`
- `left_mem_Ici` / `right_mem_Iic` → `self_mem_*`
- `eLpNorm_condExp_le` → `eLpNorm_condExp_le_eLpNorm`
- `AEStronglyMeasurable.norm_condExp_le` → `norm_condExp_le`
- `Real.exists_extension_norm_eq` → `exists_extension_norm_eq`
- `IsSetRing.diff_mem` → `sdiff_mem`
- `SimpleGraph.symm` is now a `Std.Symm` instance
- Signature changes:
  - `integrableOn_rpow_mul_exp_neg_mul_rpow`: `0 < p`
  - `tendsto_integral_of_L1(')`: takes `AEStronglyMeasurable`
  - `MemLp.condExp`: takes `1 ≤ p`
  - `leftLim_eq_of_tendsto`: takes a `NeBot` instance
  - `inner_gradient_left`: no longer takes a differentiability hypothesis
  - Taylor–Lagrange lemmas: stated on `uIcc`/`uIoo`
  - `geometricMeasure`: takes `p : unitInterval`
  - `TransGen.mono`: changed shape

Miscellaneous (from the hand-fix table above):
- `rw [Finset.range_eq_Ico]` now rewrites only one occurrence.
- Trailing `rfl` or bullet after `rw`/`gcongr` gives "no goals".
- Two `whnf` timeouts were fixed by a more direct lemma: `.of_uncurry_right` and
  `Filter.Tendsto.inner`. No heartbeat increase was needed.

## Module-system port (2026-10-09)

The second adaptation converts the entire library, including `StatLean.lean`, to Lean's
module system. A comment-aware mechanical script adds `module` as the first line,
changes each actual import to `public import`, and inserts `@[expose] public section`
after the last import and before the original content. This changes 1,143 files (1,142 submodules plus the root)
and 5,202 original imports;
31 hand-added imports give 5,233 actual public imports. Five import examples in
existing docstrings are preserved as examples. `requiresModuleSystem = true` in
`lakefile.toml` enforces the module boundary.

Private declarations can remain private in proof bodies, but references in exposed
values and public statement types must be public. The necessary helpers and instances
listed below retain their original types and values. Direct Mathlib imports replace
access formerly obtained through private transitive imports. In
`AsymptoticStatistics/LowerBounds/BayesRiskLowerBound.lean`, the nonemptiness proof inside the public statement
supplies `(f := π)` to `Finset.nonempty_of_sum_ne_zero`; the finite supremum is unchanged
by proof irrelevance. No proof-body edits were needed apart from the three uses of the
renamed analytic-set theorem.

The source contains no syntax, macro, tactic, elaborator, attribute-registration,
`initialize`, or opaque declaration requiring a manual `meta`/`public meta import`
exception. The existing 102 `open … in` constructs, 11 local instances, and four local
notations remain intact; no manual universe-binder changes or checking-disabling
options are needed.

### Declaration names and compatibility

Before the renames below, exactly one fully-qualified name overlapped with Causalean
at commit `e298f64908520f29348e3f480b72db63d37dd574`:

- `MeasureTheory.AnalyticSet.nullMeasurableSet` →
  `MeasureTheory.AnalyticSet.statLean_nullMeasurableSet`, in
  `AsymptoticStatistics/ForMathlib/AnalyticSetCapacitability.lean`.
  StatLean retains its original SFinite-measure theorem; Causalean retains its
  finite-measure theorem under the original name. Three proof uses and six
  documentation/comment mentions in that file and `MeasurableSelection.lean` are updated.
- The formerly private `StatLean.TimeSeries.factpi` in
  `TimeSeries/ForMathlib/Fourier/HerglotzBochner.lean` is exported as
  `StatLean.TimeSeries.herglotzFactTwoPi`. The type and proof are unchanged. The distinct
  private instance in `TimeSeries/Stationarity/Gaussian.lean` retains its name;
  exporting the first instance under the old name would prevent that file from compiling.
- The formerly private `AsymptoticStatistics.EmpiricalProcess.linfEvalCLM` in
  `AsymptoticStatistics/EmpiricalProcess/ChangingClassCore.lean` is exported as
  `AsymptoticStatistics.EmpiricalProcess.changingClassLinfEvalCLM`, updating its single
  use in the same file. Another public `linfEvalCLM` already exists in
  `AbstractDonsker/JointInfluenceCoordinates.lean`; the distinct name keeps both
  definitions and their generated proof names available in the umbrella import.

The collision audit scans all 2,608 Causalean source modules plus its import-only root,
including modules absent from that root. A namespace/command audit identifies every file
capable of declaring names outside `Causalean`; those files, all five tactic modules,
and `Causalean.Stat.Sample` are compiled (19 Causalean modules). Their 262 compiled
constants, including generated declarations, are compared with every compiled StatLean
constant. Other Causalean declarations lie under `Causalean`, where StatLean declares
nothing; private names also carry disjoint module prefixes. Causalean's bundled FoML
and Optlib authored names are checked as well. This audit finds only the analytic-set
clash above; the final renamed library has no shared declaration names in the audit.

### Hand fixes

Paths below are relative to this package. Counts refer to this module-system port,
separately from the earlier Lean/Mathlib adaptation.

| Hand fix | Sites | Files |
|---|---:|---:|
| Direct Mathlib imports | 31 | 25 |
| Private helpers made public | 31 | 15 |
| Private instances made public | 4 | 4 |
| Explicit nonemptiness-proof argument | 1 | 1 |
| Exported helper/instance renamed to avoid internal collisions (also counted above) | 2 | 2 |
| Causalean collision renamed | 1 | 2 |

Private helpers made public (types and values unchanged):

- `StatLean/AsymptoticStatistics/Asymptotics/Discharge/LeastFavorableVec.lean`: `nonDiagonalCrossInformation2577`.
- `StatLean/AsymptoticStatistics/EmpiricalProcess/ChangingClassCore.lean`: `changingClassLinfEvalCLM`.
- `StatLean/AsymptoticStatistics/EmpiricalProcess/VCSharpPacking.lean`: `edgeMinWeightSumRaw`, `extendSubtypeWeight`.
- `StatLean/AsymptoticStatistics/ForMathlib/CondExpL2.lean`: `lpTrimComapToLpMap_e1`, `lpCongrMeasure`, `lpTrimComapToMapTrim_hfmp`, `lpTrimComapToMapTrim_pull`, `lpTrimComapToMapTrim_surj`, `lpTrimComapToMapTrim_aux`, `lpTrimComapToLpMap_e2`.
- `StatLean/AsymptoticStatistics/LowerBounds/UnboundedSubmodelQMDPath.lean`: `unboundedOneDimCurve_at_zero`, `unboundedOneDimCurve_isProbability`, `unboundedOneDimCurve_absContinuous`, `oneDimQmd_limit_aux`, `oneDimQmdResidual`.
- `StatLean/AsymptoticStatistics/MEstimator/NuisanceRate.lean`: `nuisanceEmpiricalCriterion`, `nuisanceCenteredProcess`.
- `StatLean/AsymptoticStatistics/ParametricFamily/UnboundedSubmodel.lean`: `hellinger_residual`.
- `StatLean/Bayesian/DirichletLaplace/PosteriorContraction.lean`: `dbarVal`.
- `StatLean/HypothesisTesting/ForMathlib/EsseenSmoothing.lean`: `tentC`, `sqSincC`.
- `StatLean/MultipleTesting/Knockoff/Supermartingale.lean`: `measurable_cproc`.
- `StatLean/StatisticalModels/FactorModels/Defs.lean`: `measurable_loadingAct`.
- `StatLean/StatisticalModels/Gaussian/BlockIndex.lean`: `blockFstₗ`, `blockSndₗ`.
- `StatLean/StatisticalModels/Gaussian/Conditioning.lean`: `measurable_toEuclideanLin`.
- `StatLean/TimeSeries/ARMA/Consistency.lean`: `piMat`, `piK`.
- `StatLean/TimeSeries/ARMA/ScoreAnalysis.lean`: `findB`, `findA`.
- `StatLean/AsymptoticStatistics/EmpiricalProcess/ChangingClassMarginal.lean`: `isProbabilityMeasure_multivariateGaussian_fun`.
- `StatLean/AsymptoticStatistics/LowerBounds/NondominatedOperationalEfficiencyAnalytic.lean`: `isProbabilityMeasure_gaussianReal_anonMk`.
- `StatLean/ComputationalStatistics/Resampling/CategoricalCounts.lean`: `isFiniteMeasure_categorical`.
- `StatLean/TimeSeries/ForMathlib/Fourier/HerglotzBochner.lean`: `herglotzFactTwoPi`.

Additional public imports:

- `StatLean/AsymptoticStatistics/Experiment/FiniteRiskCompactification.lean`: `Mathlib.Probability.Kernel.Composition.RadonNikodym`.
- `StatLean/AsymptoticStatistics/Experiment/GaussianShiftConvolution.lean`: `Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion`.
- `StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean`: `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`.
- `StatLean/AsymptoticStatistics/ForMathlib/GaussianMGF.lean`: `Mathlib.Probability.Distributions.Gaussian.Fernique`, `Mathlib.Probability.Distributions.Gaussian.CharFun`.
- `StatLean/AsymptoticStatistics/ForMathlib/MultivariateGaussianWeakLimit.lean`: `Mathlib.Probability.Distributions.Gaussian.CharFun`, `Mathlib.Probability.Distributions.Gaussian.Fernique`.
- `StatLean/AsymptoticStatistics/ForMathlib/Probability/IsonormalProcess.lean`: `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic`.
- `StatLean/AsymptoticStatistics/LowerBounds/ParametricBridge.lean`: `Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion`.
- `StatLean/AsymptoticStatistics/Operators/CoarsenedQMDLimit.lean`: `Mathlib.MeasureTheory.Integral.DominatedConvergence`.
- `StatLean/ComputationalStatistics/Partitioning/Holdout.lean`: `Mathlib.MeasureTheory.Integral.Prod`.
- `StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean`: `Mathlib.Analysis.Calculus.ContDiff.Bounds`, `Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion`.
- `StatLean/HypothesisTesting/ForMathlib/DKWUniform.lean`: `Mathlib.Probability.Independence.Integration`.
- `StatLean/HypothesisTesting/ForMathlib/GaussianShell.lean`: `Mathlib.Probability.Distributions.Gaussian.Fernique`.
- `StatLean/HypothesisTesting/ForMathlib/LindebergCLT.lean`: `Mathlib.Probability.Independence.CharacteristicFunction`.
- `StatLean/Minimaxity/Examples/LipschitzDensity.lean`: `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`.
- `StatLean/Minimaxity/Examples/UniformLocation.lean`: `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`.
- `StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean`: `Mathlib.Probability.Distributions.Gaussian.CharFun`, `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute`.
- `StatLean/MultipleTesting/EmpiricalBayes/BayesRisk.lean`: `Mathlib.Probability.Independence.Integration`.
- `StatLean/NonparametricStatistics/KernelDensity/MISEBias.lean`: `Mathlib.MeasureTheory.Integral.Prod`.
- `StatLean/PointEstimation/Equivariance/LocationExamples.lean`: `Mathlib.Probability.Independence.Integration`.
- `StatLean/RobustStatistics/HeavyTails/Catoni.lean`: `Mathlib.Probability.Independence.Integration`, `Mathlib.MeasureTheory.Integral.Pi`.
- `StatLean/StatisticalModels/FactorModels/LocalIndep.lean`: `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic`.
- `StatLean/TimeSeries/GARCH/StochasticVolatility.lean`: `Mathlib.Probability.Independence.Integration`.
- `StatLean/TimeSeries/Process/LinearProcess.lean`: `Mathlib.MeasureTheory.Integral.DominatedConvergence`.
- `StatLean/TimeSeries/Process/SampleACF.lean`: `Mathlib.Probability.Independence.Integration`.
- `StatLean/TimeSeries/Stationarity/Gaussian.lean`: `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic`, `Mathlib.Probability.Distributions.Gaussian.Fernique`.

### Validation

- Before conversion: `lake exe cache get` downloaded/decompressed 8,690 cache units
  (218.20 seconds), then `lake build` compiled all 1,143 source modules
  successfully (9,849 total jobs, errors 0, 2534.90 seconds).
  No baseline fixes were required.
- After conversion and the listed fixes: `lake build` covers all 1,143 source modules
  (errors 0, 90.84 seconds for the final incremental pass).
  Earlier failed passes are retained as build1-attempt logs in the port's scratch directory.
- The exact source grep count for `sorry`/`admit`/`axiom` remains **182 → 182**;
  comment/string-aware counts remain **0 → 0 in code**. All 194 original `set_option`
  lines are unchanged. Of the original 6,443 private declarations, 35 required
  public visibility; all others retain their original privacy.
- Compiled declaration/type comparison: 28,386 StatLean
  constants before, 28,435 after. After normalizing module
  privacy and the documented names, 28,366 constants pair with unchanged declaration kinds;
  the 20 unmatched old and 69 unmatched new names are compiler-generated proof/match helpers.
  No authored declaration disappeared. Raw type hashes are not stable for types referring
  to regenerated proof helpers or changed proof-instance terms; they are not used as a
  semantic-equivalence claim. No project axioms or compiled expressions containing `sorry`
  remain. Source-body comparison accounts for every nonblank-line change in all 1,143 files.
- A separate scratch Lake project requires this StatLean copy by path, Mathlib at
  `db584cd6d46c92f209a44c0f1c829460d327499d`, and Causalean by git at
  `e298f64908520f29348e3f480b72db63d37dd574`; no local checkout is used as a dependency.
  `Probe.lean` starts with `module` and publicly imports `StatLean`,
  `Causalean.Mathlib.MeasureTheory.Function.Analytic.UniversalMeasurability.UniversalMeasurability`,
  and `Causalean.Stat.Sample`. It proves an analytic-set null-measurability lemma using
  the renamed StatLean theorem and a measurability lemma using `IIDSample.measurable_Z`,
  checks Causalean's original analytic-set name, and prints both lemmas' axioms.
  `lake build` succeeds (errors 0, 34.82 seconds). The probe builds
  the requested narrow import closure; the entire Causalean umbrella is not built.

Conversion script, individual fix records, complete declaration audits, probe source,
and timed build logs are preserved under the session's scratch `statlean/` directory;
the final report is `REPORT.md` there. StatLean is ready for the optional-library catalog
at these pins. Catalog and README changes are handled separately.

## How to re-sync with upstream

1. Clone upstream and diff the new upstream commit against
   `86b3823f77fc2b0f5a9923f85b588a4f8a65f94c`:
   `git diff 86b3823f..<new> -- StatLean StatLean.lean`.
2. Apply that upstream diff to this tree with `git apply --3way` or `patch -p1`. Every Lean file now has module headers, so conflicts can occur
   throughout the tree. Resolve them by keeping upstream's new mathematical content
   and re-applying both adaptation stages above.
3. Alternatively, take the new upstream tree wholesale, then re-apply the mechanical
   rewrites and fix the remaining errors module by module. The mechanical rewrites are:
   - `zero_le _` → `zero_le`
   - the primed `mul_le_mul_*` swap
   - `ENNReal.mul_le_mul_*` → `ENNReal.mul_le_mul_iff_*`
   - `NoAtoms` → `NullSingletonClass`
   - `simpa … using` → `using!` at every "Type mismatch: After simplification" error site
   - deleting `dsimp only` at every "`dsimp` made no progress" site
4. Re-apply the module conversion to every new/replaced file (`python3 port/convert_modules.py .`,
   idempotent; it skips a file that already has its header): first-line `module`,
   actual imports changed to `public import`, then `@[expose] public section` before
   the original content. Preserve docstring examples. Re-apply the listed direct imports,
   helper/instance visibility fixes, the explicit nonemptiness-proof argument, and all three
   source-name renames. Keep `requiresModuleSystem = true`. Build leaves first, re-audit
   declaration clashes against the pinned Causalean, and rebuild the module probe.
5. If upstream moves to a newer Lean/Mathlib than this copy, it is usually simpler to
   bump this copy's `lean-toolchain`/`lakefile.toml` instead.
6. Update the upstream commit hash at the top of this file, and verify that
   `lake build` succeeds and that the `sorry`/`axiom` grep count matches upstream.
7. After a full `lake build` here, publish the compiled files for the new sources:
   `bash port/build_cache.sh pack` (a release asset keyed by a hash of the sources and pins;
   `port/build_cache.sh fetch` is what an installer runs).
