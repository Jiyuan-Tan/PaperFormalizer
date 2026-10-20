module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyStructural

@[expose] public section

/-!
# VC uniform-entropy bounds

The corrected form of van der Vaart Lemma 19.15 is given by
`vcSubgraph_uniformLpCoveringNumber_twoRadius_le` and
`vcSubgraph_uniformLpCoveringNumber_le` from `VCUniformEntropyAssembly`.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, pp.275–276.
-/
