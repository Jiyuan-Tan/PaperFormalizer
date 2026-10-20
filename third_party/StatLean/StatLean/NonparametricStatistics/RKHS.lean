module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import StatLean.NonparametricStatistics.RKHS.KernelFunction
public import StatLean.NonparametricStatistics.RKHS.OrthonormalExpansion
public import StatLean.NonparametricStatistics.RKHS.Subspace
public import StatLean.NonparametricStatistics.RKHS.Continuity
public import StatLean.NonparametricStatistics.RKHS.ParsevalFrame
public import StatLean.NonparametricStatistics.RKHS.Papadakis
public import StatLean.NonparametricStatistics.RKHS.Moore
public import StatLean.NonparametricStatistics.RKHS.Uniqueness
public import StatLean.NonparametricStatistics.RKHS.RankOne
public import StatLean.NonparametricStatistics.RKHS.InnerKernel
public import StatLean.NonparametricStatistics.RKHS.MinKernel
public import StatLean.NonparametricStatistics.RKHS.Sobolev
public import StatLean.NonparametricStatistics.RKHS.FeatureMap
public import StatLean.NonparametricStatistics.RKHS.Separation
public import StatLean.NonparametricStatistics.RKHS.MaxMargin
public import StatLean.NonparametricStatistics.RKHS.Representer
public import StatLean.NonparametricStatistics.RKHS.IntegralOperator
public import StatLean.NonparametricStatistics.RKHS.RangeSpace
public import StatLean.NonparametricStatistics.RKHS.Mercer.Defs
public import StatLean.NonparametricStatistics.RKHS.Mercer.OperatorLemmas
public import StatLean.NonparametricStatistics.RKHS.Mercer.Basic
public import StatLean.NonparametricStatistics.RKHS.Mercer.Compact
public import StatLean.NonparametricStatistics.RKHS.Mercer.Theorem
public import StatLean.NonparametricStatistics.RKHS.Mercer.SquareRoot

@[expose] public section

/-!
# Reproducing kernel Hilbert spaces

Umbrella module for the RKHS cluster of the nonparametric-statistics area: scalar RKHS
theory over Mathlib's `RKHS` class, kernel functions and Moore's theorem, Parseval
frames, the Sobolev and min-kernel examples, feature maps / maximal margin / representer
theorems, integral operators and range spaces, and Mercer theory.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University
Press, 2016. Chapters 1 (§1.1, §1.3.1), 2 (§§2.1–2.4), 8 (§§8.2–8.6), and 11 (§§11.1–11.3).
-/
