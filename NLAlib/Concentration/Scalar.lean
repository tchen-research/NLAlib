import Mathlib.Probability.Moments.SubGaussian
import NLAlib.Concentration.Scalar.TailIntegral

/-!
# Scalar concentration

Mathlib already provides the sub-Gaussian MGF predicate `ProbabilityTheory.HasSubgaussianMGF`
and the Chernoff bound for independent sums. This file is the place for what Mathlib lacks:
chi-square tails (atlas `chi-square-upper-tail`), Hanson–Wright (`hanson-wright`, port from
HighDimProb), Bernstein for sub-exponential sums (`bernstein-scalar`).
-/
