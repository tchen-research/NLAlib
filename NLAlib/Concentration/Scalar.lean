import Mathlib.Probability.Moments.SubGaussian
import NLAlib.Concentration.Scalar.TailIntegral
import NLAlib.Concentration.Scalar.EntropyTensorization
import NLAlib.Concentration.Scalar.Herbst

/-!
# Scalar concentration

Mathlib already provides the sub-Gaussian MGF predicate `ProbabilityTheory.HasSubgaussianMGF`
and the Chernoff bound for independent sums. This file is the place for what Mathlib lacks:
chi-square tails (atlas `chi-square-upper-tail`), Hanson–Wright (`hanson-wright`, port from
HighDimProb), Bernstein for sub-exponential sums (`bernstein-scalar`).

Files (atlas ids):
* `TailIntegral` (`tail-integral`): moments from polynomial tails;
* `EntropyTensorization` (`entropy-tensorization`): `Ent_μ(h) ≤ ∑ᵢ 𝔼 Ent_{μᵢ}(h)` for a product
  probability measure, and the Gibbs variational inequality;
* `Herbst` (`herbst`): an entropy bound `Ent(e^{s f}) ≤ c s² 𝔼 e^{s f}` gives a sub-Gaussian
  moment generating function.
-/
