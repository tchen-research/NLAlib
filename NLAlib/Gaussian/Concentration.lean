import NLAlib.Gaussian.Concentration.IntegrationByParts
import NLAlib.Gaussian.Concentration.OrnsteinUhlenbeck
import NLAlib.Gaussian.Concentration.OrnsteinUhlenbeckEntropy
import NLAlib.Gaussian.Concentration.LogSobolevOneDim
import NLAlib.Gaussian.Concentration.LogSobolev
import NLAlib.Gaussian.Concentration.LipschitzConcentration

/-!
# Gaussian concentration

The Gaussian concentration inequality for Lipschitz functions (HMT 2011, Prop 10.3; Vershynin
2012, Prop 5.34) by the entropy method: Gaussian integration by parts, the Ornstein–Uhlenbeck
semigroup, Gross's logarithmic Sobolev inequality, tensorization of entropy and Herbst's
argument. Ported from the Prove2me Gaussian Random Matrices series.

Files (atlas ids):
* `IntegrationByParts` (`gaussian-integration-by-parts`): Stein's identity, one-dimensional and
  multivariate;
* `OrnsteinUhlenbeck`, `OrnsteinUhlenbeckEntropy` (`ornstein-uhlenbeck`): `ornsteinUhlenbeck`,
  invariance of `γ`, commutation `(P_t f)' = e^{-t} P_t f'`, entropy dissipation;
* `LogSobolevOneDim`, `LogSobolev` (`gaussian-log-sobolev`): `Ent(g²) ≤ 2 ∫ |∇g|²`;
* `LipschitzConcentration` (`gaussian-concentration`): `gaussian_concentration_pi` on
  `Measure.pi fun _ => gaussianReal 0 1` and `gaussian_concentration` on `gaussianMatrix p m`.

The two steps that are not Gaussian-specific live in layer 1: tensorization of entropy
(`entropy-tensorization`, `NLAlib.Concentration.Scalar.EntropyTensorization`) and Herbst's
argument (`herbst`, `NLAlib.Concentration.Scalar.Herbst`).
-/
