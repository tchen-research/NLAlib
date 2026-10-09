import NLAlib.Gaussian.Comparison.Interpolation
import NLAlib.Gaussian.Comparison.Slepian
import NLAlib.Gaussian.Comparison.SudakovFernique
import NLAlib.Gaussian.Comparison.GordonMinimax
import NLAlib.Gaussian.Comparison.ExpectationNormDiff

/-!
# Gaussian comparison inequalities

Comparison of maxima and minimax values of Gaussian processes by Gaussian interpolation.

* `Interpolation`: second-moment bookkeeping along `cos θ X + sin θ Y`;
* `Slepian` (`slepian`): `slepian_inequality`;
* `SudakovFernique` (`sudakov-fernique`): `sudakov_fernique_inequality`;
* `GordonMinimax` (`gordon-minimax`): `gordon_minimax_inequality` and the general interpolation
  principle `integral_le_integral_of_covariance_hessian_nonneg`;
* `ExpectationNormDiff` (helper of `gordon`): `√N - √n ≤ 𝔼‖g_N‖ - 𝔼‖g_n‖`.
-/
