import NLAlib.Gaussian.InverseMoments.SchurComplement
import NLAlib.Gaussian.InverseMoments.DiagonalLaw
import NLAlib.Gaussian.InverseMoments.OffDiagonal
import NLAlib.Gaussian.InverseMoments.FrobeniusMoments
import NLAlib.Gaussian.InverseMoments.SpectralNorm
import NLAlib.Gaussian.InverseMoments.LambdaMinTail
import NLAlib.Gaussian.InverseMoments.SpectralTail

/-!
# Inverse Wishart and pseudoinverse moments

Aggregator for the inverse-Wishart / Gaussian-pseudoinverse results ported from the Prove2me
Gaussian Random Matrices series. For an `r × k` standard Gaussian matrix `G`, `N = (G Gᵀ)⁻¹`
and `G† = pinvR G`:

* `InverseMoments/SchurComplement.lean`: Schur complement for the off-diagonal entries of `N`,
  independence of Gaussian regression and residual;
* `InverseMoments/DiagonalLaw.lean`: `Nᵢᵢ ∼ 1/χ²_{k-r+1}` and `E Nᵢᵢ²`;
* `InverseMoments/OffDiagonal.lean`: `E Nᵢⱼ²`, the rotation relation, `E Nᵢᵢ Nⱼⱼ`;
* `InverseMoments/FrobeniusMoments.lean`: `E‖N‖_F²` (atlas `inverse-wishart-frob-moment`),
  `E‖G†‖_F⁴` (Tropp–Webber 2023, Lemma B.2; atlas `pinv-frob-fourth-moment`), the Frobenius
  tail of `G†` (HMT 2011, Thm A.6; atlas `pinv-frob-tail`);
* `InverseMoments/SpectralNorm.lean`: `‖N‖ = 1/σ_min(Gᵀ)²`, `‖G†‖² = ‖N‖`;
* `InverseMoments/LambdaMinTail.lean`: the lower tail of `λ_min(G Gᵀ)` (Tropp–Webber 2023,
  (B.5)–(B.7); atlas `wishart-lambda-min-tail`), resting on the scaffold
  `gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral` (`SCAFFOLD: wishart-lambda-min-tail`);
* `InverseMoments/SpectralTail.lean`: the spectral tail of `G†` (HMT 2011, Prop A.3; atlas
  `pinv-spectral-tail`), `E‖G†‖ ≤ e√k/(k-r)` (HMT 2011, Prop A.4; atlas
  `pinv-spectral-expectation`), `(E‖N‖^p)^{1/p} ≤ e²(k+r)/(2(k-r)²)` (Tropp–Webber 2023,
  Lemma B.4; atlas `inverse-wishart-spectral-moment`).
-/
