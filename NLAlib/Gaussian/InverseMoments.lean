import NLAlib.Gaussian.InverseMoments.SchurComplement
import NLAlib.Gaussian.InverseMoments.Residual
import NLAlib.Gaussian.InverseMoments.Mean
import NLAlib.Gaussian.InverseMoments.DiagonalLaw
import NLAlib.Gaussian.InverseMoments.OffDiagonal
import NLAlib.Gaussian.InverseMoments.FrobeniusMoments
import NLAlib.Gaussian.InverseMoments.LambdaMinTail
import NLAlib.Gaussian.InverseMoments.SpectralTail

/-!
# Inverse moments of a standard Gaussian matrix

Aggregator for the inverse-Wishart / Gaussian-pseudoinverse results ported from the Prove2me
Gaussian Random Matrices series. For an `r × k` standard Gaussian matrix `G`, `N = (G Gᵀ)⁻¹`
and `G† = pinvR G`:

* `InverseMoments/SchurComplement.lean`: Schur complement for the off-diagonal entries of `N`,
  the residual of a row in an orthonormal basis of the kernel of the other rows, independence of
  Gaussian regression and residual;
* `InverseMoments/Residual.lean`: Schur complement for the diagonal entries of `N`
  (`Nᵢᵢ` is the inverse squared residual of row `i`), and the law `χ²_{k-n}` of that residual;
* `InverseMoments/Mean.lean`: `E N = (k - r - 1)⁻¹ I` (Tropp–Webber 2023, Lemma B.2; HMT 2011,
  Prop A.5; atlas `inverse-wishart-mean`) and `E‖G†‖_F² = r/(k - r - 1)` (HMT 2011, Prop 10.2;
  atlas `pinv-frob-moment`);
* `InverseMoments/DiagonalLaw.lean`: `Nᵢᵢ ∼ 1/χ²_{k-r+1}` and `E Nᵢᵢ²`;
* `InverseMoments/OffDiagonal.lean`: `E Nᵢⱼ²`, the rotation relation, `E Nᵢᵢ Nⱼⱼ`;
* `InverseMoments/FrobeniusMoments.lean`: `E‖N‖_F²` (atlas `inverse-wishart-frob-moment`),
  `E‖G†‖_F⁴` (Tropp–Webber 2023, Lemma B.2; atlas `pinv-frob-fourth-moment`), the Frobenius
  tail of `G†` (HMT 2011, Thm A.6; atlas `pinv-frob-tail`);
* `InverseMoments/LambdaMinTail.lean`: the lower tail of `λ_min(G Gᵀ)` (Tropp–Webber 2023,
  (B.5)–(B.7); atlas `wishart-lambda-min-tail`), obtained from Gaussian operator calculus,
  a scalar weak-density theorem, and the exact Mellin endpoint;
* `InverseMoments/SpectralTail.lean`: the spectral tail of `G†` (HMT 2011, Prop A.3; atlas
  `pinv-spectral-tail`), `E‖G†‖ ≤ e√k/(k-r)` (HMT 2011, Prop A.4; atlas
  `pinv-spectral-expectation`), `(E‖N‖^p)^{1/p} ≤ e²(k+r)/(2(k-r)²)` (Tropp–Webber 2023,
  Lemma B.4; atlas `inverse-wishart-spectral-moment`).
* `InverseMoments/Probe.lean` and `SpectralProbe.lean`: the direct Gaussian quadratic-probe
  moments, including arbitrary positive real powers below half the oversampling gap and
  the sharpened k+r-1 constants, independent of the smallest-eigenvalue density proof.

The scalar input `E[1/χ²_d] = 1/(d-2)` (atlas `inverse-chi-square-moment`) is in
`NLAlib.Gaussian.Extreme.ChiSquare`; the deterministic matrix facts (`‖G†‖_F² = tr N`,
`‖N‖₂ = 1/σ_min(Gᵀ)²`, `‖G†‖₂² = ‖N‖₂`, positivity of `N`, measurability) are in
`NLAlib.Matrix.Pseudoinverse`, `NLAlib.Matrix.Spectral`, `NLAlib.Matrix.Gram` and
`NLAlib.Matrix.Measurable`.
-/
