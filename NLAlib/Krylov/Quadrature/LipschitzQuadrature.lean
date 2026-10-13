import NLAlib.Krylov.Quadrature.GaussQuadrature
import NLAlib.Polynomial.BestApproximation.Jackson
/-!
# Lipschitz Gauss quadrature error

The degree-`2q − 1` Jackson polynomial (`jackson-lipschitz`) and Gauss exactness
(`lanczos-gauss-quadrature`) give the quadrature error `πL(c − a)/(4q) ‖v‖²` for an
`L`-Lipschitz function on the spectral interval `[a, c]`.
-/

noncomputable section

open scoped Matrix
open Polynomial Real Set

namespace NLAlib

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- **Gauss quadrature error for a Lipschitz function**: if `f` is `L`-Lipschitz on `[a, c]`,
an interval containing the spectrum of the symmetric `A`, `Q` has orthonormal columns and
`K_q(A, v) ⊆ range Q` (`q ≥ 1`), then `|vᵀ f(A) v − (Qᵀv)ᵀ f(QᵀAQ) (Qᵀv)| ≤ πL(c − a)/(4q) ‖v‖²`.
Source: Golub–Meurant (2010) [`gm10`], §6.2, with Jackson's theorem (Cheney (1966), §4.6).
atlas: lanczos-quadrature-lipschitz-error -/
theorem abs_dotProduct_cfc_mulVec_sub_le_of_lipschitzOnWith
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (v : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    {f : ℝ → ℝ} {a c : ℝ} {L : NNReal} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hf : LipschitzOnWith L f (Icc a c)) :
    |v ⬝ᵥ (cfc f A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        Real.pi * (L : ℝ) * (c - a) / (4 * q) * ‖WithLp.toLp 2 v‖ ^ 2 := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_jackson_interval hac hf (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  have h := abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK hdeg hspec hfp
  have hcast : ((2 * q - 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) := by
    exact_mod_cast (show 2 * q - 1 + 1 = 2 * q by omega)
  rw [hcast] at h
  convert h using 1
  ring

end NLAlib
