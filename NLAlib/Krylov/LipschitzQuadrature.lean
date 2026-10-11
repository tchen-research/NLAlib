import NLAlib.Krylov.GaussQuadrature
import NLAlib.Polynomial.Jackson

/-!
# Sharp Lipschitz Gauss quadrature error

The genuine degree-`2q-1` Jackson polynomial and the proved compression exactness give
the manuscript's precise `πL(c-a)/(4q)` quadrature constant.
-/

noncomputable section

open scoped Matrix
open Polynomial Real Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- Lanczos quadrature of an interval-Lipschitz function has the sharp error
`πL(c-a)/(4q) ‖v‖²` for every isometry containing the order-`q` Krylov space.
The actual Jackson polynomial is constructed from the Lipschitz premise.
Source: Arnold, numerical analysis, Section 1.2; Golub–Meurant 2010, Section 6.2;
operator rederivations `rt:lipschitz-quad`.
atlas: lanczos-quadrature-lipschitz-error -/
theorem abs_dotProduct_cfc_mulVec_sub_le_of_lipschitzOnWith
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (v : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    {f : ℝ → ℝ} {a c : ℝ} {L : NNReal} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hf : LipschitzOnWith L f (Icc a c)) :
    |v ⬝ᵥ (cfc f A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        Real.pi * (L : ℝ) * (c - a) / (4 * q) * (v ⬝ᵥ v) := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_jackson_interval hac hf (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  have h := abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK hdeg hspec hfp
  have hcast : ((2 * q - 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) := by
    exact_mod_cast (show 2 * q - 1 + 1 = 2 * q by omega)
  rw [hcast] at h
  convert h using 1
  ring

end NLAlib
