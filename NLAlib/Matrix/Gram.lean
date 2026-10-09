import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Order.Star.Real

/-!
# Gram matrices and their inverses

Deterministic facts about the Gram matrix `G Gᵀ` and its inverse, used by the inverse-Wishart
moment computations of `NLAlib.Gaussian.InverseMoments`:

* `det_ne_zero_of_rank_eq`: a square real matrix of full rank has nonzero determinant;
* `posSemidef_inv_self_mul_transpose`: `(G Gᵀ)⁻¹` is positive semidefinite (Mathlib's total
  inverse, so also when `G Gᵀ` is singular);
* `abs_apply_le_apply_self_add_apply_self`: an entry of a positive semidefinite matrix is
  dominated by the diagonal, `|Mᵢⱼ| ≤ Mᵢᵢ + Mⱼⱼ`.

Layer 0. `det_ne_zero_of_rank_eq` is a general fact and a candidate for `NLAlib.ForMathlib`.

Atlas: `inverse-wishart-mean` (helpers).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

/-- A square real matrix of full rank has nonzero determinant.

Helper (linear algebra) for the inverse-Wishart computations. Atlas: `inverse-wishart-mean`
(helper). Generalised from `Fin n` to an arbitrary finite index type. Ported from the Prove2me
solutions of the inverse Wishart series (`rri_det_ne_zero_of_rank`). -/
theorem det_ne_zero_of_rank_eq {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (h : M.rank = Fintype.card n) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
  have h1 : 0 < Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, by simpa using hv⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Matrix.rank] at h
  simp only [Module.finrank_fintype_fun_eq_card] at h2
  omega

/-- `(G Gᵀ)⁻¹` is positive semidefinite for every real matrix `G`.

Helper for Tropp–Webber 2023, App. B. Atlas: `inverse-wishart-mean` (helper). Ported from the
Prove2me solution `Sol_GaussianMatrix_inverse_wishart_rotation_relation` (`iwr_psd_inv`). -/
theorem posSemidef_inv_self_mul_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (G : Matrix m n ℝ) : ((G * Gᵀ)⁻¹).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose G
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.inv

/-- An entry of a real positive semidefinite matrix is dominated by the diagonal:
`|Mᵢⱼ| ≤ Mᵢᵢ + Mⱼⱼ`.

Helper for Tropp–Webber 2023, App. B. Atlas: `inverse-wishart-mean` (helper). Ported from the
Prove2me solution `Sol_GaussianMatrix_inverse_wishart_rotation_relation` (`iwr_psd_offdiag`). -/
theorem abs_apply_le_apply_self_add_apply_self {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.PosSemidef) (i j : m) : |M i j| ≤ M i i + M j j := by
  have hs : M j i = M i j := by
    have := hM.isHermitian.apply i j
    simpa using this
  by_cases hij : i = j
  · subst hij
    have := hM.diag_nonneg (i := i)
    rw [abs_of_nonneg this]; linarith
  have h1 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, Matrix.mulVec_single, single_dotProduct,
    hs] at h1 h2
  rw [abs_le]; constructor <;> linarith

end NLAlib
