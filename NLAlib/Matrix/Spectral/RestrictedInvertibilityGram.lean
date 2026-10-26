import NLAlib.Matrix.Spectral.RestrictedInvertibilityIteration
import NLAlib.Matrix.Basic.LeastSquares
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Transferring a selected-frame gap to its column Gram matrix

The nonzero spectra of the rectangular products `XXᵀ` and `XᵀX` agree.
Consequently, full column rank and a strict gap on the nonzero spectrum of
`XXᵀ` give the strict coefficient inequality required by restricted
invertibility. The proof uses the rectangular characteristic-polynomial
identity and includes empty column types.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib.RestrictedInvertibility

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A strict gap on the nonzero spectrum of `XXᵀ`, together with full column
rank, makes `XᵀX - bI` positive definite. This includes empty column spaces. -/
theorem posDef_gram_sub_smul_one_of_eigenvalues_gap
    (X : Matrix m n ℝ) (hRank : X.rank = Fintype.card n)
    (hA : (X * Xᵀ).IsHermitian) (b : ℝ)
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i) :
    (Xᵀ * X - b • (1 : Matrix n n ℝ)).PosDef := by
  have hGpos : (Xᵀ * X).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hGdef : (Xᵀ * X).PosDef :=
    hGpos.posDef_iff_isUnit.mpr (isUnit_transpose_mul_self_of_rank_eq hRank)
  let hG := hGpos.isHermitian
  have hEig : ∀ i, b < hG.eigenvalues i := by
    intro i
    let μ := hG.eigenvalues i
    have hμpos : 0 < μ := hGdef.eigenvalues_pos i
    have hmem : μ ∈ spectrum ℝ (Xᵀ * X) := by
      rw [hG.spectrum_real_eq_range_eigenvalues]
      exact ⟨i, rfl⟩
    have hroot := (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hmem).eq_zero
    have hpoly := congrArg (Polynomial.eval μ) (Matrix.charpoly_mul_comm' X Xᵀ)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hroot,
      mul_zero] at hpoly
    have hroot' : Polynomial.IsRoot (X * Xᵀ).charpoly μ := by
      exact (mul_eq_zero.mp hpoly).resolve_left (pow_ne_zero _ (ne_of_gt hμpos))
    have hmem' := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot'
    rw [hA.spectrum_real_eq_range_eigenvalues] at hmem'
    obtain ⟨j, hj⟩ := hmem'
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    rcases hgap j with hz | hb
    · exact False.elim (hμne (hj ▸ hz))
    · rwa [hj] at hb
  rw [sub_smul_one_eq_transpose_mul_diagonal_mul hG b, Matrix.transpose_transpose]
  have hdiag : (Matrix.diagonal (fun i => hG.eigenvalues i - b)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun i => sub_pos.mpr (hEig i)
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe (U := hG.eigenvectorUnitary))
      (x := Matrix.diagonal (fun i => hG.eigenvalues i - b))).mpr hdiag

/-- A selected-frame spectral gap gives the strict squared Euclidean
coefficient inequality for every nonzero coefficient vector. -/
theorem norm_mulVec_sq_gt_of_eigenvalues_gap
    (X : Matrix m n ℝ) (hRank : X.rank = Fintype.card n)
    (hA : (X * Xᵀ).IsHermitian) (b : ℝ)
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i)
    (a : n → ℝ) (ha : a ≠ 0) :
    b * ‖WithLp.toLp 2 a‖ ^ 2 < ‖WithLp.toLp 2 (X *ᵥ a)‖ ^ 2 := by
  have hpos := (posDef_gram_sub_smul_one_of_eigenvalues_gap X hRank hA b hgap).quadForm_pos ha
  simp only [quadForm, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hpos
  have hgram : a ⬝ᵥ ((Xᵀ * X) *ᵥ a) = (X *ᵥ a) ⬝ᵥ (X *ᵥ a) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hgram] at hpos
  simp only [norm_toLp_sq_eq_dotProduct_self]
  linarith

end NLAlib.RestrictedInvertibility
