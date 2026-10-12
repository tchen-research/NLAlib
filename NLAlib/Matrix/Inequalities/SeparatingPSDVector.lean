import NLAlib.Matrix.Inequalities.BlockOrderConsequences
import NLAlib.ForMathlib.LinearAlgebra.SeparatingRows
/-!
# A rank-one PSD certificate with distinct coordinates

Normalize a separating matrix image by the square root of one plus its
quadratic energy. PSD Cauchy--Schwarz then bounds its rank-one Gram matrix
by the original PSD matrix. Source: Horn--Johnson (2013), Section 7.5;
supports the finite entrywise exponential certificate.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- PSD Cauchy--Schwarz for a real symmetric form, including its kernel.
Horn--Johnson (2013), Section 7.1; helper for rank-one domination. -/
theorem sq_bilinear_le_quadForm_mul_of_posSemidef {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (x y : n → ℝ) :
    (x ⬝ᵥ A *ᵥ y) ^ 2 ≤ quadForm A x * quadForm A y := by
  have hAt : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hH : (fromBlocks A A Aᵀ A).PosSemidef := by
    rw [hAt]
    exact (posSemidef_equal_diagonal_fromBlocks_iff_le hA hA).mpr le_rfl
  exact sq_bilinear_le_quadForm_mul_of_fromBlocks_posSemidef hH x y

/-- A PSD matrix with pairwise distinct rows dominates a rank-one Gram
matrix whose defining coordinates are pairwise distinct. This deterministic
certificate allows singular input and a zero row.
Horn--Johnson (2013), proof of Theorem 7.5.9;
helper for strict entrywise exponential positivity. -/
theorem exists_injective_vecMulVec_le_of_posSemidef_rows_injective
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (hrows : Function.Injective A.row) :
    ∃ b : n → ℝ, Function.Injective b ∧ vecMulVec b b ≤ A := by
  obtain ⟨z, hz⟩ := exists_mulVec_injective_of_rows_injective A hrows
  let ν := quadForm A z
  have hν : 0 ≤ ν := by simpa only [ν, quadForm, star_trivial] using hA.dotProduct_mulVec_nonneg z
  let r := Real.sqrt (1 + ν)
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hrs : r ^ 2 = 1 + ν := Real.sq_sqrt (by linarith)
  let b := r⁻¹ • (A *ᵥ z)
  have hb : Function.Injective b := by
    intro i j hij
    apply hz
    apply mul_left_cancel₀ (inv_ne_zero hr.ne')
    exact hij
  refine ⟨b, hb, ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.isHermitian.sub (by simpa only [star_trivial] using
      (Matrix.posSemidef_vecMulVec_self_star b).isHermitian))
  intro x
  have hx : 0 ≤ quadForm A x := by simpa only [quadForm, star_trivial] using hA.dotProduct_mulVec_nonneg x
  have hcs := sq_bilinear_le_quadForm_mul_of_posSemidef hA x z
  have hscaled : x ⬝ᵥ b = (x ⬝ᵥ A *ᵥ z) / r := by
    simp only [b, dotProduct_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbound : (x ⬝ᵥ b) ^ 2 ≤ quadForm A x := by
    rw [hscaled, div_pow, hrs]
    apply (div_le_iff₀ (show 0 < 1 + ν by linarith)).mpr
    change (x ⬝ᵥ A *ᵥ z) ^ 2 ≤ quadForm A x * (1 + quadForm A z)
    nlinarith
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  change 0 ≤ quadForm A x - quadForm (vecMulVec b b) x
  rw [quadForm_vecMulVec_self, sub_nonneg]
  exact hbound

end NLAlib
