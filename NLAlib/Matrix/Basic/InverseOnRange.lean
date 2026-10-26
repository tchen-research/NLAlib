import NLAlib.Matrix.Basic.LeastSquares
import NLAlib.Matrix.Basic.QuadForm

/-!
# The inverse of an injective matrix on its range

This is the actual bounded inverse from the Euclidean range of an injective
rectangular matrix to its coefficient space. Its operator norm therefore
has the inverse-on-range meaning used in restricted invertibility, without
an assumption that the matrix is square.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The actual inverse of an injective rectangular matrix, defined on its
Euclidean range. It is the inverse of the canonical linear equivalence onto
that range, with continuity supplied by finite dimensionality. -/
def inverseOnRange (A : Matrix m n ℝ) (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    LinearMap.range (Matrix.toEuclideanLin A) →L[ℝ] EuclideanSpace ℝ n :=
  ((LinearEquiv.ofInjective (Matrix.toEuclideanLin A) hA).symm.toLinearMap).toContinuousLinearMap

/-- Applying the original matrix after its range inverse recovers the range
vector. -/
@[simp] theorem toEuclideanLin_inverseOnRange (A : Matrix m n ℝ)
    (hA : Function.Injective (Matrix.toEuclideanLin A))
    (y : LinearMap.range (Matrix.toEuclideanLin A)) :
    Matrix.toEuclideanLin A (inverseOnRange A hA y) = y.val := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective (Matrix.toEuclideanLin A) hA).apply_symm_apply y)

/-- A positive definite column Gram matrix makes the Euclidean matrix map
injective. -/
theorem injective_toEuclideanLin_of_posDef_gram (A : Matrix m n ℝ)
    (hG : (Aᵀ * A).PosDef) : Function.Injective (Matrix.toEuclideanLin A) := by
  have hmul : Function.Injective A.mulVec := by
    intro x y hxy
    apply Matrix.mulVec_injective_of_isUnit hG.isUnit
    simp only [← Matrix.mulVec_mulVec, hxy]
  intro x y hxy
  apply WithLp.ofLp_injective
  apply hmul
  apply WithLp.toLp_injective 2
  exact hxy

/-- A positive lower column-Gram barrier bounds the norm of the actual
inverse on the selected range by the reciprocal square root of that barrier. -/
theorem norm_inverseOnRange_le_of_posDef_gram_sub
    (A : Matrix m n ℝ) (hA : Function.Injective (Matrix.toEuclideanLin A))
    {b : ℝ} (hb : 0 < b)
    (hG : (Aᵀ * A - b • (1 : Matrix n n ℝ)).PosDef) :
    ‖inverseOnRange A hA‖ ≤ 1 / Real.sqrt b := by
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro y
  let x : EuclideanSpace ℝ n := inverseOnRange A hA y
  have hAx : Matrix.toEuclideanLin A x = y.val := toEuclideanLin_inverseOnRange A hA y
  have hh := hG.posSemidef.quadForm_nonneg x.ofLp
  simp only [quadForm, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hh
  have hgram : x.ofLp ⬝ᵥ ((Aᵀ * A) *ᵥ x.ofLp) =
      (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hgram, ← norm_toLp_sq_eq_dotProduct_self, ← norm_toLp_sq_eq_dotProduct_self] at hh
  change 0 ≤ ‖Matrix.toEuclideanLin A x‖ ^ 2 - b * ‖x‖ ^ 2 at hh
  rw [hAx] at hh
  have hynorm : ‖y.val‖ = ‖y‖ := rfl
  rw [hynorm] at hh
  have hbound : ‖x‖ ≤ ‖y‖ / Real.sqrt b := by
    apply (le_div_iff₀ hsqrt).mpr
    nlinarith [Real.sq_sqrt hb.le, norm_nonneg x, norm_nonneg y]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hbound

end NLAlib
