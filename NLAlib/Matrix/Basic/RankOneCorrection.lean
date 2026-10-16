import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!+# Minimum Frobenius correction in a prescribed unit direction

Among matrices that cancel the image of a unit vector, the unique smallest
Frobenius correction is the negative rank-one outer product. An exact
orthogonal residual identity proves its value and uniqueness.
-/
noncomputable section
open Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- Frobenius energy of an outer product is the product of vector energies. -/
theorem frobSq_vecMulVec_star (u : m → 𝕜) (v : n → 𝕜) :
    frobSq (Matrix.vecMulVec u (star v)) =
      ‖WithLp.toLp 2 u‖ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp only [frobSq_eq_sum_norm_sq, Matrix.vecMulVec_apply, Pi.star_apply, norm_mul,
    norm_star, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, EuclideanSpace.norm_sq_eq]

/-- Pairing a rank-one outer product with a matrix is a vector pairing. -/
theorem frobInner_vecMulVec_star (u : m → 𝕜) (v : n → 𝕜) (M : Matrix m n 𝕜) :
    frobInner (Matrix.vecMulVec u (star v)) M = RCLike.re (star u ⬝ᵥ (M *ᵥ v)) := by
  unfold frobInner
  congr 1
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_mul, star_star,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The unique candidate correction canceling the image of a unit direction. -/
def rankOneCancel (C : Matrix m n 𝕜) (v : n → 𝕜) : Matrix m n 𝕜 :=
  -Matrix.vecMulVec (C *ᵥ v) (star v)

/-- A rank-one correction cancels exactly the chosen unit image. -/
theorem rankOneCancel_mulVec (C : Matrix m n 𝕜) (v : n → 𝕜)
    (hv : ‖WithLp.toLp 2 v‖ = 1) : rankOneCancel C v *ᵥ v = -(C *ᵥ v) := by
  have hdot : star v ⬝ᵥ v = (1 : 𝕜) := by
    have he : inner 𝕜 (WithLp.toLp 2 v) (WithLp.toLp 2 v) = (1 : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
    simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using he
  rw [rankOneCancel, Matrix.neg_mulVec, Matrix.vecMulVec_mulVec, hdot,
    MulOpposite.op_one, one_smul]

/-- The attained Frobenius cost in a prescribed unit direction. -/
theorem frobSq_rankOneCancel (C : Matrix m n 𝕜) (v : n → 𝕜)
    (hv : ‖WithLp.toLp 2 v‖ = 1) :
    frobSq (rankOneCancel C v) = ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 := by
  simp only [rankOneCancel, frobSq_neg, frobSq_vecMulVec_star, hv, one_pow, mul_one]

/-- The full Frobenius orthogonal decomposition for every feasible
correction, not only the lower bound. -/
theorem frobSq_correction_decomposition (C D : Matrix m n 𝕜) (v : n → 𝕜)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (hD : D *ᵥ v = -(C *ᵥ v)) :
    frobSq D = ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 + frobSq (D - rankOneCancel C v) := by
  have hz : (D - rankOneCancel C v) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hD, rankOneCancel_mulVec C v hv, sub_self]
  have hi : frobInner (rankOneCancel C v) (D - rankOneCancel C v) = 0 := by
    change frobInner (-Matrix.vecMulVec (C *ᵥ v) (star v)) (D - rankOneCancel C v) = 0
    rw [frobInner_neg_left, frobInner_vecMulVec_star, hz,
      dotProduct_zero, map_zero, neg_zero]
  have he := frobSq_add_of_frobInner_eq_zero (rankOneCancel C v) (D - rankOneCancel C v) hi
  rw [add_sub_cancel, frobSq_rankOneCancel C v hv] at he
  exact he

/-- For a fixed unit direction the rank-one correction is the unique
minimum, with its exact energy. -/
theorem frobSq_correction_minimum_iff (C D : Matrix m n 𝕜) (v : n → 𝕜)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (hD : D *ᵥ v = -(C *ᵥ v)) :
    ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 ≤ frobSq D ∧
      (frobSq D = ‖WithLp.toLp 2 (C *ᵥ v)‖ ^ 2 ↔ D = rankOneCancel C v) := by
  have he := frobSq_correction_decomposition C D v hv hD
  constructor
  · linarith [frobSq_nonneg (D - rankOneCancel C v)]
  · constructor
    · intro hh
      have hz : frobSq (D - rankOneCancel C v) = 0 := by linarith
      exact sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hz)
    · rintro rfl
      exact frobSq_rankOneCancel C v hv

end NLAlib
