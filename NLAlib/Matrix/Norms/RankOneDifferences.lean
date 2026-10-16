import NLAlib.Matrix.Norms.Core

/-!
# Frobenius distances between real rank-one matrices

Unit-vector rank-one matrices have the increment comparison used in Gaussian
minimax arguments. The statement is real: complex phases do not obey this
particular comparison with the same constant.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

private theorem rank_one_coeff_ineq {m n : Type*} [Fintype m] [Fintype n] (u u' : EuclideanSpace ℝ n)
    (v v' : EuclideanSpace ℝ m)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2 ≤ ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu, one_pow]
  have su' : ∑ j, u' j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu', one_pow]
  have sv : ∑ i, v i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hv, one_pow]
  have sv' : ∑ i, v' i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hv', one_pow]
  set α := ∑ j, u j * u' j with hαdef
  set β := ∑ i, v i * v' i with hβdef
  have hL : ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2
      = (∑ i, v i ^ 2) * (∑ j, u j ^ 2) - 2 * (β * α) + (∑ i, v' i ^ 2) * (∑ j, u' j ^ 2) := by
    rw [hαdef, hβdef, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRu : ∑ j, (u j - u' j) ^ 2 = ∑ j, u j ^ 2 - 2 * α + ∑ j, u' j ^ 2 := by
    rw [hαdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRv : ∑ i, (v i - v' i) ^ 2 = ∑ i, v i ^ 2 - 2 * β + ∑ i, v' i ^ 2 := by
    rw [hβdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : α ≤ 1 := by
    have : 0 ≤ ∑ j, (u j - u' j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hβ : β ≤ 1 := by
    have : 0 ≤ ∑ i, (v i - v' i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [hL, hRu, hRv, su, su', sv, sv']
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

private theorem rank_one_coeff_same {m n : Type*} [Fintype m] [Fintype n] (u : EuclideanSpace ℝ n)
    (v v' : EuclideanSpace ℝ m)
    (hu : ‖u‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u j) ^ 2 = ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu, one_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ j, (v i * u j - v' i * u j) ^ 2 = (v i - v' i) ^ 2 * u j ^ 2 := fun j => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, su, mul_one]

/-- The Frobenius distance between two real unit-vector outer products is
bounded by the sum of the two squared Euclidean distances. This is the
coefficient comparison in Gordon's Gaussian minimax argument. -/
theorem frobSq_vecMulVec_sub_le_norm_sq_add {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ n) (v v' : EuclideanSpace ℝ m)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    frobSq (Matrix.vecMulVec v.ofLp u.ofLp - Matrix.vecMulVec v'.ofLp u'.ofLp)
      ≤ ‖u-u'‖ ^ 2 + ‖v-v'‖ ^ 2 := by
  simpa only [frobSq_eq_sum_sq, Matrix.sub_apply, Matrix.vecMulVec_apply,
    EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply] using
    rank_one_coeff_ineq u u' v v' hu hu' hv hv'

/-- With one unit-vector factor fixed, the Frobenius distance between the
outer products is exactly the Euclidean distance between the other factors. -/
theorem frobSq_vecMulVec_sub_same_eq_norm_sq {m n : Type*} [Fintype m] [Fintype n]
    (u : EuclideanSpace ℝ n) (v v' : EuclideanSpace ℝ m) (hu : ‖u‖ = 1) :
    frobSq (Matrix.vecMulVec v.ofLp u.ofLp - Matrix.vecMulVec v'.ofLp u.ofLp)
      = ‖v-v'‖ ^ 2 := by
  simpa only [frobSq_eq_sum_sq, Matrix.sub_apply, Matrix.vecMulVec_apply,
    EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply] using
    rank_one_coeff_same u v v' hu

end NLAlib
