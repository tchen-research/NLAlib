import NLAlib.Matrix.Norms.LoewnerBounds
import Mathlib.Tactic.Module

/-!
# Convexity of realized Hermitian square mass

The operator-convex square identity is proved from positivity of (U-V)^2.
Summing in the Loewner order and using monotonicity of the positive spectral
norm gives convexity of the actual aggregate square-mass norm.
Source: the common-resolvent squared-sum mechanism supporting
Brailovskaya--van Handel, arXiv:2201.05142v3, Proposition 5.1 and Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

private theorem hermitian_sq_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) : 0 ≤ A ^ 2 := by
  simpa only [hA.eq, pow_two] using (Matrix.posSemidef_conjTranspose_mul_self A).nonneg

private theorem hermitian_convex_sq_le {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • A + t • B) ^ 2 ≤ (1 - t) • A ^ 2 + t • B ^ 2 := by
  rw [← sub_nonneg]
  have hn : 0 ≤ (t * (1 - t)) • (A - B) ^ 2 :=
    smul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (hermitian_sq_nonneg (hA.sub hB))
  convert hn using 1
  simp only [pow_two, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul]
  module

open scoped Matrix.Norms.L2Operator in
/-- The realized aggregate square-mass spectral norm is convex on Hermitian
families. No positivity of the individual matrices, nonempty dimensions,
or probability assumptions are needed. -/
theorem specNorm_sum_one_sub_smul_add_smul_sq_le
    (U V : ι → Matrix n n ℂ) (hU : ∀ i, (U i).IsHermitian)
    (hV : ∀ i, (V i).IsHermitian) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    specNorm (∑ i, ((1 - t) • U i + t • V i) ^ 2) ≤
      (1 - t) * specNorm (∑ i, U i ^ 2) + t * specNorm (∑ i, V i ^ 2) := by
  have hMix (i : ι) : ((1 - t) • U i + t • V i).IsHermitian :=
    ((hU i).smul (IsSelfAdjoint.all _)).add ((hV i).smul (IsSelfAdjoint.all _))
  have hle : (∑ i, ((1 - t) • U i + t • V i) ^ 2) ≤
      (1 - t) • (∑ i, U i ^ 2) + t • (∑ i, V i ^ 2) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hermitian_convex_sq_le (hU i) (hV i) ht0 ht1
  have hn := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (Finset.sum_nonneg (fun i _ => hermitian_sq_nonneg (hMix i))) hle
  calc
    _ ≤ ‖(1 - t) • (∑ i, U i ^ 2) + t • (∑ i, V i ^ 2)‖ := hn
    _ ≤ ‖(1 - t) • (∑ i, U i ^ 2)‖ + ‖t • (∑ i, V i ^ 2)‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
      rfl

end NLAlib
