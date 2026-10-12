import NLAlib.Matrix.Inequalities.LogDetConcavity
import NLAlib.ForMathlib.Analysis.InverseConvexity
/-!
# Strict convexity of inverse trace

The inverse trace of a simultaneously diagonalized positive definite pair
is a scalar reciprocal sum with strictly positive Gram weights.
Source: Horn--Johnson (2013), Theorem 7.8.21; atlas `log-det-concavity`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of the inverse is strictly convex on the real positive definite
cone. The empty-dimensional cone is included. Horn--Johnson (2013),
Theorem 7.8.21.
atlas: log-det-concavity (partial) -/
theorem strictConvexOn_trace_inv :
    StrictConvexOn ℝ {A : Matrix n n ℝ | A.PosDef} (fun A => A⁻¹.trace) := by
  refine ⟨convex_setOf_posDef, ?_⟩
  intro A hA B hB hAB a b ha hb hab
  obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_positive_definite_pair_congruence hA hB
  let L := Sᵀ⁻¹
  let w : n → ℝ := fun i => (Lᵀ * L) i i
  have hLu : IsUnit L := Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_transpose S).mpr hS)
  have hw : ∀ i, 0 < w i := by
    have hG : (Lᵀ * L).PosDef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.PosDef.conjTranspose_mul_self L (Matrix.mulVec_injective_of_isUnit hLu)
    exact fun i => hG.diag_pos (i := i)
  have hLt : Lᵀ = S⁻¹ := by simp only [L, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
  have hAi : A⁻¹.trace = ∑ i, w i := by
    have he : A⁻¹ = L * Lᵀ := by rw [hAA, Matrix.mul_inv_rev, hLt]
    rw [he, Matrix.trace_mul_comm]
    rfl
  have hBi : B⁻¹.trace = ∑ i, (d i)⁻¹ * w i := by
    rw [hBB, inv_congruence_diagonal S d (fun i => (hd i).ne')]
    change (L * diagonal (fun i => (d i)⁻¹) * S⁻¹).trace = _
    rw [← hLt, trace_congruence_diagonal]
  have hCi : (a • A + b • B)⁻¹.trace = ∑ i, (a + b * d i)⁻¹ * w i := by
    rw [smul_add_smul_eq_congruence_diagonal hAA hBB,
      inv_congruence_diagonal S _ (fun i => (add_pos ha (mul_pos hb (hd i))).ne')]
    change (L * diagonal (fun i => (a + b * d i)⁻¹) * S⁻¹).trace = _
    rw [← hLt, trace_congruence_diagonal]
  have hle (i : n) : (a + b * d i)⁻¹ * w i ≤ a * w i + b * ((d i)⁻¹ * w i) := by
    calc
      _ ≤ (a + b * (d i)⁻¹) * w i := mul_le_mul_of_nonneg_right
        (inv_affine_le_affine_inv_and_lt_of_ne ha hb hab (hd i)).1 (hw i).le
      _ = _ := by ring
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 1 := by
    by_contra hnone
    push Not at hnone
    apply hAB
    have hd1 : d = fun _ => 1 := funext hnone
    rw [hAA, hBB, hd1, Matrix.diagonal_one, Matrix.mul_one]
  have hlt : (a + b * d i)⁻¹ * w i < a * w i + b * ((d i)⁻¹ * w i) := by
    calc
      _ < (a + b * (d i)⁻¹) * w i := mul_lt_mul_of_pos_right
        ((inv_affine_le_affine_inv_and_lt_of_ne ha hb hab (hd i)).2 hi) (hw i)
      _ = _ := by ring
  have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset n))
    (fun i _ => hle i) ⟨i, Finset.mem_univ i, hlt⟩
  simp only [smul_eq_mul]
  rw [hAi, hBi, hCi]
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum

/-- Inverse-trace Jensen includes both endpoint weights.
Horn--Johnson (2013), Theorem 7.8.21.
atlas: log-det-concavity (partial) -/
theorem trace_inv_smul_add_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B)⁻¹.trace ≤ a * A⁻¹.trace + b * B⁻¹.trace :=
  strictConvexOn_trace_inv.convexOn.2 hA hB ha hb hab

/-- Interior equality in inverse-trace Jensen holds exactly for equal
positive definite matrices. Horn--Johnson (2013), Theorem 7.8.21.
atlas: log-det-concavity (partial) -/
theorem trace_inv_smul_add_eq_iff {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (a • A + b • B)⁻¹.trace = a * A⁻¹.trace + b * B⁻¹.trace ↔ A = B := by
  constructor
  · intro heq
    by_contra hne
    have h := strictConvexOn_trace_inv.2 hA hB hne ha hb hab
    change (a • A + b • B)⁻¹.trace < a * A⁻¹.trace + b * B⁻¹.trace at h
    linarith
  · rintro rfl
    rw [← add_smul, hab, one_smul, ← add_mul, hab, one_mul]

end NLAlib
