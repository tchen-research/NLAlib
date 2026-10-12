import NLAlib.Matrix.DefinitePairCalculus
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Strict log-determinant concavity

Simultaneous congruence reduces the inequality and its exact equality case
to strict scalar log concavity. Source: Horn--Johnson (2013), Theorem 7.6.6;
atlas `log-det-concavity`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The cone of positive definite real matrices is convex, including the
zero-dimensional singleton cone. Horn--Johnson (2013), Section 7.6;
helper for determinant and inverse convexity. -/
theorem convex_setOf_posDef : Convex ℝ {A : Matrix n n ℝ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  rcases lt_or_eq_of_le ha with ha | ha
  · exact (hA.smul ha).add_posSemidef (hB.posSemidef.smul hb)
  · have hb1 : b = 1 := by linarith
    simp only [← ha, hb1, zero_smul, one_smul, zero_add]
    exact hB

/-- Log determinant is strictly concave on the real positive definite cone.
This includes the empty-dimensional cone, where the strict condition is
vacuous because there are no distinct matrices. Horn--Johnson (2013),
Theorem 7.6.6.
atlas: log-det-concavity (partial) -/
theorem strictConcaveOn_log_det :
    StrictConcaveOn ℝ {A : Matrix n n ℝ | A.PosDef} (fun A => Real.log A.det) := by
  refine ⟨convex_setOf_posDef, ?_⟩
  intro A hA B hB hAB a b ha hb hab
  obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_positive_definite_pair_congruence hA hB
  have hAi : Real.log A.det = Real.log (S.det ^ 2) := by
    rw [hAA, Matrix.det_mul, Matrix.det_transpose, ← sq]
  have hBi : Real.log B.det = Real.log (S.det ^ 2) + ∑ i, Real.log (d i) := by
    rw [hBB]
    exact log_det_congruence_diagonal hS d hd
  have hCi : Real.log (a • A + b • B).det =
      Real.log (S.det ^ 2) + ∑ i, Real.log (a + b * d i) := by
    rw [smul_add_smul_eq_congruence_diagonal hAA hBB]
    exact log_det_congruence_diagonal hS _ (fun i => add_pos ha (mul_pos hb (hd i)))
  have hle (i : n) : b * Real.log (d i) ≤ Real.log (a + b * d i) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.2
      (Set.mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)) (Set.mem_Ioi.mpr (hd i)) ha.le hb.le hab
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] using h
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 1 := by
    by_contra hnone
    push Not at hnone
    apply hAB
    have hd1 : d = fun _ => 1 := funext hnone
    rw [hAA, hBB, hd1, Matrix.diagonal_one, Matrix.mul_one]
  have hlt : b * Real.log (d i) < Real.log (a + b * d i) := by
    have h := strictConcaveOn_log_Ioi.2
      (Set.mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)) (Set.mem_Ioi.mpr (hd i)) hi.symm ha hb hab
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] using h
  have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset n))
    (fun i _ => hle i) ⟨i, Finset.mem_univ i, hlt⟩
  rw [← Finset.mul_sum] at hsum
  simp only [smul_eq_mul]
  rw [hAi, hBi, hCi]
  have hscale := congrArg (fun t : ℝ => t * Real.log (S.det ^ 2)) hab
  nlinarith

/-- The log-determinant Jensen inequality holds at both endpoints as well
as in the interior. Horn--Johnson (2013), Theorem 7.6.6.
atlas: log-det-concavity (partial) -/
theorem log_det_smul_add_ge {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Real.log A.det + b * Real.log B.det ≤ Real.log (a • A + b • B).det :=
  strictConcaveOn_log_det.concaveOn.2 hA hB ha hb hab

/-- Interior equality in log-determinant Jensen holds exactly for equal
positive definite matrices. Horn--Johnson (2013), Theorem 7.6.6.
atlas: log-det-concavity (partial) -/
theorem log_det_smul_add_eq_iff {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.log (a • A + b • B).det = a * Real.log A.det + b * Real.log B.det ↔ A = B := by
  constructor
  · intro heq
    by_contra hne
    have h := strictConcaveOn_log_det.2 hA hB hne ha hb hab
    change a * Real.log A.det + b * Real.log B.det < Real.log (a • A + b • B).det at h
    linarith
  · rintro rfl
    rw [← add_smul, hab, one_smul, ← add_mul, hab, one_mul]

/-- The multiplicative determinant Jensen inequality, with real powers and
its exact interior equality case. Horn--Johnson (2013), Theorem 7.6.6.
atlas: log-det-concavity (partial) -/
theorem det_smul_add_ge_rpow_mul_and_eq_iff {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) :
    A.det ^ a * B.det ^ b ≤ (a • A + b • B).det ∧
      ((a • A + b • B).det = A.det ^ a * B.det ^ b ↔ A = B) := by
  have hC : (a • A + b • B).PosDef := convex_setOf_posDef hA hB ha.le hb.le hab
  have hlog : Real.log (A.det ^ a * B.det ^ b) = a * Real.log A.det + b * Real.log B.det := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hA.det_pos a).ne'
      (Real.rpow_pos_of_pos hB.det_pos b).ne', Real.log_rpow hA.det_pos, Real.log_rpow hB.det_pos]
  have hprod : 0 < A.det ^ a * B.det ^ b := mul_pos
    (Real.rpow_pos_of_pos hA.det_pos a) (Real.rpow_pos_of_pos hB.det_pos b)
  constructor
  · apply (Real.log_le_log_iff hprod hC.det_pos).mp
    rw [hlog]
    exact log_det_smul_add_ge hA hB ha.le hb.le hab
  · rw [← Real.log_injOn_pos.eq_iff hC.det_pos hprod, hlog]
    exact log_det_smul_add_eq_iff hA hB ha hb hab

end NLAlib
