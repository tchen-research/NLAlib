import NLAlib.Concentration.Matrix.OperatorConvexity.GeneralizedKlein
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Proposition 8.1.3 — Matrix relative entropy is nonnegative

Lean name: `NLAlib.ch8_entropy_nonnegative`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.1.3 and Section 8.3.5, printed pp. 120 and 126.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open NLAlib
set_option autoImplicit false

theorem NLAlib.ch8_entropy_nonnegative {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef) :
    0 ≤ ch8_relativeEntropy A H := by
  let f : Fin 3 → ℝ → ℝ := ![fun a => a * Real.log a - a, fun a => -a, fun _ => 1]
  let g : Fin 3 → ℝ → ℝ := ![fun _ => 1, Real.log, id]
  have hp (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosDef) :
      spectrum ℝ M ⊆ Set.Ioi 0 := by
    rw [hM.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hM.eigenvalues_pos i
  have hf : ∀ a ∈ Set.Ioi (0 : ℝ), ∀ h ∈ Set.Ioi (0 : ℝ),
      0 ≤ ∑ i, f i a * g i h := by
    intro a ha h hh
    change 0 < a at ha
    change 0 < h at hh
    have hlog := Real.log_le_sub_one_of_pos (div_pos hh ha)
    rw [Real.log_div (ne_of_gt hh) (ne_of_gt ha)] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
    have hd : a * (h / a - 1) = h - a := by field_simp [ne_of_gt ha]
    rw [hd] at hm
    simp [f, g, Fin.sum_univ_succ]
    nlinarith
  have hk := ch8_generalized_klein (Set.Ioi 0) (convex_Ioi 0) f g hf A H hA.1 hH.1
    (hp A hA) (hp H hH)
  have hc (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian) (q : ℝ → ℝ) :
      ContinuousOn q (spectrum ℝ M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  simp only [Fin.sum_univ_succ, f, g, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, ch8_matrixFunction] at hk
  simp only [cfc_sub _ _ A (hc A hA.1 _) (hc A hA.1 _),
    cfc_mul _ _ A (hc A hA.1 _) (hc A hA.1 _), cfc_neg (fun x : ℝ => x) A,
    cfc_id ℝ A hA.1.isSelfAdjoint, cfc_id' ℝ A hA.1.isSelfAdjoint, cfc_id ℝ H hH.1.isSelfAdjoint,
    cfc_const (1 : ℝ) A hA.1.isSelfAdjoint, cfc_const (1 : ℝ) H hH.1.isSelfAdjoint, map_one, mul_one, one_mul,
    neg_mul, Finset.sum_empty, add_zero] at hk
  simpa [ch8_relativeEntropy, matrixLog, mul_sub, mul_add, mul_neg, Matrix.trace_sub,
    Matrix.trace_neg, Matrix.trace_add, Complex.add_re, Complex.sub_re, Complex.neg_re, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hk
