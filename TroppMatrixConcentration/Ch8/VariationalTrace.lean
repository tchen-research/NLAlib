import TroppMatrixConcentration.Ch8.EntropyNonnegative
import Mathlib.Tactic.Linarith

/-!
# Lemma 8.1.6 — Attained variational formula for trace

Lean name: `TroppMatrixConcentration.ch8_variational_trace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 8.1.6 and its attainment observation, printed p. 121.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem TroppMatrixConcentration.ch8_variational_trace {d : ℕ} [NeZero d]
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * matrixLog M - T * matrixLog T + T)).re}
      (Matrix.trace M).re := by
  constructor
  · exact ⟨M, hM, by simp⟩
  · rintro r ⟨T, hT, rfl⟩
    have h := ch8_entropy_nonnegative T M hT hM
    simp only [ch8_relativeEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re] at h
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
    linarith
