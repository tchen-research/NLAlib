import NLAlib.Concentration.Matrix.OperatorConvexity.EntropyNonnegative
import NLAlib.Concentration.Matrix.Laplace.CgfExpLog
import Mathlib.Tactic.Linarith

/-!
# Example 8.3.4 — Trace exponential is monotone

Lean name: `NLAlib.ch8_trace_exp_monotone`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Example 8.3.4, printed p. 125.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix
private theorem trace_mul_nonneg {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  let S := CFC.sqrt A
  have hS : Sᴴ = S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hp := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : Matrix.trace (S * B * Sᴴ) = Matrix.trace (A * B) := by
    rw [hS, Matrix.trace_mul_cycle, hSS]
  rw [ht] at hp
  exact (RCLike.nonneg_iff.mp hp).1

open NLAlib
set_option autoImplicit false

theorem NLAlib.ch8_trace_exp_monotone {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAH : loewnerLE A H) :
    traceExp A ≤ traceExp H := by
  obtain ⟨hEA, hLA⟩ := ch3_cgf_exp_log A hA
  obtain ⟨hEH, hLH⟩ := ch3_cgf_exp_log H hH
  have he := ch8_entropy_nonnegative (matrixExp A) (matrixExp H) hEA hEH
  have hp := trace_mul_nonneg (matrixExp A) (H - A) hEA.posSemidef hAH
  simp only [ch8_relativeEntropy, hLA, hLH, mul_sub, Matrix.trace_sub,
    Complex.sub_re] at he hp
  unfold traceExp
  linarith
