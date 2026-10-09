import NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTrace
import NLAlib.Concentration.Matrix.Laplace.CgfExpLog
import Mathlib.Tactic.Ring

/-!
# Equation 8.1.2 — Variational trace exponential

Main declaration: `NLAlib.isGreatest_variational_traceExp`.

Atlas: `operator-monotone-convex` (step of Lieb's theorem).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Equation (8.1.2), together with the attainment in Lemma 8.1.6, printed p. 121.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open NLAlib
set_option autoImplicit false

/-- Variational formula for the trace exponential: `traceExp (H + log A)` is the greatest value of `tr
(T H) + tr A - D(T; A)` over positive definite `T`.

Tropp 2015, eq. (8.1.2) with Lemma 8.1.6. Atlas: `operator-monotone-convex`. Ported from the
Prove2me mission *An Introduction to Matrix Concentration Inequalities, Ch 8*.

The positive-definiteness hypothesis on `A` is not used by the proof; it is kept to match the
source. -/
theorem NLAlib.isGreatest_variational_traceExp {d : ℕ} [NeZero d]
    (H A : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (_hA : A.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * H)).re + (Matrix.trace A).re -
        relativeEntropy T A}
      (traceExp (H + matrixLog A)) := by
  have hHerm : (H + matrixLog A).IsHermitian := hH.add (cfc_predicate Real.log A)
  obtain ⟨hPD, hLog⟩ := posDef_matrixExp_and_matrixLog_matrixExp (H + matrixLog A) hHerm
  have hVar := isGreatest_variational_trace (matrixExp (H + matrixLog A)) hPD
  have score (T : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (T * matrixLog (matrixExp (H + matrixLog A)) - T * matrixLog T + T)).re =
        (Matrix.trace (T * H)).re + (Matrix.trace A).re - relativeEntropy T A := by
    rw [hLog]
    simp only [relativeEntropy, mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re]
    ring
  constructor
  · obtain ⟨T,hT,hEq⟩ := hVar.1
    exact ⟨T,hT,hEq.trans (score T)⟩
  · rintro r ⟨T,hT,rfl⟩
    rw [← score T]
    exact hVar.2 ⟨T,hT,rfl⟩
