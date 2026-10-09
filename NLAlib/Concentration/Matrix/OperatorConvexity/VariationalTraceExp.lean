import NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTrace
import NLAlib.Concentration.Matrix.Laplace.CgfExpLog
import Mathlib.Tactic.Ring

/-!
# Equation 8.1.2 — Variational trace exponential

Lean name: `NLAlib.ch8_variational_trace_exp`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Equation (8.1.2), together with the attainment in Lemma 8.1.6, printed p. 121.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open NLAlib
set_option autoImplicit false

theorem NLAlib.ch8_variational_trace_exp {d : ℕ} [NeZero d]
    (H A : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (hA : A.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * H)).re + (Matrix.trace A).re -
        ch8_relativeEntropy T A}
      (traceExp (H + matrixLog A)) := by
  have hHerm : (H + matrixLog A).IsHermitian := hH.add (cfc_predicate Real.log A)
  obtain ⟨hPD, hLog⟩ := ch3_cgf_exp_log (H + matrixLog A) hHerm
  have hVar := ch8_variational_trace (matrixExp (H + matrixLog A)) hPD
  have score (T : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (T * matrixLog (matrixExp (H + matrixLog A)) - T * matrixLog T + T)).re =
        (Matrix.trace (T * H)).re + (Matrix.trace A).re - ch8_relativeEntropy T A := by
    rw [hLog]
    simp only [ch8_relativeEntropy, mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re]
    ring
  constructor
  · obtain ⟨T,hT,hEq⟩ := hVar.1
    exact ⟨T,hT,hEq.trans (score T)⟩
  · rintro r ⟨T,hT,rfl⟩
    rw [← score T]
    exact hVar.2 ⟨T,hT,rfl⟩
