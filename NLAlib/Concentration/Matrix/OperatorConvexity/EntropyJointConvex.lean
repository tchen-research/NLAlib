import NLAlib.Concentration.Matrix.OperatorConvexity.JointTensorRepresentation
import NLAlib.Concentration.Matrix.OperatorConvexity.PerspectiveConvex
import NLAlib.Concentration.Matrix.OperatorConvexity.LogOperatorConcave
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Theorem 8.1.4 — Joint convexity of matrix relative entropy

Main declaration: `NLAlib.convexOn_relativeEntropy`.

Atlas: `operator-monotone-convex`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 8.1.4 and Section 8.8, printed pp. 120, 137–138.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open NLAlib Matrix
set_option autoImplicit false

private lemma left_pos {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (h : A.PosDef) :
    (jointTensorLeft A).PosDef :=
  (h.kronecker Matrix.PosDef.one).submatrix finProdFinEquiv.symm.injective
private lemma right_pos {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (h : A.PosDef) :
    (jointTensorRight A).PosDef :=
  (Matrix.PosDef.one.kronecker h.transpose).submatrix finProdFinEquiv.symm.injective

private lemma left_combo {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (a b : ℝ) :
    jointTensorLeft (a • A + b • B) = a • jointTensorLeft A + b • jointTensorLeft B := by
  ext i j
  simp [jointTensorLeft, Matrix.kroneckerMap, add_mul]
  ring
private lemma right_combo {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (a b : ℝ) :
    jointTensorRight (a • A + b • B) = a • jointTensorRight A + b • jointTensorRight B := by
  ext i j
  simp [jointTensorRight, Matrix.kroneckerMap, mul_add]
  ring
private lemma eval_combo {d : ℕ} (A B : Matrix (Fin (d*d)) (Fin (d*d)) ℂ) (a b : ℝ) :
    jointTensorEval (a • A + b • B) = a * jointTensorEval A + b * jointTensorEval B := by
  simp [jointTensorEval, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul]
private lemma eval_mono {d : ℕ} (A B : Matrix (Fin (d*d)) (Fin (d*d)) ℂ)
    (h : LoewnerLE A B) : jointTensorEval A ≤ jointTensorEval B := by
  have hp := h.dotProduct_mulVec_nonneg jointTensorVec
  have hr := (Complex.nonneg_iff.mp hp).1
  simpa [jointTensorEval, Matrix.sub_mulVec, dotProduct_sub] using hr

private lemma pd_combo {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : (a • A + b • B).PosDef := by
  exact (CFC.concaveOn_log.1 hA.isStrictlyPositive hB.isStrictlyPositive ha hb hab).posDef

/-- Matrix relative entropy is jointly convex on pairs of positive definite matrices.

Tropp 2015, Thm 8.1.4. Atlas: `operator-monotone-convex`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 8*. -/
theorem NLAlib.convexOn_relativeEntropy {d : ℕ} [NeZero d] :
    ConvexOn ℝ {P : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ |
      P.1.PosDef ∧ P.2.PosDef} (fun P => relativeEntropy P.1 P.2) := by
  constructor
  · intro P hP Q hQ a b ha hb hab
    exact ⟨pd_combo _ _ hP.1 hQ.1 a b ha hb hab, pd_combo _ _ hP.2 hQ.2 a b ha hb hab⟩
  · intro P hP Q hQ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    have ha1 : a ≤ 1 := by linarith
    have hpers := matrixPerspective_jointly_operatorConvex (fun x => -Real.log x)
      operatorConvexOn_neg_log (jointTensorLeft P.1) (jointTensorLeft Q.1)
      (jointTensorRight P.2) (jointTensorRight Q.2)
      (left_pos _ hP.1) (left_pos _ hQ.1) (right_pos _ hP.2) (right_pos _ hQ.2)
      a ha ha1
    rw [← hb', ← left_combo, ← right_combo] at hpers
    have he := eval_mono _ _ hpers
    rw [eval_combo] at he
    change relativeEntropy (a • P.1 + b • Q.1) (a • P.2 + b • Q.2) ≤
      a * relativeEntropy P.1 P.2 + b * relativeEntropy Q.1 Q.2
    rw [relativeEntropy_eq_jointTensorEval_sub_trace _ _ (pd_combo _ _ hP.1 hQ.1 a b ha hb hab)
      (pd_combo _ _ hP.2 hQ.2 a b ha hb hab),
      relativeEntropy_eq_jointTensorEval_sub_trace _ _ hP.1 hP.2,
      relativeEntropy_eq_jointTensorEval_sub_trace _ _ hQ.1 hQ.2]
    have ht : (Matrix.trace (a • P.1 + b • Q.1 - (a • P.2 + b • Q.2))).re =
        a * (Matrix.trace (P.1 - P.2)).re + b * (Matrix.trace (Q.1 - Q.2)).re := by
      simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.mul_re]
      ring
    rw [ht]
    nlinarith
