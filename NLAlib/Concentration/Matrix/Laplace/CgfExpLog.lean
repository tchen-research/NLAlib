import NLAlib.Concentration.Matrix.Defs.Spectral

/-!
# Hermitian exponential is positive definite and logarithm is its inverse

Lean name: `NLAlib.ch3_cgf_exp_log`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Sections 2.1.11–12, especially equation (2.1.17), printed pp. 22–23; used in Corollary 3.4.2, printed p. 35.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false
open NLAlib

theorem NLAlib.ch3_cgf_exp_log {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    (matrixExp A).PosDef ∧ matrixLog (matrixExp A) = A := by
  constructor
  · rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
    apply Matrix.IsStrictlyPositive.posDef
    exact (cfc_isStrictlyPositive_iff Real.exp A (by fun_prop) hA.isSelfAdjoint).mpr
      (fun x _ => Real.exp_pos x)
  · exact CFC.log_exp A hA.isSelfAdjoint
