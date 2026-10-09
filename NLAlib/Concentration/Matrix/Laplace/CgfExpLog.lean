import NLAlib.Concentration.Matrix.Defs.Spectral

/-!
# Hermitian exponential is positive definite and logarithm is its inverse

Main declaration: `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp`.

Atlas: `loewner-order` (matrix exponential and logarithm); supports `matrix-laplace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Sections 2.1.11–12, especially equation (2.1.17), printed pp. 22–23; used in Corollary 3.4.2, printed p. 35.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false
open NLAlib

/-- The exponential of a Hermitian matrix is positive definite and `matrixLog` inverts it: `(matrixExp
A).PosDef ∧ matrixLog (matrixExp A) = A`.

Tropp 2015, §2.1.11–12, eq. (2.1.17). Atlas: `loewner-order`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 3*. -/
theorem NLAlib.posDef_matrixExp_and_matrixLog_matrixExp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    (matrixExp A).PosDef ∧ matrixLog (matrixExp A) = A := by
  constructor
  · rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
    apply Matrix.IsStrictlyPositive.posDef
    exact (cfc_isStrictlyPositive_iff Real.exp A (by fun_prop) hA.isSelfAdjoint).mpr
      (fun x _ => Real.exp_pos x)
  · exact CFC.log_exp A hA.isSelfAdjoint
