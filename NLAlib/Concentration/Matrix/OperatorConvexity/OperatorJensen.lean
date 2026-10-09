import NLAlib.Concentration.Matrix.OperatorConvexity.JensenIsometricCompression
import NLAlib.Concentration.Matrix.OperatorConvexity.JensenBlockCalculus
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Theorem 8.5.2 — Operator Jensen inequality

Main declaration: `NLAlib.operator_jensen`.

Atlas: `operator-monotone-convex`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 8.5.2 and Chapter 8 dimension conventions, printed pp. 120, 132–133.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder

open NLAlib

/-- Operator Jensen inequality: for `f` operator convex on `I` and `K₁ᴴ K₁ + K₂ᴴ K₂ = 1`, `f (K₁ᴴ A₁
K₁ + K₂ᴴ A₂ K₂) ≼ K₁ᴴ f(A₁) K₁ + K₂ᴴ f(A₂) K₂`.

Tropp 2015, Thm 8.5.2. Atlas: `operator-monotone-convex`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 8*. -/
theorem NLAlib.operator_jensen {d m n : ℕ} [NeZero d] [NeZero m] [NeZero n]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : OperatorConvexOn I f)
    (A₁ : Matrix (Fin m) (Fin m) ℂ) (A₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.IsHermitian) (hA₂ : A₂.IsHermitian)
    (hA₁I : spectrum ℝ A₁ ⊆ I) (hA₂I : spectrum ℝ A₂ ⊆ I)
    (K₁ : Matrix (Fin m) (Fin d) ℂ) (K₂ : Matrix (Fin n) (Fin d) ℂ)
    (hK : K₁.conjTranspose * K₁ + K₂.conjTranspose * K₂ = 1) :
    LoewnerLE
      (matrixFunction f (K₁.conjTranspose * A₁ * K₁ + K₂.conjTranspose * A₂ * K₂))
      (K₁.conjTranspose * matrixFunction f A₁ * K₁ +
        K₂.conjTranspose * matrixFunction f A₂ * K₂) := by
  obtain ⟨hAB, hspec, hcalc⟩ := matrixFunction_fromBlocks A₁ A₂ hA₁ hA₂ f
  have hdomain : spectrum ℝ (Matrix.fromBlocks A₁ 0 0 A₂) ⊆ I := by
    rw [hspec]
    exact Set.union_subset hA₁I hA₂I
  have hisometry : (Matrix.fromRows K₁ K₂).conjTranspose * Matrix.fromRows K₁ K₂ = 1 := by
    simpa only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows] using hK
  have h := OperatorConvexOn.matrixFunction_conjTranspose_mul_mul_le I f hf
    (Matrix.fromBlocks A₁ 0 0 A₂) hAB hdomain (Matrix.fromRows K₁ K₂) hisometry
  simpa only [hcalc, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromCols_mul_fromRows] using h


