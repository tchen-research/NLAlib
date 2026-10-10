import NLAlib.Matrix.Norms
import Mathlib.Data.Matrix.Basis

/-!
# Trace contractions for coordinate Gram derivatives

These finite matrix identities contract first and second Gram directions
without differentiating eigenvectors. They support the explicit resolvent
Laplacian formula in the operator smallest-eigenvalue proof.

Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A coordinate Gram derivative pairs with a symmetric matrix as twice
the corresponding matrix product entry. Source: trace cyclicity; atlas
`wishart-lambda-min-tail` (helper). -/
theorem trace_mul_gram_direction (X : Matrix ι ι ℝ) (hX : Xᵀ = X)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    Matrix.trace (X * (E * Gᵀ + G * Eᵀ)) = 2 * (X * G) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hGX : Gᵀ * X = (X * G)ᵀ := by rw [Matrix.transpose_mul, hX]
  have h1 : Matrix.trace (X * (E * Gᵀ)) = (X * G) i j := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [E, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul,
      one_mul, hGX, Matrix.transpose_apply]
  have h2 : Matrix.trace (X * (G * Eᵀ)) = (X * G) i j := by
    rw [← Matrix.mul_assoc]
    simp only [E, Matrix.transpose_single, Matrix.trace_mul_single,
      op_smul_eq_smul, smul_eq_mul, one_mul]
  change Matrix.trace (X * (E * Gᵀ + G * Eᵀ)) = _
  rw [mul_add, Matrix.trace_add, h1, h2]
  ring

/-- The squared coordinate trace pairings sum to a single Gram trace.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper). -/
theorem sum_trace_mul_gram_direction_sq (X : Matrix ι ι ℝ) (hX : Xᵀ = X)
    (G : Matrix ι κ ℝ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      Matrix.trace (X * (E * Gᵀ + G * Eᵀ)) ^ 2) =
      4 * Matrix.trace (X ^ 2 * (G * Gᵀ)) := by
  simp_rw [trace_mul_gram_direction X hX G, mul_pow]
  norm_num only
  have hfrob : frobInner (X * G) (X * G) = Matrix.trace (X ^ 2 * (G * Gᵀ)) := by
    rw [frobInner_eq_trace, Matrix.transpose_mul, hX, pow_two]
    calc Matrix.trace ((Gᵀ * X) * (X * G)) = Matrix.trace (Gᵀ * (X * X * G)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * X * G) * Gᵀ) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; simp only [Matrix.mul_assoc]
  rw [← hfrob]
  simp only [frobInner, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The trace contraction of two coordinate Gram directions has three
explicit terms. Source: operator Gram chain rule and single-matrix algebra;
atlas `wishart-lambda-min-tail` (helper). -/
theorem trace_mul_gram_direction_mul_gram_direction (X Y : Matrix ι ι ℝ)
    (hX : Xᵀ = X) (hY : Yᵀ = Y) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    Matrix.trace (X * (E * Gᵀ + G * Eᵀ) * Y * (E * Gᵀ + G * Eᵀ)) =
      2 * (X * G) i j * (Y * G) i j + X i i * (Gᵀ * Y * G) j j +
        Y i i * (Gᵀ * X * G) j j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hGX : Gᵀ * X = (X * G)ᵀ := by rw [Matrix.transpose_mul, hX]
  have hGY : Gᵀ * Y = (Y * G)ᵀ := by rw [Matrix.transpose_mul, hY]
  have h1 : Matrix.trace (X * (E * Gᵀ) * Y * (E * Gᵀ)) =
      (X * G) i j * (Y * G) i j := by
    calc _ = Matrix.trace (X * (E * (Gᵀ * Y) * E * Gᵀ)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((E * (Gᵀ * Y) * E * Gᵀ) * X) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((E * (Gᵀ * Y) * E) * (Gᵀ * X)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.single_mul_mul_single, one_mul, mul_one,
            Matrix.trace_single_mul, smul_eq_mul, hGX, hGY, Matrix.transpose_apply]
          ring
  have h2 : Matrix.trace (X * (E * Gᵀ) * Y * (G * Eᵀ)) =
      X i i * (Gᵀ * Y * G) j j := by
    calc _ = Matrix.trace (X * (E * (Gᵀ * Y * G) * Eᵀ)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.transpose_single, Matrix.single_mul_mul_single,
            one_mul, mul_one, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul]
          ring
  have h3 : Matrix.trace (X * (G * Eᵀ) * Y * (E * Gᵀ)) =
      Y i i * (Gᵀ * X * G) j j := by
    calc _ = Matrix.trace ((X * G * Eᵀ * Y * E) * Gᵀ) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Gᵀ * (X * G * Eᵀ * Y * E)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Gᵀ * X * G) * (Eᵀ * Y * E)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.transpose_single, Matrix.single_mul_mul_single,
            one_mul, mul_one, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul]
  have h4 : Matrix.trace (X * (G * Eᵀ) * Y * (G * Eᵀ)) =
      (X * G) i j * (Y * G) i j := by
    calc _ = Matrix.trace ((X * G) * (Eᵀ * (Y * G) * Eᵀ)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.transpose_single, Matrix.single_mul_mul_single,
            one_mul, mul_one, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul]
          ring
  change Matrix.trace (X * (E * Gᵀ + G * Eᵀ) * Y * (E * Gᵀ + G * Eᵀ)) = _
  simp only [mul_add, add_mul, Matrix.trace_add]
  rw [h1, h2, h3, h4]
  ring

/-- Summing all coordinate Gram directions contracts the trace Hessian
to three trace products. Source: operator Gram chain rule; atlas
`wishart-lambda-min-tail` (helper). -/
theorem sum_trace_mul_gram_direction_mul_gram_direction (X Y : Matrix ι ι ℝ)
    (hX : Xᵀ = X) (hY : Yᵀ = Y) (G : Matrix ι κ ℝ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      Matrix.trace (X * (E * Gᵀ + G * Eᵀ) * Y * (E * Gᵀ + G * Eᵀ))) =
      2 * Matrix.trace (X * Y * (G * Gᵀ)) +
        Matrix.trace X * Matrix.trace (Y * (G * Gᵀ)) +
        Matrix.trace Y * Matrix.trace (X * (G * Gᵀ)) := by
  simp_rw [trace_mul_gram_direction_mul_gram_direction X Y hX hY G]
  have hfrob : frobInner (X * G) (Y * G) = Matrix.trace (X * Y * (G * Gᵀ)) := by
    rw [frobInner_eq_trace, Matrix.transpose_mul, hX]
    calc Matrix.trace ((Gᵀ * X) * (Y * G)) = Matrix.trace (Gᵀ * (X * Y * G)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * Y * G) * Gᵀ) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; simp only [Matrix.mul_assoc]
  have htraceX : Matrix.trace (Gᵀ * X * G) = Matrix.trace (X * (G * Gᵀ)) := by
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_comm (G * Gᵀ) X]
    simp only [Matrix.mul_assoc]
  have htraceY : Matrix.trace (Gᵀ * Y * G) = Matrix.trace (Y * (G * Gᵀ)) := by
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_comm (G * Gᵀ) Y]
    simp only [Matrix.mul_assoc]
  rw [← hfrob, ← htraceX, ← htraceY]
  simp only [frobInner, Matrix.trace, Matrix.diag, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
  all_goals rw [Finset.sum_comm]

end NLAlib
