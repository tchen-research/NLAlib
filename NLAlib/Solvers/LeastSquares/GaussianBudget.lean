/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.LeastSquares.GaussianMoments

/-!
# Gaussian sketch-and-solve with an explicit sample budget

Markov's inequality is applied to the excess above the optimal residual, whose expectation
is known exactly. This gives a `1 + ε` squared-residual guarantee with failure probability
at most `δ` using `rank A + 2 + ceil (rank A / (δ ε))` rows. At fixed confidence the budget
is `O((rank A + 1) / ε)`. Exact-fit and zero-rank inputs are included.

Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16, for the regression guarantee.
The proof here is a direct consequence of the exact Gaussian residual moment of
Epperly–Webber 2026, Theorem 2.1, rather than a subspace-embedding budget.
Atlas: `sketch-and-solve-ls`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- A sufficient Gaussian row budget for squared relative residual `1 + ε` and failure
probability `δ`. The guarantee assumes `ε > 0` and `δ > 0`.
Source: the exact Gaussian residual moment and Markov's inequality. -/
def gaussianSketchSolveDim (r : ℕ) (ε δ : ℝ) : ℕ := r + 2 + ⌈(r : ℝ) / (δ * ε)⌉₊

private theorem frobSq_optimalResidual_le {m n : ℕ} {p : Type*} [Fintype p]
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) p ℝ)
    (X : Matrix (Fin n) p ℝ) :
    frobSq ((1 - A * moorePenroseInverse A) * B) ≤ frobSq (B - A * X) := by
  obtain ⟨Q, hQ, hQA⟩ := exists_orthonormal_frame_reproducing_matrix A
  have hproj : Q * Qᵀ = A * moorePenroseInverse A :=
    mul_conjTranspose_eq_mul_moorePenroseInverse hQ hQA (by simp)
  have hres : projResidual Q B = (1 - A * moorePenroseInverse A) * B := by
    rw [residual_eq_one_sub_mul, Matrix.conjTranspose_eq_transpose_of_trivial, hproj]
  have h := frobSq_residual_le_frobSq_sub_mul hQ B ((Qᵀ * A) * X)
  rwa [hres, ← Matrix.mul_assoc, hQA] at h

/-- The actual Gaussian sketch-and-solve estimator has squared relative residual `1 + ε`
except on an event of probability at most `δ`, under the explicit real-valued sample budget.
This uses the exact moment of the nonnegative excess; no embedding or moment assumption is
left to the caller. The case of an exactly solvable problem is included.
Source: Sarlós 2006, Theorem 12; Epperly–Webber 2026, Theorem 2.1 and Markov's inequality.
atlas: sketch-and-solve-ls (partial) -/
theorem measureReal_frobSq_sub_mul_sketchAndSolve_gt_le_of_hasLaw_gaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) p ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hs : A.rank + 2 ≤ s)
    (hbudget : (A.rank : ℝ) ≤ δ * ε * ((s : ℝ) - A.rank - 1)) :
    μ.real {ω | (1 + ε) * frobSq ((1 - A * moorePenroseInverse A) * B) <
      frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B)} ≤ δ := by
  let : IsProbabilityMeasure μ := hΨ.isProbabilityMeasure
  let c := frobSq ((1 - A * moorePenroseInverse A) * B)
  let f := fun ω => frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B)
  obtain ⟨hi, he⟩ :=
    integrable_and_integral_frobSq_sub_mul_sketchAndSolve_of_hasLaw_gaussianMatrix hΨ A B hs
  have hc : 0 ≤ c := frobSq_nonneg _
  have hf : ∀ ω, c ≤ f ω := fun ω => frobSq_optimalResidual_le A B _
  have hi' : Integrable (fun ω => f ω - c) μ := hi.sub (integrable_const _)
  have he' : ∫ ω, f ω - c ∂μ = (A.rank : ℝ) / ((s : ℝ) - A.rank - 1) * c := by
    rw [integral_sub hi (integrable_const _), he, integral_const, probReal_univ, one_smul]
    dsimp [c]
    ring
  have hden : 0 < (s : ℝ) - A.rank - 1 := by
    have hs' : (A.rank : ℝ) + 2 ≤ s := by exact_mod_cast hs
    linarith
  have hratio : (A.rank : ℝ) / ((s : ℝ) - A.rank - 1) ≤ δ * ε :=
    (div_le_iff₀ hden).2 hbudget
  by_cases hc0 : c = 0
  · have hae : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg
      (fun ω => frobSq_nonneg _) hi).1 (by
        change ∫ ω, f ω ∂μ = 0
        rw [he, show frobSq ((1 - A * moorePenroseInverse A) * B) = 0 from hc0, mul_zero])
    have hnull : μ {ω | (1 + ε) * c < f ω} = 0 := by
      apply measure_mono_null (t := {ω | f ω ≠ 0}) _ (ae_iff.mp hae)
      intro ω hω
      dsimp at hω ⊢
      rw [hc0, mul_zero] at hω
      exact ne_of_gt hω
    change μ.real {ω | (1 + ε) * c < f ω} ≤ δ
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact hδ.le
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => sub_nonneg.mpr (hf ω)) hi' (ε * c)
    rw [he'] at hm
    have hsub : {ω | (1 + ε) * c < f ω} ⊆ {ω | ε * c ≤ f ω - c} := by
      intro ω hω
      dsimp at hω ⊢
      linarith
    change μ.real {ω | (1 + ε) * c < f ω} ≤ δ
    apply (measureReal_mono hsub).trans
    apply (le_of_mul_le_mul_left _ (mul_pos hε hcpos))
    calc
      ε * c * μ.real {ω | ε * c ≤ f ω - c} ≤
          (A.rank : ℝ) / ((s : ℝ) - A.rank - 1) * c := hm
      _ ≤ δ * ε * c := mul_le_mul_of_nonneg_right hratio hc
      _ = ε * c * δ := by ring

/-- **Gaussian sketch-and-solve with an explicit integer budget.** The number of sketch rows
`rank A + 2 + ceil (rank A / (δ ε))` suffices for squared relative residual `1 + ε` with
failure probability at most `δ`. At fixed confidence this is `O((rank A + 1) / ε)` rows.
The estimator is the actual Moore–Penrose solution, and its law is a standard Gaussian
matrix. No full-rank or nonzero optimal-residual hypothesis is needed.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16 (sample order), via the exact
Gaussian residual moment of Epperly–Webber 2026, Theorem 2.1.
atlas: sketch-and-solve-ls (partial) -/
theorem measureReal_frobSq_sub_mul_sketchAndSolve_gt_le_of_gaussianSketchSolveDim_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) p ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : gaussianSketchSolveDim A.rank ε δ ≤ s) :
    μ.real {ω | (1 + ε) * frobSq ((1 - A * moorePenroseInverse A) * B) <
      frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B)} ≤ δ := by
  have hs' : A.rank + 2 + ⌈(A.rank : ℝ) / (δ * ε)⌉₊ ≤ s := hs
  apply measureReal_frobSq_sub_mul_sketchAndSolve_gt_le_of_hasLaw_gaussianMatrix
    hΨ A B hε hδ (by omega)
  have hceil := Nat.le_ceil ((A.rank : ℝ) / (δ * ε))
  have hsreal : (A.rank : ℝ) + 2 + (⌈(A.rank : ℝ) / (δ * ε)⌉₊ : ℝ) ≤ s := by
    exact_mod_cast hs'
  have hratio : (A.rank : ℝ) / (δ * ε) ≤ (s : ℝ) - A.rank - 1 := by linarith
  have h := (div_le_iff₀ (mul_pos hδ hε)).1 hratio
  simpa only [mul_comm] using h

/-- The same Gaussian row budget gives the usual unsquared Frobenius-residual factor
`1 + ε`. This follows from the stronger squared-residual theorem.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16.
atlas: sketch-and-solve-ls (partial) -/
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_gt_le_of_gaussianSketchSolveDim_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) p ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : gaussianSketchSolveDim A.rank ε δ ≤ s) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - A * moorePenroseInverse A) * B) <
      frobNorm (B - A * sketchAndSolve A (Ψ ω)ᵀ B)} ≤ δ := by
  let : IsProbabilityMeasure μ := hΨ.isProbabilityMeasure
  apply (measureReal_mono (s₂ := {ω | (1 + ε) *
    frobSq ((1 - A * moorePenroseInverse A) * B) <
      frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B)}) ?_).trans
    (measureReal_frobSq_sub_mul_sketchAndSolve_gt_le_of_gaussianSketchSolveDim_le
      hΨ A B hε hδ hs)
  intro ω hω
  dsimp at hω ⊢
  rw [← frobNorm_sq, ← frobNorm_sq]
  have hc := frobNorm_nonneg ((1 - A * moorePenroseInverse A) * B)
  have hf := frobNorm_nonneg (B - A * sketchAndSolve A (Ψ ω)ᵀ B)
  have hsq := mul_self_lt_mul_self (mul_nonneg (by linarith : 0 ≤ 1 + ε) hc) hω
  have hextra : 0 ≤ ε * (1 + ε) * frobNorm ((1 - A * moorePenroseInverse A) * B) ^ 2 := by
    positivity
  nlinarith

end NLAlib
