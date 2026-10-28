/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.LeastSquares.SketchAndSolve
import NLAlib.LowRank.Nystrom.RawNystromBridge
import NLAlib.LowRank.RandomizedSVD.GaussianSketch
import NLAlib.RandomMatrix.Gaussian.Spectral.SketchRank
import NLAlib.Matrix.Basic.MoorePenroseProjector
import NLAlib.Matrix.Basic.GramVanishing

/-!
# Gaussian sketch-and-solve moments

The exact residual expectation for the actual minimum-norm estimator, at arbitrary input
rank, follows from the Gaussian completion identity after choosing a fixed frame for the
column space. Every random-matrix assumption is an actual `HasLaw` statement. Integrability
is proved together with the expectation; zero-rank inputs are included.

Source: Epperly–Webber 2026, Theorem 2.1 (real Gaussian case, attributed there to Bartan and
Pilanci); the block-moment calculation is the Gaussian completion lemma of Chen–Persson and
Tropp–Webber 2023, Section 5. Atlas: `gaussian-haar-sketch-solve-exact` (partial).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The fitted values of sketch-and-solve are the raw generalized Nyström formula, with the
design matrix as its first factor. This is an algebraic identity at every rank. -/
theorem mul_sketchAndSolve_eq_rawGeneralizedNystrom
    {m n p s : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype s]
    (A : Matrix m n ℝ) (Ψ : Matrix m s ℝ) (B : Matrix m p ℝ) :
    A * sketchAndSolve A Ψᵀ B = rawGeneralizedNystrom B A Ψ := by
  simp only [sketchAndSolve, rawGeneralizedNystrom, Matrix.mul_assoc]

/-- **Exact real Gaussian residual moment**, including integrability and zero-rank inputs.
For `s ≥ rank A + 2`, the expected squared Frobenius residual of the minimum-norm sketched
solution is `1 + rank A / (s - rank A - 1)` times the optimal squared residual.
The sketch has independent standard real Gaussian entries, expressed by its actual law.
Source: Epperly–Webber 2026, Theorem 2.1, real Gaussian case.
Helper for the Gaussian sketch-and-solve budget.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_sub_mul_sketchAndSolve_of_hasLaw_gaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) p ℝ)
    (hs : A.rank + 2 ≤ s) :
    Integrable (fun ω => frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B)) μ ∧
      ∫ ω, frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B) ∂μ =
        (1 + (A.rank : ℝ) / ((s : ℝ) - A.rank - 1)) *
          frobSq ((1 - A * moorePenroseInverse A) * B) := by
  let : IsProbabilityMeasure μ := hΨ.isProbabilityMeasure
  by_cases hr : A.rank = 0
  · have hA : A = 0 := eq_zero_of_matrix_rank_eq_zero hr
    subst A
    simp
  obtain ⟨Q, hQ, hQA⟩ := exists_orthonormal_frame_reproducing_matrix A
  obtain ⟨Qp, hQp, hcomp⟩ := exists_unitary_complement Q hQ
  have hcomp' : Q * Qᵀ + Qp * Qpᵀ = 1 := by simpa using hcomp
  have hproj : Q * Qᵀ = A * moorePenroseInverse A :=
    mul_conjTranspose_eq_mul_moorePenroseInverse hQ hQA (by simp)
  have hres : projResidual Q B = (1 - A * moorePenroseInverse A) * B := by
    rw [residual_eq_one_sub_mul, Matrix.conjTranspose_eq_transpose_of_trivial, hproj]
  obtain ⟨hi, he⟩ := completion_reduction_gaussian_integrable Q Qp B hQ hQp hcomp'
    (by omega) hs Ψ hΨ
  have hfull : ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᵀ * Q)ᵀ * ((Ψ ω)ᵀ * Q)) := by
    filter_upwards [ae_isUnit_block hΨ Q hQ (by omega)] with ω hω
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hω
  have heq : (fun ω => frobSq (B - A * sketchAndSolve A (Ψ ω)ᵀ B)) =ᵐ[μ]
      fun ω => frobSq (B - sketchedOutput Q (Ψ ω) B) := by
    filter_upwards [hfull] with ω hω
    rw [mul_sketchAndSolve_eq_rawGeneralizedNystrom,
      rawGeneralizedNystrom_eq_sketchedOutput B A Q (Ψ ω) hQA (by simp) hω]
  refine ⟨hi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, he, hres]

end NLAlib
