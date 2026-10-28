/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.LeastSquares.GaussianMoments
import Mathlib.Probability.Independence.Integration
import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral

/-!
# Unbiased Gaussian sketch-and-solve

The independent off-range Gaussian block has mean zero, even after multiplication by the
pseudoinverse of the in-range block. This identifies the mean of the actual minimum-norm
sketched solution with the minimum-norm unsketched solution.

Source: Epperly–Webber 2026, Theorem 2.1 (real Gaussian case).
Atlas: `gaussian-haar-sketch-solve-exact` (partial).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem integrable_entry_of_integrable_frobSq
    {Ω a b : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Fintype a] [Fintype b] {X : Ω → Matrix a b ℝ}
    (hX : ∀ i j, AEStronglyMeasurable (fun ω => X ω i j) μ)
    (hi : Integrable (fun ω => frobSq (X ω)) μ) (i : a) (j : b) :
    Integrable (fun ω => X ω i j) μ := by
  classical
  refine ((integrable_const 1).add hi).mono' (hX i j) (Filter.Eventually.of_forall ?_)
  intro ω
  change ‖X ω i j‖ ≤ 1 + frobSq (X ω)
  have hsq : X ω i j ^ 2 ≤ frobSq (X ω) := by
    rw [frobSq_eq_sum_sq]
    exact (Finset.single_le_sum (fun k _ => sq_nonneg (X ω i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (X ω k l))
        (Finset.mem_univ i))
  rw [Real.norm_eq_abs]
  have habs := sq_abs (X ω i j)
  nlinarith [sq_nonneg (|X ω i j| - 1)]

private theorem integrable_and_integral_gaussian_cross_block_entry
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m s q r : ℕ}
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin r) ℝ)
    (hQ : HasOrthonormalCols Q) (hQp : HasOrthonormalCols Qp) (hQQp : Qᵀ * Qp = 0)
    (hqs : q + 2 ≤ s) (i : Fin r) (j : Fin q) :
    Integrable (fun ω => ((Qpᵀ * Ψ ω) * pinvR (Qᵀ * Ψ ω)) i j) μ ∧
      ∫ ω, ((Qpᵀ * Ψ ω) * pinvR (Qᵀ * Ψ ω)) i j ∂μ = 0 := by
  let : IsProbabilityMeasure μ := hΨ.isProbabilityMeasure
  have hX := (measurable_block Q).comp_aemeasurable hΨ.aemeasurable
  have hY := hasLaw_gaussianMatrix_block_of_hasLaw hΨ Qp hQp
  have hind := gaussianMatrix_indepFun_block_of_hasLaw hΨ Q Qp hQ hQp hQQp
  have hiP (t : Fin s) : Integrable (fun ω => pinvR (Qᵀ * Ψ ω) t j) μ :=
    integrable_entry_of_integrable_frobSq
      (fun a b => ((measurable_pinvR_entry a b).comp_aemeasurable hX).aestronglyMeasurable)
      (integrable_pinvR_block hΨ Q hQ hqs) t j
  have hiY (t : Fin s) : Integrable (fun ω => (Qpᵀ * Ψ ω) i t) μ := by
    have h := (memLp_gaussianMatrix_entry i t 1 (by simp)).integrable (by simp)
    rw [← hY.map_eq] at h
    exact h.comp_aemeasurable hY.aemeasurable
  have hiProd (t : Fin s) :
      Integrable (fun ω => (Qpᵀ * Ψ ω) i t * pinvR (Qᵀ * Ψ ω) t j) μ :=
    (hind.symm.comp (Matrix.measurable_entry i t) (measurable_pinvR_entry t j)).integrable_mul
      (hiY t) (hiP t)
  refine ⟨?_, ?_⟩
  · simpa only [Matrix.mul_apply] using integrable_finsetSum Finset.univ (fun t _ => hiProd t)
  · change (∫ ω, ∑ t, (Qpᵀ * Ψ ω) i t * pinvR (Qᵀ * Ψ ω) t j ∂μ) = 0
    rw [integral_finsetSum _ (fun t _ => hiProd t)]
    apply Finset.sum_eq_zero
    intro t _
    have hprod := IndepFun.integral_fun_mul_eq_mul_integral
      (hind.symm.comp (Matrix.measurable_entry i t) (measurable_pinvR_entry t j))
        (hiY t).aestronglyMeasurable
        (hiP t).aestronglyMeasurable
    simp only [Function.comp_apply] at hprod
    have hmean : ∫ ω, (Qpᵀ * Ψ ω) i t ∂μ = 0 := by
      have h := hY.integral_comp (Matrix.measurable_entry i t).aestronglyMeasurable
      simpa only [Function.comp_apply, integral_gaussianMatrix_entry_eq_zero] using h
    exact hprod.trans (by rw [hmean, zero_mul])

private theorem integrable_and_integral_sketchedCore_entry
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m s q r : ℕ}
    {p : Type*} [Fintype p]
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin r) ℝ)
    (hQ : HasOrthonormalCols Q) (hQp : HasOrthonormalCols Qp)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (hqs : q + 2 ≤ s)
    (B : Matrix (Fin m) p ℝ) (i : Fin q) (j : p) :
    Integrable (fun ω => sketchedCore Q (Ψ ω) B i j) μ ∧
      ∫ ω, sketchedCore Q (Ψ ω) B i j ∂μ = (Qᵀ * B) i j := by
  let : IsProbabilityMeasure μ := hΨ.isProbabilityMeasure
  have hQQp : Qᵀ * Qp = 0 := conjTranspose_mul_eq_zero_of_completion
    hQ.conjTranspose_mul_self hQp.conjTranspose_mul_self hcomp
  let D := Qpᵀ * projResidual Q B
  let C := fun ω => (Qpᵀ * Ψ ω) * pinvR (Qᵀ * Ψ ω)
  have hC (k : Fin r) := integrable_and_integral_gaussian_cross_block_entry
    hΨ Q Qp hQ hQp hQQp hqs k i
  have hnoise (ω : Ω) :
      (pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) * D) i j =
        ∑ k, C ω k i * D k j := by
    have heq : pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) = (C ω)ᵀ := by
      simp only [C, Matrix.transpose_mul, pinvR_transpose, Matrix.transpose_transpose]
    rw [heq]
    rfl
  have hni : Integrable (fun ω => ∑ k, C ω k i * D k j) μ :=
    integrable_finsetSum _ fun k _ => (hC k).1.mul_const _
  have hne : (∫ ω, ∑ k, C ω k i * D k j ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (hC k).1.mul_const _)]
    apply Finset.sum_eq_zero
    intro k _
    rw [integral_mul_const, (hC k).2, zero_mul]
  have hfull : ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᵀ * Q)ᵀ * ((Ψ ω)ᵀ * Q)) := by
    filter_upwards [ae_isUnit_block hΨ Q hQ (by omega)] with ω hω
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hω
  have heq : (fun ω => sketchedCore Q (Ψ ω) B i j) =ᵐ[μ]
      fun ω => (Qᵀ * B) i j + ∑ k, C ω k i * D k j := by
    filter_upwards [hfull] with ω hω
    rw [sketchedCore_eq Q Qp (Ψ ω) B hQ hcomp hω, Matrix.add_apply, hnoise]
  refine ⟨((integrable_const _).add hni).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add (integrable_const _) hni, integral_const,
    probReal_univ, one_smul, hne, add_zero]

open scoped Matrix.Norms.L2Operator in
/-- **The actual Gaussian minimum-norm sketch-and-solve estimator is unbiased.** Its matrix
entries are integrable, and its Bochner expectation equals `A⁺ B`. The sample condition is
the one required for the exact residual second moment; rank-zero designs are included.
Source: Epperly–Webber 2026, Theorem 2.1, real Gaussian case.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_sketchAndSolve_of_hasLaw_gaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ω → Matrix (Fin m) (Fin s) ℝ}
    (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) p ℝ)
    (hs : A.rank + 2 ≤ s) :
    Integrable (fun ω => sketchAndSolve A (Ψ ω)ᵀ B) μ ∧
      (∫ ω, sketchAndSolve A (Ψ ω)ᵀ B ∂μ) = moorePenroseInverse A * B := by
  classical
  let : IsProbabilityMeasure μ := hΨ.isProbabilityMeasure
  obtain ⟨Q, hQ, hQA⟩ := exists_orthonormal_frame_reproducing_matrix A
  obtain ⟨Qp, hQp, hcomp⟩ := exists_unitary_complement Q hQ
  have hcomp' : Q * Qᵀ + Qp * Qpᵀ = 1 := by simpa using hcomp
  let R := Qᵀ * A
  have hR : IsUnit (R * Rᵀ) :=
    isUnit_rowGram_of_frame_factorization Q A hQA (by simp)
  have hpinv : moorePenroseInverse A = pinvR R * Qᵀ := by
    have hQQ : Qᵀ * Q = 1 := hQ
    have hpQ : pinvL Q = Qᵀ := by simp [pinvL, hQQ]
    have h := moorePenroseInverse_mul_eq_pinvR_mul_pinvL Q R
      (by change IsUnit (Qᵀ*Q); rw [hQQ]; exact isUnit_one) hR
    rw [show Q * R = A from hQA, hpQ] at h
    exact h
  have hfull : ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᵀ * Q)ᵀ * ((Ψ ω)ᵀ * Q)) := by
    filter_upwards [ae_isUnit_block hΨ Q hQ (by omega)] with ω hω
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hω
  have heq : (fun ω => sketchAndSolve A (Ψ ω)ᵀ B) =ᵐ[μ]
      fun ω => pinvR R * sketchedCore Q (Ψ ω) B := by
    filter_upwards [hfull] with ω hω
    have hfactor : (Ψ ω)ᵀ * A = ((Ψ ω)ᵀ * Q) * R := by
      calc
        (Ψ ω)ᵀ * A = (Ψ ω)ᵀ * (Q * R) := congrArg ((Ψ ω)ᵀ * ·) hQA.symm
        _ = ((Ψ ω)ᵀ * Q) * R := (Matrix.mul_assoc _ _ _).symm
    rw [sketchAndSolve, hfactor,
      moorePenroseInverse_mul_eq_pinvR_mul_pinvL ((Ψ ω)ᵀ*Q) R hω hR, sketchedCore, Matrix.mul_assoc]
  have hcore (i : Fin A.rank) (j : p) :=
    integrable_and_integral_sketchedCore_entry hΨ Q Qp hQ hQp hcomp' hs B i j
  have hi (i : Fin n) (j : p) :
      Integrable (fun ω => (pinvR R * sketchedCore Q (Ψ ω) B) i j) μ := by
    change Integrable (fun ω => ∑ k, pinvR R i k * sketchedCore Q (Ψ ω) B k j) μ
    exact integrable_finsetSum _ fun k _ => (hcore k j).1.const_mul _
  have hXi : Integrable (fun ω => pinvR R * sketchedCore Q (Ψ ω) B) μ :=
    Matrix.integrable_iff_entries.mpr hi
  refine ⟨hXi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, hpinv, Matrix.mul_assoc]
  ext i j
  rw [Matrix.integral_apply hXi i j]
  change (∫ ω, ∑ k, pinvR R i k * sketchedCore Q (Ψ ω) B k j ∂μ) =
    ∑ k, pinvR R i k * (Qᵀ * B) k j
  rw [integral_finsetSum _ (fun k _ => (hcore k j).1.const_mul _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, (hcore k j).2]

end NLAlib
