import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Defs.Calculus
import NLAlib.Concentration.Matrix.Defs.Dilation
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Equation 2.2.10 — Variance statistic under dilation

Main declaration: `NLAlib.hermitianSecondMoment_dilation_eq_rectSecondMoment`.

Atlas: `hermitian-dilation`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.8, equations (2.2.7–10), printed pp. 28–29.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace NLAlib

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Compression by an isometry does not increase the L2 operator norm. -/
private lemma norm_compress_le {k : Type*} [Fintype k] [DecidableEq k]
    (E : Matrix k m ℂ) (hE : Eᴴ * E = 1) (M : Matrix k k ℂ) :
    ‖Eᴴ * M * E‖ ≤ ‖M‖ := by
  have hE1 : ‖E‖ ≤ 1 := by
    have h1 : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
    have h2 : ‖E‖ * ‖E‖ ≤ 1 := by
      rw [← l2_opNorm_conjTranspose_mul_self, hE]; exact h1
    nlinarith [norm_nonneg E]
  calc ‖Eᴴ * M * E‖ ≤ ‖Eᴴ * M‖ * ‖E‖ := l2_opNorm_mul _ _
    _ ≤ ‖Eᴴ‖ * ‖M‖ * ‖E‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by
      rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖M‖ := by ring

/-- The L2 operator norm of a block-diagonal matrix is the max of the block norms. -/
private lemma norm_fromBlocks_diag (P : Matrix m m ℂ) (Q : Matrix n n ℂ) :
    ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
  apply le_antisymm
  · rw [cstar_norm_def]
    set c := max ‖P‖ ‖Q‖
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    let x₁ : EuclideanSpace ℂ m := WithLp.toLp 2 (fun i => x (Sum.inl i))
    let x₂ : EuclideanSpace ℂ n := WithLp.toLp 2 (fun i => x (Sum.inr i))
    have h1 := l2_opNorm_mulVec P x₁
    have h2 := l2_opNorm_mulVec Q x₂
    have hx : ‖x‖ ^ 2 = ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₁, x₂]
    have hT : ‖toEuclideanCLM (n := m ⊕ n) (𝕜 := ℂ) (fromBlocks P 0 0 Q) x‖ ^ 2 =
        ‖(EuclideanSpace.equiv m ℂ).symm (P *ᵥ x₁)‖ ^ 2 +
          ‖(EuclideanSpace.equiv n ℂ).symm (Q *ᵥ x₂)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp [fromBlocks_mulVec, Fintype.sum_sum_type, x₁, x₂, Function.comp_def]
    have hP : ‖P‖ ≤ c := le_max_left _ _
    have hQ : ‖Q‖ ≤ c := le_max_right _ _
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [hT, mul_pow, hx, mul_add]
    gcongr
    · calc _ ≤ (‖P‖ * ‖x₁‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
    · calc _ ≤ (‖Q‖ * ‖x₂‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
  · apply max_le
    · have h := norm_compress_le (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : P = (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))ᴴ * fromBlocks P 0 0 Q * (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h
    · have h := norm_compress_le (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : Q = (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))ᴴ * fromBlocks P 0 0 Q * (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h

end NLAlib

open NLAlib Matrix

/-- The matrix variance of the Hermitian dilation of a centered rectangular random matrix equals its
rectangular variance statistic.

Tropp 2015, §2.2.8, eq. (2.2.10). Atlas: `hermitian-dilation`. Ported from the Prove2me mission
*An Introduction to Matrix Concentration Inequalities, Ch 6*.

The measurability hypothesis is not used by the proof; it is kept to match the source's standing
assumptions.
atlas: hermitian-dilation -/
theorem NLAlib.hermitianSecondMoment_dilation_eq_rectSecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} [NeZero m] [NeZero n]
    (Z : Ω → Matrix (Fin m) (Fin n) ℂ) (_hMeas : Measurable Z)
    (hL2 : MemLp Z 2 μ) :
    hermitianSecondMoment μ (fun ω => dilation (Z ω - ∫ ω', Z ω' ∂μ)) =
      rectSecondMoment μ (fun ω => Z ω - ∫ ω', Z ω' ∂μ) := by
  have hW2 : MemLp (fun ω => Z ω - ∫ ω', Z ω' ∂μ) 2 μ := hL2.sub (memLp_const _)
  have hWsq : Integrable (fun ω => ‖Z ω - ∫ ω', Z ω' ∂μ‖ ^ 2) μ :=
    hW2.integrable_norm_pow (p := 2) two_ne_zero
  have hP : Integrable
      (fun ω => (Z ω - ∫ ω', Z ω' ∂μ) * (Z ω - ∫ ω', Z ω' ∂μ)ᴴ) μ := by
    refine Integrable.mono' hWsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℂ => X * Xᴴ) :=
        continuous_id.matrix_mul continuous_id.matrix_conjTranspose
      exact hc.comp_aestronglyMeasurable hW2.1
    · calc _ ≤ ‖Z ω - ∫ ω', Z ω' ∂μ‖ * ‖(Z ω - ∫ ω', Z ω' ∂μ)ᴴ‖ := l2_opNorm_mul _ _
        _ = _ := by rw [l2_opNorm_conjTranspose, sq]
  have hQ : Integrable
      (fun ω => (Z ω - ∫ ω', Z ω' ∂μ)ᴴ * (Z ω - ∫ ω', Z ω' ∂μ)) μ := by
    refine Integrable.mono' hWsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℂ => Xᴴ * X) :=
        continuous_id.matrix_conjTranspose.matrix_mul continuous_id
      exact hc.comp_aestronglyMeasurable hW2.1
    · rw [l2_opNorm_conjTranspose_mul_self, sq]
  unfold hermitianSecondMoment rectSecondMoment spectralNorm
  simp_rw [dilation_sq]
  rw [integral_fromBlocks_diag μ _ _ hP hQ, norm_fromBlocks_diag]
