import NLAlib.Matrix.Norms.Core
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Linarith

/-! # Operator and Frobenius norms of disjoint matrix blocks -/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A coordinate quadratic bound controls the Euclidean operator norm. -/
theorem specNorm_le_of_sum_norm_sq_mulVec_le {K m n : Type*} [RCLike K]
    [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n K} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x : n → K,
      ∑ i, norm ((A *ᵥ x) i) ^ 2 ≤ c ^ 2 * ∑ j, ‖x j‖ ^ 2) : specNorm A ≤ c := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hx := h x.ofLp
  change ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ _ at hx
  have hx' : ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    simpa [EuclideanSpace.norm_sq_eq, mul_pow] using hx
  change ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ ≤ c * ‖x‖
  nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ x.ofLp)), mul_nonneg hc (norm_nonneg x)]

variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]

/-- A block diagonal operator is bounded by the maximum diagonal-block norm. -/
theorem specNorm_fromBlocks_diagonal_le (A : Matrix m m K) (D : Matrix n n K) :
    specNorm (Matrix.fromBlocks A 0 0 D) ≤ max (specNorm A) (specNorm D) := by
  apply specNorm_le_of_sum_norm_sq_mulVec_le (le_max_of_le_left (specNorm_nonneg A))
  intro x
  have hA := sum_norm_sq_mulVec_le_specNorm_sq A (x ∘ Sum.inl)
  have hD := sum_norm_sq_mulVec_le_specNorm_sq D (x ∘ Sum.inr)
  have hAm : specNorm A ^ 2 ≤ max (specNorm A) (specNorm D) ^ 2 :=
    pow_le_pow_left₀ (specNorm_nonneg A) (le_max_left _ _) 2
  have hDm : specNorm D ^ 2 ≤ max (specNorm A) (specNorm D) ^ 2 :=
    pow_le_pow_left₀ (specNorm_nonneg D) (le_max_right _ _) 2
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have hposA : 0 ≤ ∑ i, ‖x (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hposD : 0 ≤ ∑ i, ‖x (Sum.inr i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  dsimp [Function.comp_def] at *
  nlinarith [mul_le_mul_of_nonneg_right hAm hposA, mul_le_mul_of_nonneg_right hDm hposD]

/-- The norm of a directed off-diagonal pair is bounded by the maximum of its
two block norms; this is valid for rectangular sibling blocks. -/
theorem specNorm_fromBlocks_offDiagonal_le (B : Matrix m n K) (C : Matrix n m K) :
    specNorm (Matrix.fromBlocks 0 B C 0) ≤ max (specNorm B) (specNorm C) := by
  apply specNorm_le_of_sum_norm_sq_mulVec_le (le_max_of_le_left (specNorm_nonneg B))
  intro x
  have hB := sum_norm_sq_mulVec_le_specNorm_sq B (x ∘ Sum.inr)
  have hC := sum_norm_sq_mulVec_le_specNorm_sq C (x ∘ Sum.inl)
  have hBm : specNorm B ^ 2 ≤ max (specNorm B) (specNorm C) ^ 2 :=
    pow_le_pow_left₀ (specNorm_nonneg B) (le_max_left _ _) 2
  have hCm : specNorm C ^ 2 ≤ max (specNorm B) (specNorm C) ^ 2 :=
    pow_le_pow_left₀ (specNorm_nonneg C) (le_max_right _ _) 2
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have hposB : 0 ≤ ∑ i, ‖x (Sum.inr i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hposC : 0 ≤ ∑ i, ‖x (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  dsimp [Function.comp_def] at *
  nlinarith [mul_le_mul_of_nonneg_right hBm hposB, mul_le_mul_of_nonneg_right hCm hposC]

omit [DecidableEq m] [DecidableEq n] in
/-- Disjoint rectangular blocks satisfy exact Frobenius Pythagoras. -/
theorem frobSq_fromBlocks {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix m p K) (B : Matrix m q K) (C : Matrix n p K) (D : Matrix n q K) :
    frobSq (Matrix.fromBlocks A B C D) = frobSq A + frobSq B + frobSq C + frobSq D := by
  simp only [frobSq_eq_sum_norm_sq, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

end NLAlib
