/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Basic.LeastSquares
import NLAlib.Sketching.Properties.SubspaceEmbedding.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Linarith

/-!
# Sketch-and-solve least squares

The sketched minimum-norm solution is the actual Moore–Penrose estimator. A subspace
embedding of the data and right-hand side bounds the residual of every sketched minimizer,
including rank-deficient input. The native embedding convention uses squared norms.

Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16. The deterministic comparison
is adapted from `NLA-lib/NLAlib`, `Regression/Embedding.lean`, commit
`79f8cc2f74523a30d1d53316542b826018e245a4` (Apache-2.0).
Atlas: `sketch-and-solve-ls` (deterministic clause).
-/

noncomputable section
open scoped Matrix
namespace NLAlib

section Definition
variable {𝕜 k m n p : Type*} [RCLike 𝕜]
  [Fintype k] [Fintype m] [Fintype n]

/-- The minimum-norm sketch-and-solve estimator `(S A)⁺ S B`. It is defined also when
the sketched matrix is rank deficient, using the general Moore–Penrose inverse.
Source: Woodruff 2014, §2.2; Epperly–Webber 2026, Theorem 2.1. -/
def sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    Matrix n p 𝕜 := moorePenroseInverse (S * A) * (S * B)

end Definition

section Realization
variable {k m n p : Type*} [Fintype k] [Fintype m] [Fintype n]

/-- Every column of the actual sketch-and-solve estimator solves its sketched least-squares
problem, even when the design or sketch is rank deficient.
Source: the Moore–Penrose characterization of least squares (Golub–Van Loan 2013, §5.5.2). -/
theorem isLeastSquaresSolution_sketchAndSolve_col (A : Matrix m n ℝ)
    (S : Matrix k m ℝ) (B : Matrix m p ℝ) (j : p) :
    IsLeastSquaresSolution (S * A) (S *ᵥ B.col j) ((sketchAndSolve A S B).col j) := by
  exact isLeastSquaresSolution_moorePenroseInverse_mulVec (S * A) (S *ᵥ B.col j)

end Realization

section Embedding
variable {k m n d : Type*} [Fintype k] [Fintype m] [Fintype n] [Fintype d]
  {S : Matrix k m ℝ} {A : Matrix m n ℝ} {U : Matrix m d ℝ}
  {b : m → ℝ} {x : n → ℝ} {ε : ℝ}

/-- Every sketched least-squares minimizer has squared residual at most
`(1 + ε) / (1 - ε)` times that of every comparison point, if the embedding spans the data
and right-hand side and `ε < 1`. No rank assumption is needed.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16, in squared norms.
atlas: sketch-and-solve-ls (partial) -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le (h : IsSubspaceEmbedding S U ε)
    (hε : ε < 1) (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hb : b ∈ LinearMap.range U.mulVecLin)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ b) x) (y : n → ℝ) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 ≤
      (1 + ε) / (1 - ε) * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ ^ 2 := by
  have hemb : ∀ v ∈ LinearMap.range U.mulVecLin,
      (1 - ε) * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ v)‖ ^ 2 ∧
      ‖WithLp.toLp 2 (S *ᵥ v)‖ ^ 2 ≤ (1 + ε) * ‖WithLp.toLp 2 v‖ ^ 2 := by
    rintro v ⟨w, rfl⟩
    simpa only [Matrix.mulVecLin_apply, norm_toLp_sq_eq_dotProduct_self] using h w
  have hAx (z : n → ℝ) : A *ᵥ z ∈ LinearMap.range U.mulVecLin := hA ⟨z, rfl⟩
  have h₁ := (hemb _ (sub_mem hb (hAx x))).1
  have h₂ := (hemb _ (sub_mem hb (hAx y))).2
  have h₃ : ‖WithLp.toLp 2 (S *ᵥ (b - A *ᵥ x))‖ ^ 2 ≤
      ‖WithLp.toLp 2 (S *ᵥ (b - A *ᵥ y))‖ ^ 2 := by
    simpa only [Matrix.mulVec_sub, Matrix.mulVec_mulVec] using
      pow_le_pow_left₀ (norm_nonneg _) (hx y) 2
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀' (sub_pos.mpr hε)).2 (h₁.trans (h₃.trans h₂))

/-- The unsquared residual comparison for a squared-norm subspace embedding has the sharper
factor `sqrt ((1 + ε) / (1 - ε))`.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16.
atlas: sketch-and-solve-ls (partial) -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_le_sqrt (h : IsSubspaceEmbedding S U ε)
    (hε : ε < 1) (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hb : b ∈ LinearMap.range U.mulVecLin)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ b) x) (y : n → ℝ) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤
      Real.sqrt ((1 + ε) / (1 - ε)) * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ := by
  calc
    _ = Real.sqrt (‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 + ε) / (1 - ε) * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ ^ 2) :=
      Real.sqrt_le_sqrt (h.norm_sub_mulVec_sq_le hε hA hb hx y)
    _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The usual sketch-and-solve factor `(1 + ε) / (1 - ε)` follows from the sharper squared-norm
embedding comparison when `0 ≤ ε < 1`, for every sketched minimizer and comparison point.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16.
atlas: sketch-and-solve-ls (partial) -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_le (h : IsSubspaceEmbedding S U ε)
    (hε₀ : 0 ≤ ε) (hε : ε < 1)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hb : b ∈ LinearMap.range U.mulVecLin)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ b) x) (y : n → ℝ) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤
      (1 + ε) / (1 - ε) * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ := by
  have hc : 1 ≤ (1 + ε) / (1 - ε) :=
    (le_div_iff₀ (sub_pos.mpr hε)).2 (by linarith)
  refine (h.norm_sub_mulVec_le_sqrt hε hA hb hx y).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (Real.sqrt_le_iff).2 ⟨by linarith, by nlinarith⟩

/-- The usual embedding hypothesis on the augmented matrix `[A, b]` gives the residual
guarantee against the actual optimal least-squares residual. Every sketched minimizer is
covered; no full-rank condition is assumed.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16.
atlas: sketch-and-solve-ls (partial) -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_le_of_fromCols
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit b)) ε)
    (hε₀ : 0 ≤ ε) (hε : ε < 1)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ b) x) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ (1 + ε) / (1 - ε) *
      ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ := by
  apply h.norm_sub_mulVec_le hε₀ hε _ _ hx
  · rintro v ⟨w, rfl⟩
    refine ⟨Sum.elim w 0, ?_⟩
    simp
  · refine ⟨Sum.elim 0 (fun _ : Unit => 1), ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim,
      Matrix.mulVec_zero, zero_add]
    ext i
    simp [Matrix.mulVec, dotProduct]

end Embedding
end NLAlib
