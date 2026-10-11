import NLAlib.LowRank.SpectralRangeFinder
import NLAlib.Matrix.PolynomialIntertwining
import NLAlib.Krylov.Block
import NLAlib.Matrix.DiagonalFilter

/-!
# Polynomial-filter range finding

The one-competitor argument of manuscript `sa:filter` gives squared spectral and
Frobenius residual bounds for an arbitrary polynomial filter. The right inverse of
the leading filtered block is explicit; no inverse of the leading singular block
is needed. All matrix index types are arbitrary finite types.
-/

noncomputable section

open Polynomial
open scoped Matrix

namespace NLAlib

variable {m n k r r' t q : Type*} [Fintype m] [Fintype n] [Fintype k]
  [Fintype r] [Fintype r'] [Fintype t] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq r]
  [DecidableEq r'] [DecidableEq q]

omit [Fintype t] [DecidableEq n] in
/-- A polynomially filtered block SVD has the corresponding filtered diagonal blocks.
Source: manuscript `sa:filter`, the intertwining step before `sa:filter-theorem`.
The blocks need not be diagonal, so their squared singular blocks are written as Grams. -/
theorem aeval_gram_mul_mul_eq_of_block_decomposition
    {A : Matrix m n ℝ} {U₁ : Matrix m k ℝ} {U₂ : Matrix m r ℝ}
    {V₁ : Matrix n k ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix k k ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ)
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℝ) :
    aeval (A * Aᵀ) p * A * Ω =
      U₁ * S₁ * aeval (S₁ᵀ * S₁) p * (V₁ᵀ * Ω) +
      U₂ * S₂ * aeval (S₂ᵀ * S₂) p * (V₂ᵀ * Ω) := by
  have hU' : U₂ᵀ * U₁ = 0 := transpose_mul_eq_zero_comm.1 hU
  have hV' : V₂ᵀ * V₁ = 0 := transpose_mul_eq_zero_comm.1 hV
  have hAtU₁ : Aᵀ * U₁ = V₁ * S₁ᵀ := by
    rw [hA, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [hU₁, hU', Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero]
  have hAtU₂ : Aᵀ * U₂ = V₂ * S₂ᵀ := by
    rw [hA, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [hU, hU₂, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hAV₁ : A * V₁ = U₁ * S₁ := by
    rw [hA, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [hV₁, hV', Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero]
  have hAV₂ : A * V₂ = U₂ * S₂ := by
    rw [hA, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [hV, hV₂, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hB₁ : (A * Aᵀ) * U₁ = U₁ * (S₁ * S₁ᵀ) := by
    rw [Matrix.mul_assoc, hAtU₁, ← Matrix.mul_assoc, hAV₁, Matrix.mul_assoc]
  have hB₂ : (A * Aᵀ) * U₂ = U₂ * (S₂ * S₂ᵀ) := by
    rw [Matrix.mul_assoc, hAtU₂, ← Matrix.mul_assoc, hAV₂, Matrix.mul_assoc]
  have hp₁ := aeval_mul_eq_mul_aeval_of_mul_eq hB₁ p
  have hp₂ := aeval_mul_eq_mul_aeval_of_mul_eq hB₂ p
  conv_lhs => arg 1; arg 2; rw [hA]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [← Matrix.mul_assoc]
  rw [hp₁, hp₂]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (aeval (S₁ * S₁ᵀ) p),
    aeval_gram_mul_eq_mul_aeval_gram S₁ p,
    ← Matrix.mul_assoc (aeval (S₂ * S₂ᵀ) p),
    aeval_gram_mul_eq_mul_aeval_gram S₂ p]
  simp only [Matrix.mul_assoc]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq r]
  [DecidableEq r'] in
/-- The explicit competitor for filtered range finding has precisely the leading block
and the filtered tail correction. Source: manuscript `sa:filter-theorem`, its competitor
`Z = Y Ω₁† C⁻¹ V₁ᵀ`. The right inverses are supplied as data. -/
theorem sub_mul_mul_mul_transpose_eq_of_filtered_blocks
    {A : Matrix m n ℝ} {U₁ : Matrix m k ℝ} {U₂ : Matrix m r ℝ}
    {V₁ : Matrix n k ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ C : Matrix k k ℝ} {S₂ : Matrix r r' ℝ} {D : Matrix r' r' ℝ}
    {Ω₁ : Matrix k t ℝ} {Ω₂ : Matrix r' t ℝ} {R : Matrix t k ℝ}
    {Cinv : Matrix k k ℝ} {Y : Matrix m t ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ)
    (hY : Y = U₁ * S₁ * C * Ω₁ + U₂ * S₂ * D * Ω₂)
    (hR : Ω₁ * R = 1) (hC : C * Cinv = 1) :
    A - Y * R * Cinv * V₁ᵀ =
      U₂ * (S₂ * V₂ᵀ - (S₂ * D * Ω₂ * R * Cinv) * V₁ᵀ) := by
  have hZ : Y * R * Cinv * V₁ᵀ =
      U₁ * S₁ * V₁ᵀ + U₂ * S₂ * D * Ω₂ * R * Cinv * V₁ᵀ := by
    rw [hY, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ω₁, hR, Matrix.one_mul,
      ← Matrix.mul_assoc C, hC, Matrix.one_mul]
  rw [hA, hZ, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]
  abel

/-- The filtered one-competitor argument bounds both squared norms, with the same exact
tail correction. Source: manuscript `sa:filter-theorem`. This algebraic form is the reusable
core; the next theorem supplies the filtered blocks by polynomial calculus. -/
theorem residual_sq_le_of_filtered_blocks
    {A : Matrix m n ℝ} {U₁ : Matrix m k ℝ} {U₂ : Matrix m r ℝ}
    {V₁ : Matrix n k ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ C : Matrix k k ℝ} {S₂ : Matrix r r' ℝ} {D : Matrix r' r' ℝ}
    {Ω₁ : Matrix k t ℝ} {Ω₂ : Matrix r' t ℝ} {R : Matrix t k ℝ}
    {Cinv : Matrix k k ℝ} {Y : Matrix m t ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ)
    (hY : Y = U₁ * S₁ * C * Ω₁ + U₂ * S₂ * D * Ω₂)
    (hR : Ω₁ * R = 1) (hC : C * Cinv = 1)
    (hU₂ : HasOrthonormalCols U₂) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q)
    (hQ : Q * (Qᵀ * Y) = Y) :
    specNorm (residual Q A) ^ 2 ≤ specNorm S₂ ^ 2 +
      specNorm (S₂ * D * Ω₂ * R * Cinv) ^ 2 ∧
    frobSq (residual Q A) ≤ frobSq S₂ + frobSq (S₂ * D * Ω₂ * R * Cinv) := by
  let Z := Y * R * Cinv * V₁ᵀ
  let T := S₂ * D * Ω₂ * R * Cinv
  have hQZ : Q * (Qᵀ * Z) = Z := by
    dsimp [Z]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ Y, ← Matrix.mul_assoc Q, hQ]
  have hdiff : A - Z = U₂ * (S₂ * V₂ᵀ - T * V₁ᵀ) :=
    sub_mul_mul_mul_transpose_eq_of_filtered_blocks hA hY hR hC
  have hres : residual Q A = residual Q (A - Z) := by
    simp only [residual, Matrix.mul_sub, hQZ]
    abel
  have horth : (S₂ * V₂ᵀ) * (-(T * V₁ᵀ))ᵀ = 0 := by
    have hV' : V₂ᵀ * V₁ = 0 := transpose_mul_eq_zero_comm.1 hV
    rw [Matrix.transpose_neg, Matrix.mul_neg, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc S₂, ← Matrix.mul_assoc V₂ᵀ,
      hV', Matrix.zero_mul, Matrix.mul_zero, neg_zero]
  have hs := specNorm_add_sq_le_of_mul_transpose_eq_zero horth
  rw [specNorm_neg, specNorm_mul_transpose_right_of_hasOrthonormalCols hV₂,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hV₁] at hs
  have hforth : frobInner (S₂ * V₂ᵀ) (T * V₁ᵀ) = 0 := by
    rw [← frobInner_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact frobInner_mul_mul_eq_zero _ _ _ _ (transpose_mul_eq_zero_comm.1 hV)
  constructor
  · calc specNorm (residual Q A) ^ 2 ≤ specNorm (A - Z) ^ 2 :=
          pow_le_pow_left₀ (specNorm_nonneg _) (by
            rw [hres]; exact specNorm_sub_mul_transpose_mul_le hQo _) 2
      _ ≤ _ := by
          rw [hdiff, specNorm_mul_left_of_hasOrthonormalCols hU₂, sub_eq_add_neg]
          exact hs
  · calc frobSq (residual Q A) ≤ frobSq (A - Z) := by
          rw [hres]; exact frobSq_residual_le hQo _
      _ = _ := by
          rw [hdiff, frobSq_mul_left_of_orthonormal hU₂,
            frobSq_sub_of_frobInner_eq_zero _ _ hforth,
            frobSq_mul_right_of_orthonormal hV₂, frobSq_mul_right_of_orthonormal hV₁]

/-- Polynomial-filter range finding has the manuscript's exact spectral and Frobenius
constants. Source: manuscript `sa:filter-theorem`; HMT (2011), the one-competitor argument.
Grams replace squares to generalize diagonal SVD blocks to arbitrary orthogonal blocks.
The result includes an empty leading or tail block.
atlas: polynomial-filter-range-finder (partial) -/
theorem residual_sq_le_of_polynomial_filter
    {A : Matrix m n ℝ} {U₁ : Matrix m k ℝ} {U₂ : Matrix m r ℝ}
    {V₁ : Matrix n k ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix k k ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ)
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℝ) (R : Matrix t k ℝ) (Cinv : Matrix k k ℝ)
    (hR : (V₁ᵀ * Ω) * R = 1)
    (hC : aeval (S₁ᵀ * S₁) p * Cinv = 1)
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q)
    (hQ : Q * (Qᵀ * (aeval (A * Aᵀ) p * A * Ω)) =
      aeval (A * Aᵀ) p * A * Ω) :
    specNorm (residual Q A) ^ 2 ≤ specNorm S₂ ^ 2 +
      specNorm (S₂ * aeval (S₂ᵀ * S₂) p * (V₂ᵀ * Ω) * R * Cinv) ^ 2 ∧
    frobSq (residual Q A) ≤ frobSq S₂ +
      frobSq (S₂ * aeval (S₂ᵀ * S₂) p * (V₂ᵀ * Ω) * R * Cinv) :=
  residual_sq_le_of_filtered_blocks hA
    (aeval_gram_mul_mul_eq_of_block_decomposition hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω)
    hR hC hU₂ hV₁ hV₂ hV hQo hQ

omit [DecidableEq n] in
/-- A frame containing the block Krylov space reproduces every filtered sketch of degree
below the Krylov order, simultaneously. Source: manuscript `sa:filter`, its final block
Krylov specialization; Musco--Musco (2015), polynomial competitor argument. -/
theorem mul_transpose_aeval_gram_mul_mul_eq_of_blockKrylovSpace_le
    (A : Matrix m n ℝ) (Ω : Matrix n t ℝ) {Q : Matrix m q ℝ}
    (hQo : HasOrthonormalCols Q) {order : ℕ}
    (hK : blockKrylovSpace (A * Aᵀ) (A * Ω) order ≤ LinearMap.range Q.mulVecLin)
    {p : ℝ[X]} (hp : p.degree < order) :
    Q * (Qᵀ * (aeval (A * Aᵀ) p * A * Ω)) = aeval (A * Aᵀ) p * A * Ω := by
  apply mul_transpose_mul_eq_of_range_le hQo
  rw [Matrix.mul_assoc]
  exact (range_aeval_mul_le_blockKrylovSpace _ _ hp).trans hK

/-- The smallest absolute leading polynomial value. Source: manuscript `sa:filter`,
its `c_phi`. A positive-dimensional leading block makes the minimum nonempty. -/
def filterHeadMinAbs {κ : ℕ} [Nonempty (Fin κ)] (s : Fin κ → ℝ) (p : ℝ[X]) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => |p.eval ((s i) ^ 2)|

/-- The largest absolute filtered singular tail entry, with value zero for an empty
tail. Source: manuscript `sa:filter`, its `t_phi`; zero-padded singular values are allowed. -/
def filterTailMaxAbs (s : ℕ → ℝ) (p : ℝ[X]) (a b : ℕ) : ℝ :=
  (((Finset.range (min a b)).sup
    (fun i => Real.toNNReal (|s i * p.eval (s i ^ 2)|)) : NNReal) : ℝ)

/-- The leading filter minimum bounds each leading filter value from below.
Source: manuscript `sa:filter`, definition of `c_phi`. -/
theorem filterHeadMinAbs_le {κ : ℕ} [Nonempty (Fin κ)] (s : Fin κ → ℝ)
    (p : ℝ[X]) (i : Fin κ) : filterHeadMinAbs s p ≤ |p.eval ((s i) ^ 2)| :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- Every finite tail filter value is bounded by the zero-safe tail maximum.
Source: manuscript `sa:filter`, definition of `t_phi`. -/
theorem abs_mul_eval_le_filterTailMaxAbs (s : ℕ → ℝ) (p : ℝ[X]) {a b i : ℕ}
    (hi : i < min a b) : |s i * p.eval (s i ^ 2)| ≤ filterTailMaxAbs s p a b := by
  have h := Finset.le_sup (f := fun j => Real.toNNReal (|s j * p.eval (s j ^ 2)|))
    (Finset.mem_range.mpr hi)
  have hc : (Real.toNNReal (|s i * p.eval (s i ^ 2)|) : ℝ) ≤ filterTailMaxAbs s p a b :=
    NNReal.coe_le_coe.mpr h
  rwa [Real.coe_toNNReal _ (abs_nonneg _)] at hc

/-- The scalar maximum/minimum filter envelope follows from the exact polynomial
competitor. Source: manuscript `sa:filter`, the scalar spectral inequality following
`sa:filter-theorem`. Choosing `c = filterHeadMinAbs` and `τ = filterTailMaxAbs`
gives exactly its constants; the tail can be empty.
atlas: polynomial-filter-range-finder (partial) -/
theorem specNorm_residual_sq_le_of_polynomial_filter_envelopes
    [DecidableEq t] {κ a b : ℕ} {A : Matrix m n ℝ} {U₁ : Matrix m (Fin κ) ℝ}
    {U₂ : Matrix m (Fin a) ℝ} {V₁ : Matrix n (Fin κ) ℝ}
    {V₂ : Matrix n (Fin b) ℝ} (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal s₁ * V₁ᵀ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ) * V₂ᵀ)
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℝ) (R : Matrix t (Fin κ) ℝ)
    (hR : (V₁ᵀ * Ω) * R = 1) {c τ : ℝ}
    (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval ((s₁ i) ^ 2)|)
    (hτ : 0 ≤ τ) (hmax : ∀ i, i < min a b → |s₂ i * p.eval (s₂ i ^ 2)| ≤ τ)
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q)
    (hQ : Q * (Qᵀ * (aeval (A * Aᵀ) p * A * Ω)) = aeval (A * Aᵀ) p * A * Ω) :
    specNorm (residual Q A) ^ 2 ≤
      specNorm (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ) ^ 2 +
        (τ / c) ^ 2 * specNorm (V₂ᵀ * Ω) ^ 2 * specNorm R ^ 2 := by
  let S₂ : Matrix (Fin a) (Fin b) ℝ := rectDiag s₂
  let D := aeval (S₂ᵀ * S₂) p
  let Cinv := Matrix.diagonal fun i => (p.eval ((s₁ i) ^ 2))⁻¹
  obtain ⟨hC, hCi⟩ := diagonal_filter_right_inverse_and_specNorm_le s₁ p hc hmin
  have htail : specNorm (S₂ * D) ≤ τ := by
    change specNorm ((rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ) *
      aeval ((rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ)ᵀ * rectDiag s₂) p) ≤ τ
    rw [rectDiag_mul_aeval_gram]
    exact specNorm_rectDiag_le hτ hmax
  have hcore := (residual_sq_le_of_polynomial_filter hA hU₁ hU₂ hU hV₁ hV₂ hV
    p Ω R Cinv hR hC hQo hQ).1
  have hTR : specNorm (S₂ * D * (V₂ᵀ * Ω) * R) ≤
      (specNorm (S₂ * D) * specNorm (V₂ᵀ * Ω)) * specNorm R :=
    (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (specNorm_mul_le _ _) (specNorm_nonneg R))
  have hchain : specNorm (S₂ * D * (V₂ᵀ * Ω) * R * Cinv) ≤
      (τ / c) * specNorm (V₂ᵀ * Ω) * specNorm R := by
    calc specNorm (S₂ * D * (V₂ᵀ * Ω) * R * Cinv) ≤
        ((specNorm (S₂ * D) * specNorm (V₂ᵀ * Ω)) * specNorm R) * specNorm Cinv :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hTR (specNorm_nonneg Cinv))
      _ = specNorm (S₂ * D) * (specNorm (V₂ᵀ * Ω) * specNorm R * specNorm Cinv) := by ring
      _ ≤ τ * (specNorm (V₂ᵀ * Ω) * specNorm R * specNorm Cinv) :=
        mul_le_mul_of_nonneg_right htail
          (mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) (specNorm_nonneg _))
      _ = (τ * specNorm (V₂ᵀ * Ω) * specNorm R) * specNorm Cinv := by ring
      _ ≤ (τ * specNorm (V₂ᵀ * Ω) * specNorm R) * (1 / c) :=
        mul_le_mul_of_nonneg_left hCi
          (mul_nonneg (mul_nonneg hτ (specNorm_nonneg _)) (specNorm_nonneg _))
      _ = _ := by ring
  calc specNorm (residual Q A) ^ 2 ≤ specNorm S₂ ^ 2 +
        specNorm (S₂ * D * (V₂ᵀ * Ω) * R * Cinv) ^ 2 := hcore
    _ ≤ specNorm S₂ ^ 2 + ((τ / c) * specNorm (V₂ᵀ * Ω) * specNorm R) ^ 2 :=
      add_le_add le_rfl (pow_le_pow_left₀ (specNorm_nonneg _) hchain 2)
    _ = _ := by rw [mul_pow, mul_pow]

/-- The scalar spectral filter bound uses the actual finite maximum and minimum.
Source: manuscript `sa:filter`, scalar inequality with zero-indexed padded singular
values. The leading and tail diagonal arrays come from the ordinary SVD block
certificate. Empty tails are included.
atlas: polynomial-filter-range-finder (partial) -/
theorem specNorm_residual_sq_le_filterTailMaxAbs_div_filterHeadMinAbs
    [DecidableEq t] {κ a b : ℕ} [Nonempty (Fin κ)] {A : Matrix m n ℝ}
    {U₁ : Matrix m (Fin κ) ℝ} {U₂ : Matrix m (Fin a) ℝ}
    {V₁ : Matrix n (Fin κ) ℝ} {V₂ : Matrix n (Fin b) ℝ}
    (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal s₁ * V₁ᵀ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ) * V₂ᵀ)
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℝ) (R : Matrix t (Fin κ) ℝ)
    (hR : (V₁ᵀ * Ω) * R = 1) (hc : 0 < filterHeadMinAbs s₁ p)
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q)
    (hQ : Q * (Qᵀ * (aeval (A * Aᵀ) p * A * Ω)) = aeval (A * Aᵀ) p * A * Ω) :
    specNorm (residual Q A) ^ 2 ≤
      specNorm (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ) ^ 2 +
        (filterTailMaxAbs s₂ p a b / filterHeadMinAbs s₁ p) ^ 2 *
          specNorm (V₂ᵀ * Ω) ^ 2 * specNorm R ^ 2 :=
  specNorm_residual_sq_le_of_polynomial_filter_envelopes s₁ s₂ hA hU₁ hU₂ hU hV₁ hV₂ hV
    p Ω R hR hc (filterHeadMinAbs_le s₁ p) (NNReal.coe_nonneg _)
    (fun _ hi => abs_mul_eval_le_filterTailMaxAbs s₂ p hi) hQo hQ

end NLAlib
