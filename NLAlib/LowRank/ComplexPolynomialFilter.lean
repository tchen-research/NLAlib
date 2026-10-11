import NLAlib.Matrix.PolynomialIntertwining
import NLAlib.Matrix.ComplexProjectionBounds
import NLAlib.LowRank.PolynomialFilter
import NLAlib.Krylov.ComplexBlock

/-!
# Complex polynomial-filter range finding

The manuscript's exact squared spectral and Frobenius competitor bounds use
actual complex column projectors, conjugate Grams, and a real polynomial filter.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n k r r' t q : Type*} [Fintype m] [Fintype n] [Fintype k]
  [Fintype r] [Fintype r'] [Fintype t] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq r]
  [DecidableEq r'] [DecidableEq q]

private theorem complex_mul_conjTranspose_eq_zero_comm
    {a b c : Type*} [Fintype a] {X : Matrix a b ℂ} {Y : Matrix a c ℂ}
    (h : Xᴴ * Y = 0) : Yᴴ * X = 0 := by
  have ht := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using ht
omit [Fintype t] [DecidableEq n] in
/-- A polynomially filtered block SVD has the corresponding filtered diagonal blocks.
Source: manuscript `sa:filter`, the intertwining step before `sa:filter-theorem`.
The blocks need not be diagonal, so their squared singular blocks are written as Grams. -/
theorem aeval_conjGram_mul_mul_eq_of_block_decomposition
    {A : Matrix m n ℂ} {U₁ : Matrix m k ℂ} {U₂ : Matrix m r ℂ}
    {V₁ : Matrix n k ℂ} {V₂ : Matrix n r' ℂ}
    {S₁ : Matrix k k ℂ} {S₂ : Matrix r r' ℂ}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1)
    (hU : U₁ᴴ * U₂ = 0) (hV₁ : V₁ᴴ * V₁ = 1)
    (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) :
    aeval (A * Aᴴ) p * A * Ω =
      U₁ * S₁ * aeval (S₁ᴴ * S₁) p * (V₁ᴴ * Ω) +
      U₂ * S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) := by
  have hU' : U₂ᴴ * U₁ = 0 := complex_mul_conjTranspose_eq_zero_comm hU
  have hV' : V₂ᴴ * V₁ = 0 := complex_mul_conjTranspose_eq_zero_comm hV
  have hAtU₁ : Aᴴ * U₁ = V₁ * S₁ᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [hU₁, hU', Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero]
  have hAtU₂ : Aᴴ * U₂ = V₂ * S₂ᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul]
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
  have hB₁ : (A * Aᴴ) * U₁ = U₁ * (S₁ * S₁ᴴ) := by
    rw [Matrix.mul_assoc, hAtU₁, ← Matrix.mul_assoc, hAV₁, Matrix.mul_assoc]
  have hB₂ : (A * Aᴴ) * U₂ = U₂ * (S₂ * S₂ᴴ) := by
    rw [Matrix.mul_assoc, hAtU₂, ← Matrix.mul_assoc, hAV₂, Matrix.mul_assoc]
  have hp₁ := aeval_mul_eq_mul_aeval_of_mul_eq hB₁ p
  have hp₂ := aeval_mul_eq_mul_aeval_of_mul_eq hB₂ p
  conv_lhs => arg 1; arg 2; rw [hA]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [← Matrix.mul_assoc]
  rw [hp₁, hp₂]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (aeval (S₁ * S₁ᴴ) p),
    aeval_conjGram_mul_eq_mul_aeval_conjGram S₁ p,
    ← Matrix.mul_assoc (aeval (S₂ * S₂ᴴ) p),
    aeval_conjGram_mul_eq_mul_aeval_conjGram S₂ p]
  simp only [Matrix.mul_assoc]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq r]
  [DecidableEq r'] in
/-- The explicit competitor for filtered range finding has precisely the leading block
and the filtered tail correction. Source: manuscript `sa:filter-theorem`, its competitor
`Z = Y Ω₁† C⁻¹ V₁ᴴ`. The right inverses are supplied as data. -/
theorem sub_mul_mul_mul_conjTranspose_eq_of_filtered_blocks
    {A : Matrix m n ℂ} {U₁ : Matrix m k ℂ} {U₂ : Matrix m r ℂ}
    {V₁ : Matrix n k ℂ} {V₂ : Matrix n r' ℂ}
    {S₁ C : Matrix k k ℂ} {S₂ : Matrix r r' ℂ} {D : Matrix r' r' ℂ}
    {Ω₁ : Matrix k t ℂ} {Ω₂ : Matrix r' t ℂ} {R : Matrix t k ℂ}
    {Cinv : Matrix k k ℂ} {Y : Matrix m t ℂ}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    (hY : Y = U₁ * S₁ * C * Ω₁ + U₂ * S₂ * D * Ω₂)
    (hR : Ω₁ * R = 1) (hC : C * Cinv = 1) :
    A - Y * R * Cinv * V₁ᴴ =
      U₂ * (S₂ * V₂ᴴ - (S₂ * D * Ω₂ * R * Cinv) * V₁ᴴ) := by
  have hZ : Y * R * Cinv * V₁ᴴ =
      U₁ * S₁ * V₁ᴴ + U₂ * S₂ * D * Ω₂ * R * Cinv * V₁ᴴ := by
    rw [hY, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ω₁, hR, Matrix.one_mul,
      ← Matrix.mul_assoc C, hC, Matrix.one_mul]
  rw [hA, hZ, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]
  abel

/-- The actual complex filtered column projector obeys the exact squared spectral
competitor bound. Source: manuscript `sa:filter-theorem`, the orthogonal-row argument;
HMT (2011), deterministic range finding. Empty leading and tail blocks are allowed.
atlas: polynomial-filter-range-finder (partial) -/
theorem norm_complex_filter_residual_sq_le_of_filtered_blocks
    [DecidableEq t]
    {A : Matrix m n ℂ} {U₁ : Matrix m k ℂ} {U₂ : Matrix m r ℂ}
    {V₁ : Matrix n k ℂ} {V₂ : Matrix n r' ℂ}
    {S₁ C : Matrix k k ℂ} {S₂ : Matrix r r' ℂ} {D : Matrix r' r' ℂ}
    {Ω₁ : Matrix k t ℂ} {Ω₂ : Matrix r' t ℂ} {R : Matrix t k ℂ}
    {Cinv : Matrix k k ℂ} {Y : Matrix m t ℂ}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    (hY : Y = U₁ * S₁ * C * Ω₁ + U₂ * S₂ * D * Ω₂)
    (hR : Ω₁ * R = 1) (hC : C * Cinv = 1)
    (hU₂ : U₂ᴴ * U₂ = 1) (hV₁ : V₁ᴴ * V₁ = 1)
    (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0) :
    ‖A - complexColumnProjector Y * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
      ‖S₂ * D * Ω₂ * R * Cinv‖ ^ 2 := by
  let Z := Y * R * Cinv * V₁ᴴ
  let T := S₂ * D * Ω₂ * R * Cinv
  have hPZ : complexColumnProjector Y * Z = Z := by
    dsimp [Z]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      complexColumnProjector_mul]
  have hres : A - complexColumnProjector Y * A =
      (A - Z) - complexColumnProjector Y * (A - Z) := by
    rw [Matrix.mul_sub, hPZ]
    abel
  have hdiff : A - Z = U₂ * (S₂ * V₂ᴴ - T * V₁ᴴ) :=
    sub_mul_mul_mul_conjTranspose_eq_of_filtered_blocks hA hY hR hC
  have horth : (S₂ * V₂ᴴ) * (-(T * V₁ᴴ))ᴴ = 0 := by
    rw [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc S₂,
      ← Matrix.mul_assoc V₂ᴴ, complex_mul_conjTranspose_eq_zero_comm hV,
      Matrix.zero_mul, Matrix.mul_zero, neg_zero]
  have hs := norm_add_sq_le_of_mul_conjTranspose_eq_zero horth
  rw [norm_neg, norm_mul_conjTranspose_right_of_conjTranspose_mul_eq_one hV₂,
    norm_mul_conjTranspose_right_of_conjTranspose_mul_eq_one hV₁] at hs
  calc ‖A - complexColumnProjector Y * A‖ ^ 2 ≤ ‖A - Z‖ ^ 2 := by
        rw [hres]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_complexColumnProjector_mul_le Y _) 2
    _ ≤ _ := by
        rw [hdiff, norm_mul_left_of_conjTranspose_mul_eq_one hU₂, sub_eq_add_neg]
        exact hs

/-- A real polynomial filter of an actual complex matrix satisfies the squared
spectral competitor bound with its exact filtered tail correction.
Source: manuscript `sa:filter-theorem`; HMT (2011), deterministic range finding.
atlas: polynomial-filter-range-finder (partial) -/
theorem norm_complex_polynomial_filter_residual_sq_le [DecidableEq t]
    {A : Matrix m n ℂ} {U₁ : Matrix m k ℂ} {U₂ : Matrix m r ℂ}
    {V₁ : Matrix n k ℂ} {V₂ : Matrix n r' ℂ}
    {S₁ : Matrix k k ℂ} {S₂ : Matrix r r' ℂ}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1)
    (hU : U₁ᴴ * U₂ = 0) (hV₁ : V₁ᴴ * V₁ = 1)
    (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) (R : Matrix t k ℂ) (Cinv : Matrix k k ℂ)
    (hR : (V₁ᴴ * Ω) * R = 1) (hC : aeval (S₁ᴴ * S₁) p * Cinv = 1) :
    ‖A - complexColumnProjector (aeval (A * Aᴴ) p * A * Ω) * A‖ ^ 2 ≤
      ‖S₂‖ ^ 2 + ‖S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 :=
  norm_complex_filter_residual_sq_le_of_filtered_blocks hA
    (aeval_conjGram_mul_mul_eq_of_block_decomposition hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω)
    hR hC hU₂ hV₁ hV₂ hV

section Frobenius
open scoped Matrix.Norms.Frobenius

omit [DecidableEq n] in
/-- The actual complex filtered column projector obeys the exact squared Frobenius
competitor bound. Source: manuscript `sa:filter-theorem`, the orthogonal-row identity.
This uses genuine complex column projection, at all ranks and block shapes.
atlas: polynomial-filter-range-finder (partial) -/
theorem frobenius_norm_complex_filter_residual_sq_le_of_filtered_blocks
    [DecidableEq t]
    {A : Matrix m n ℂ} {U₁ : Matrix m k ℂ} {U₂ : Matrix m r ℂ}
    {V₁ : Matrix n k ℂ} {V₂ : Matrix n r' ℂ}
    {S₁ C : Matrix k k ℂ} {S₂ : Matrix r r' ℂ} {D : Matrix r' r' ℂ}
    {Ω₁ : Matrix k t ℂ} {Ω₂ : Matrix r' t ℂ} {R : Matrix t k ℂ}
    {Cinv : Matrix k k ℂ} {Y : Matrix m t ℂ}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    (hY : Y = U₁ * S₁ * C * Ω₁ + U₂ * S₂ * D * Ω₂)
    (hR : Ω₁ * R = 1) (hC : C * Cinv = 1)
    (hU₂ : U₂ᴴ * U₂ = 1) (hV₁ : V₁ᴴ * V₁ = 1)
    (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0) :
    ‖A - complexColumnProjector Y * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
      ‖S₂ * D * Ω₂ * R * Cinv‖ ^ 2 := by
  let Z := Y * R * Cinv * V₁ᴴ
  let T := S₂ * D * Ω₂ * R * Cinv
  have hPZ : complexColumnProjector Y * Z = Z := by
    dsimp [Z]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      complexColumnProjector_mul]
  have hres : A - complexColumnProjector Y * A =
      (A - Z) - complexColumnProjector Y * (A - Z) := by
    rw [Matrix.mul_sub, hPZ]
    abel
  have hdiff : A - Z = U₂ * (S₂ * V₂ᴴ - T * V₁ᴴ) :=
    sub_mul_mul_mul_conjTranspose_eq_of_filtered_blocks hA hY hR hC
  have horth : (S₂ * V₂ᴴ) * (-(T * V₁ᴴ))ᴴ = 0 := by
    rw [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc S₂,
      ← Matrix.mul_assoc V₂ᴴ, complex_mul_conjTranspose_eq_zero_comm hV,
      Matrix.zero_mul, Matrix.mul_zero, neg_zero]
  have hs := frobenius_norm_add_sq_eq_of_mul_conjTranspose_eq_zero horth
  rw [norm_neg, frobenius_norm_sq_mul_conjTranspose_right_of_conjTranspose_mul_eq_one hV₂,
    frobenius_norm_sq_mul_conjTranspose_right_of_conjTranspose_mul_eq_one hV₁] at hs
  calc ‖A - complexColumnProjector Y * A‖ ^ 2 ≤ ‖A - Z‖ ^ 2 := by
        rw [hres]
        exact frobenius_norm_sub_complexColumnProjector_mul_sq_le Y _
    _ = _ := by
        rw [hdiff, frobenius_norm_sq_mul_left_of_conjTranspose_mul_eq_one hU₂,
          sub_eq_add_neg]
        exact hs

omit [DecidableEq n] in
/-- A real polynomial filter of an actual complex matrix satisfies the squared
Frobenius competitor bound with its exact filtered tail correction.
Source: manuscript `sa:filter-theorem`; HMT (2011), deterministic range finding.
atlas: polynomial-filter-range-finder (partial) -/
theorem frobenius_norm_complex_polynomial_filter_residual_sq_le [DecidableEq t]
    {A : Matrix m n ℂ} {U₁ : Matrix m k ℂ} {U₂ : Matrix m r ℂ}
    {V₁ : Matrix n k ℂ} {V₂ : Matrix n r' ℂ}
    {S₁ : Matrix k k ℂ} {S₂ : Matrix r r' ℂ}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1)
    (hU : U₁ᴴ * U₂ = 0) (hV₁ : V₁ᴴ * V₁ = 1)
    (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) (R : Matrix t k ℂ) (Cinv : Matrix k k ℂ)
    (hR : (V₁ᴴ * Ω) * R = 1) (hC : aeval (S₁ᴴ * S₁) p * Cinv = 1) :
    ‖A - complexColumnProjector (aeval (A * Aᴴ) p * A * Ω) * A‖ ^ 2 ≤
      ‖S₂‖ ^ 2 + ‖S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 :=
  frobenius_norm_complex_filter_residual_sq_le_of_filtered_blocks hA
    (aeval_conjGram_mul_mul_eq_of_block_decomposition hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω)
    hR hC hU₂ hV₁ hV₂ hV

end Frobenius
/-- The actual complex column projector reproduces every matrix whose native
column range it contains. Source: orthogonal projection onto the actual range;
supports manuscript `sa:filter`. -/
theorem complexColumnProjector_mul_eq_of_range_mulVecLin_le
    [DecidableEq t] (Q : Matrix m q ℂ) (Y : Matrix m t ℂ)
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    complexColumnProjector Q * Y = Y := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, toEuclideanLin_complexColumnProjector]
  apply LinearMap.ext
  intro x
  apply (Submodule.starProjection_eq_self_iff (K := complexColumnSpace Q)).mpr
  obtain ⟨z, hz⟩ := h (show Y *ᵥ WithLp.ofLp x ∈ LinearMap.range Y.mulVecLin from
    ⟨WithLp.ofLp x, rfl⟩)
  refine ⟨WithLp.toLp 2 z, ?_⟩
  have hh := congrArg (WithLp.toLp 2) hz
  simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVecLin_apply] using hh

omit [DecidableEq n] in
/-- A complex frame containing the actual block Krylov space reproduces every
filtered sketch below its order, simultaneously. Source: manuscript `sa:filter`,
block Krylov specialization; Musco--Musco (2015), polynomial competitor.
atlas: polynomial-filter-range-finder (partial) -/
theorem complexColumnProjector_aeval_conjGram_mul_mul_eq_of_complexBlockKrylovSpace_le
    [DecidableEq t] (A : Matrix m n ℂ) (Ω : Matrix n t ℂ) (Q : Matrix m q ℂ)
    {order : ℕ}
    (hK : complexBlockKrylovSpace (A * Aᴴ) (A * Ω) order ≤ LinearMap.range Q.mulVecLin)
    {p : ℝ[X]} (hp : p.degree < order) :
    complexColumnProjector Q * (aeval (A * Aᴴ) p * A * Ω) = aeval (A * Aᴴ) p * A * Ω := by
  apply complexColumnProjector_mul_eq_of_range_mulVecLin_le
  rw [Matrix.mul_assoc]
  exact (range_aeval_mul_le_complexBlockKrylovSpace _ _ hp).trans hK

end NLAlib
