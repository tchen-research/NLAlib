import NLAlib.Matrix.Basic.Tikhonov
import NLAlib.Matrix.Spectral.ThinSingularFunctions
/-!
# Truncated-SVD regularization

A retained positive singular family defines the truncated matrix and its
full Moore–Penrose inverse. The regularized solution is the unique residual
minimizer in the retained right singular subspace. Its bias and propagated
noise are exactly orthogonal, giving the sharp inverse-singular-value bound.

Source: Hansen, §3.1; matrix-toolkit re-derivation, §26.
Atlas: `truncated-svd-regularization`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
variable [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- The retained-singular-family specialization of the shared thin matrix
constructor. The abbreviation keeps the existing TSVD-facing API compatible. -/
abbrev singularTripletMatrix (U : Matrix m r 𝕜) (V : Matrix n r 𝕜) (σ : r → ℝ) :
    Matrix m n 𝕜 := thinSingularMatrix U V σ

/-- The inverse filter of a retained positive singular family. -/
def truncatedSingularInverse (U : Matrix m r 𝕜) (V : Matrix n r 𝕜) (σ : r → ℝ) :
    Matrix n m 𝕜 := V * diagonal (fun i => ((σ i)⁻¹ : 𝕜)) * Uᴴ

/-- The retained singular family is a full thin SVD of its truncation. -/
theorem IsSingularTripletFamily.isThinSVD_singularTripletMatrix {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSingularTripletFamily A U V σ) :
    IsThinSVD (singularTripletMatrix U V σ) U V σ :=
  ⟨h.left_orth, h.right_orth, h.pos, rfl⟩

/-- The spectral filter is exactly the Moore–Penrose inverse of the
truncated matrix, with no inverse of a zero singular value involved.
atlas: truncated-svd-regularization (partial) -/
theorem IsSingularTripletFamily.moorePenroseInverse_singularTripletMatrix
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSingularTripletFamily A U V σ) :
    moorePenroseInverse (singularTripletMatrix U V σ) = truncatedSingularInverse U V σ :=
  h.isThinSVD_singularTripletMatrix.moorePenroseInverse_eq

/-- The retained inverse followed by the original matrix is the retained
right-space orthogonal projector. -/
theorem IsSingularTripletFamily.truncatedSingularInverse_mul {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSingularTripletFamily A U V σ) :
    truncatedSingularInverse U V σ * A = V * Vᴴ := by
  have hUA : Uᴴ * A = diagonal (fun i => (σ i : 𝕜)) * Vᴴ := by
    have he := congrArg Matrix.conjTranspose h.adjoint_mul_left
    have hs : star (fun i => (σ i : 𝕜)) = fun i => (σ i : 𝕜) := by
      funext i; simp [Pi.star_apply]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs] using he
  have hD : (diagonal fun i => ((σ i)⁻¹ : 𝕜)) * diagonal (fun i => (σ i : 𝕜)) =
      (1 : Matrix r r 𝕜) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [(h.pos i).ne']
    · simp [hij]
  rw [truncatedSingularInverse, Matrix.mul_assoc, hUA, ← Matrix.mul_assoc,
    Matrix.mul_assoc V, hD, Matrix.mul_one]

/-- TSVD is the unique Euclidean residual minimizer in the retained right
singular subspace, rather than an unconstrained least-squares assertion.
atlas: truncated-svd-regularization (partial) -/
theorem IsSingularTripletFamily.truncatedSingularInverse_unique_minimizer
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSingularTripletFamily A U V σ) (b : m → 𝕜) :
    truncatedSingularInverse U V σ *ᵥ b ∈ LinearMap.range V.mulVecLin ∧
    (∀ x ∈ LinearMap.range V.mulVecLin,
      ‖WithLp.toLp 2 (A *ᵥ (truncatedSingularInverse U V σ *ᵥ b) - b)‖ ≤
        ‖WithLp.toLp 2 (A *ᵥ x - b)‖) ∧
    ∀ x ∈ LinearMap.range V.mulVecLin,
      ‖WithLp.toLp 2 (A *ᵥ x - b)‖ ≤
        ‖WithLp.toLp 2 (A *ᵥ (truncatedSingularInverse U V σ *ᵥ b) - b)‖ →
          x = truncatedSingularInverse U V σ *ᵥ b := by
  let C : Matrix m r 𝕜 := A * V
  have hc : IsThinSVD C U (1 : Matrix r r 𝕜) σ := by
    refine ⟨h.left_orth, hasOrthonormalCols_one, h.pos, ?_⟩
    simp only [Matrix.conjTranspose_one, Matrix.mul_one]
    exact h.mul_right
  have hleft : moorePenroseInverse C * C = 1 := by
    simpa using hc.moorePenroseInverse_mul_eq
  have hinj : Function.Injective C.mulVec := by
    intro x y he
    have he' := congrArg (fun v => moorePenroseInverse C *ᵥ v) he
    simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using he'
  have hG : (Cᴴ * C).PosDef := Matrix.PosDef.conjTranspose_mul_self C hinj
  have hn : Cᴴ * C * moorePenroseInverse C = Cᴴ := by
    have he := congrArg Matrix.conjTranspose (mul_moorePenroseInverse_mul C)
    rw [Matrix.conjTranspose_mul, (mul_moorePenroseInverse_isHermitian C).eq] at he
    simpa only [Matrix.mul_assoc] using he
  let z := moorePenroseInverse C *ᵥ b
  have hz : (Cᴴ * C) *ᵥ z = Cᴴ *ᵥ b := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, hn]
  have hmin := quadraticObjective_minimizer_of_posDef hG hz
  have hVz : V *ᵥ z = truncatedSingularInverse U V σ *ᵥ b := by
    dsimp [z]
    rw [hc.moorePenroseInverse_eq]
    simp only [Matrix.one_mul, ← Matrix.mulVec_mulVec, truncatedSingularInverse]
  have hobj (w : r → 𝕜) : ‖WithLp.toLp 2 (C *ᵥ w - b)‖ ^ 2 =
      2 * quadraticObjective (Cᴴ * C) (Cᴴ *ᵥ b) w + ‖WithLp.toLp 2 b‖ ^ 2 := by
    simpa [tikhonovObjective, tikhonovNormal] using
      tikhonovObjective_eq_quadraticObjective C b 0 w
  refine ⟨⟨z, hVz⟩, ?_, ?_⟩
  · rintro x ⟨w, rfl⟩
    rw [← hVz]
    change ‖WithLp.toLp 2 (A *ᵥ (V *ᵥ z) - b)‖ ≤ ‖WithLp.toLp 2 (A *ᵥ (V *ᵥ w) - b)‖
    rw [Matrix.mulVec_mulVec z A V, Matrix.mulVec_mulVec w A V]
    change ‖WithLp.toLp 2 (C *ᵥ z - b)‖ ≤ ‖WithLp.toLp 2 (C *ᵥ w - b)‖
    have hsq : ‖WithLp.toLp 2 (C *ᵥ z - b)‖ ^ 2 ≤
        ‖WithLp.toLp 2 (C *ᵥ w - b)‖ ^ 2 := by
      rw [hobj z, hobj w]
      linarith [hmin.1 w]
    nlinarith [norm_nonneg (WithLp.toLp 2 (C *ᵥ z - b)),
      norm_nonneg (WithLp.toLp 2 (C *ᵥ w - b))]
  · rintro x ⟨w, rfl⟩ hw
    rw [← hVz] at hw
    change ‖WithLp.toLp 2 (A *ᵥ (V *ᵥ w) - b)‖ ≤ ‖WithLp.toLp 2 (A *ᵥ (V *ᵥ z) - b)‖ at hw
    rw [Matrix.mulVec_mulVec w A V, Matrix.mulVec_mulVec z A V] at hw
    change ‖WithLp.toLp 2 (C *ᵥ w - b)‖ ≤ ‖WithLp.toLp 2 (C *ᵥ z - b)‖ at hw
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [hobj w, hobj z] at hsq
    have hwz : w = z := hmin.2 w (by linarith)
    rw [hwz]
    exact hVz

/-- Bias and propagated noise in TSVD are exactly orthogonal. The identity
holds for arbitrary retained positive singular families.
atlas: truncated-svd-regularization (partial) -/
theorem IsSingularTripletFamily.norm_truncatedSingularInverse_data_sub_sq
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSingularTripletFamily A U V σ) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (truncatedSingularInverse U V σ *ᵥ (A *ᵥ x + e) - x)‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - V * Vᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 (truncatedSingularInverse U V σ *ᵥ e)‖ ^ 2 := by
  let noise := truncatedSingularInverse U V σ *ᵥ e
  let bias := (1 - V * Vᴴ) *ᵥ x
  have hV : Vᴴ *ᵥ bias = 0 := by
    dsimp [bias]
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      h.right_orth.conjTranspose_mul_self, Matrix.one_mul, sub_self, Matrix.zero_mulVec]
  have hcross : star noise ⬝ᵥ bias = 0 := by
    dsimp [noise, truncatedSingularInverse]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hV, dotProduct_zero]
  have hother : star bias ⬝ᵥ noise = 0 := by
    have he := congrArg star hcross
    simpa only [← Matrix.star_dotProduct_star, star_star, star_zero, dotProduct_comm] using he
  have herr : truncatedSingularInverse U V σ *ᵥ (A *ᵥ x + e) - x = noise - bias := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h.truncatedSingularInverse_mul]
    dsimp [noise, bias]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [herr]
  change ‖WithLp.toLp 2 (noise - bias)‖ ^ 2 =
    ‖WithLp.toLp 2 bias‖ ^ 2 + ‖WithLp.toLp 2 noise‖ ^ 2
  simp only [norm_toLp_sq_eq_re_star_dotProduct, star_sub, sub_dotProduct, dotProduct_sub,
    hcross, hother, map_sub, map_zero, sub_zero, zero_sub, map_neg]
  ring

/-- The exact inverse norm of a leading retained block is the reciprocal
of its smallest retained singular value (zero-indexed at `k-1`).
atlas: truncated-svd-regularization (partial) -/
theorem IsSingularTripletFamily.specNorm_truncatedSingularInverse {k : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin k) 𝕜} {V : Matrix n (Fin k) 𝕜}
    (h : IsSingularTripletFamily A U V (fun i => singularValues A i)) (hk : 0 < k) :
    specNorm (truncatedSingularInverse U V (fun i => singularValues A i)) =
      1 / singularValues A (k - 1) := by
  rw [truncatedSingularInverse,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols h.left_orth,
    specNorm_mul_left_of_hasOrthonormalCols h.right_orth]
  open scoped Matrix.Norms.L2Operator in
    rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    have hlast := h.pos (⟨k - 1, by omega⟩ : Fin k)
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      rw [norm_inv, RCLike.norm_ofReal, abs_of_pos (h.pos i), ← one_div]
      exact one_div_le_one_div_of_le hlast (singularValues_antitone A (by have := i.isLt; omega))
    · have hi := norm_le_pi_norm (fun i : Fin k => ((singularValues A i)⁻¹ : 𝕜))
        (⟨k - 1, by omega⟩ : Fin k)
      simpa [norm_inv, RCLike.norm_ofReal, abs_of_pos hlast, one_div] using hi

/-- The sharp bias/noise inequality for a leading TSVD block.
atlas: truncated-svd-regularization (partial) -/
theorem IsSingularTripletFamily.norm_truncatedSingularInverse_data_sub_sq_le {k : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin k) 𝕜} {V : Matrix n (Fin k) 𝕜}
    (h : IsSingularTripletFamily A U V (fun i => singularValues A i)) (hk : 0 < k)
    (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (truncatedSingularInverse U V (fun i => singularValues A i) *ᵥ
      (A *ᵥ x + e) - x)‖ ^ 2 ≤
      ‖WithLp.toLp 2 ((1 - V * Vᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 e‖ ^ 2 / singularValues A (k - 1) ^ 2 := by
  rw [h.norm_truncatedSingularInverse_data_sub_sq]
  have hb : ‖WithLp.toLp 2 (truncatedSingularInverse U V (fun i => singularValues A i) *ᵥ e)‖ ≤
      (1 / singularValues A (k - 1)) * ‖WithLp.toLp 2 e‖ := by
    rw [← h.specNorm_truncatedSingularInverse hk]
    open scoped Matrix.Norms.L2Operator in
      exact (truncatedSingularInverse U V (fun i => singularValues A i)).l2_opNorm_mulVec
        (WithLp.toLp 2 e)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  apply add_le_add le_rfl
  simpa [mul_pow, div_pow, div_eq_mul_inv, mul_comm] using hs

end NLAlib
