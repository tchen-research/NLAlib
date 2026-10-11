import NLAlib.LowRank.ComplexSubspaceConvergence
import NLAlib.Matrix.ComplexEmbedding

/-!
# Individual complex subspace-iteration angles

Actual Hilbert orthogonal projections define vector-to-subspace tangents.
Orthogonal graph competitors prove the corrected individual eigenvector rates
whose initial factors are graph-column norms. Source: manuscript `sa:subspace`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- The tangent from a complex vector to an actual complex column space is its
orthogonal residual norm divided by its projection norm.
Source: manuscript `sa:subspace`, individual-angle clause. -/
def complexVectorTangentToColumns (B : Matrix n k ℂ) (u : EuclideanSpace ℂ n) : ℝ :=
  ‖u - (complexColumnSpace B).starProjection u‖ / ‖(complexColumnSpace B).starProjection u‖

omit [DecidableEq n] in
/-- An orthogonal graph competitor bounds the actual complex vector-to-subspace
tangent. Source: manuscript `sa:subspace`, individual-angle comparison. -/
theorem complexVectorTangentToColumns_le_of_orthogonal_competitor
    (B : Matrix n k ℂ) {u w : EuclideanSpace ℂ n} (hu : ‖u‖ = 1)
    (huw : inner ℂ u w = 0) (hw : u + w ∈ complexColumnSpace B) :
    complexVectorTangentToColumns B u ≤ ‖w‖ := by
  let S := complexColumnSpace B
  have hpv : inner ℂ (S.starProjection u) (u + w) = 1 := by
    rw [S.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff (K := S)).mpr hw,
      inner_add_right, huw, add_zero, inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hvv : ‖u + w‖ ^ 2 = 1 + ‖w‖ ^ 2 := by
    simpa only [← pow_two, hu, one_pow] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u w huw)
  have hcs : 1 ≤ ‖S.starProjection u‖ ^ 2 * (1 + ‖w‖ ^ 2) := by
    have hc := norm_inner_le_norm (𝕜 := ℂ) (S.starProjection u) (u + w)
    rw [hpv, norm_one] at hc
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hc 2
    simpa only [one_pow, mul_pow, hvv] using hs
  have hpp : 0 < ‖S.starProjection u‖ := by
    by_contra h
    have hz : ‖S.starProjection u‖ = 0 :=
      le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [hz, zero_pow two_ne_zero, zero_mul] at hcs
    linarith
  have hsplit := S.norm_sq_eq_add_norm_sq_starProjection u
  rw [hu, one_pow, S.starProjection_orthogonal_val] at hsplit
  unfold complexVectorTangentToColumns
  change ‖u - S.starProjection u‖ / ‖S.starProjection u‖ ≤ ‖w‖
  apply (div_le_iff₀ hpp).2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  nlinarith

omit [DecidableEq n] in
/-- Complex orthonormal columns preserve actual Euclidean vector norms.
Source: the Gram identity; supports manuscript `sa:subspace`. -/
theorem norm_toLp_mulVec_eq_of_conjTranspose_mul_eq_one
    {U : Matrix n k ℂ} (hU : Uᴴ * U = 1) (z : k → ℂ) :
    ‖(WithLp.toLp 2 (U *ᵥ z) : EuclideanSpace ℂ n)‖ =
      ‖(WithLp.toLp 2 z : EuclideanSpace ℂ k)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_toLp_sq_eq_re_star_dotProduct, norm_toLp_sq_eq_re_star_dotProduct]
  have hh : star z ⬝ᵥ ((Uᴴ * U) *ᵥ z) = star (U *ᵥ z) ⬝ᵥ (U *ᵥ z) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
      star_star]
  rw [← hh, hU, Matrix.one_mulVec]

omit [DecidableEq n] in
/-- An actual complex graph column bounds its leading eigenvector's tangent to
any containing complex column space. Source: manuscript `sa:subspace`, corrected
individual-angle factor. -/
theorem complexVectorTangentToColumns_graph_col_le
    {l : Type*} [Fintype l] [DecidableEq l] (B : Matrix n l ℂ)
    {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (F : Matrix r k ℂ)
    (hRange : complexColumnSpace (U₁ + U₂ * F) ≤ complexColumnSpace B) (i : k) :
    complexVectorTangentToColumns B (WithLp.toLp 2 (U₁.col i)) ≤
      ‖(WithLp.toLp 2 (F.col i) : EuclideanSpace ℂ r)‖ := by
  let e : k → ℂ := Pi.single i 1
  have he : U₁.col i = U₁ *ᵥ e := by simp [e]
  have hu : ‖(WithLp.toLp 2 (U₁.col i) : EuclideanSpace ℂ n)‖ = 1 := by
    rw [he, norm_toLp_mulVec_eq_of_conjTranspose_mul_eq_one hU₁]
    simp [e]
  have horth : inner ℂ (WithLp.toLp 2 (U₁.col i) : EuclideanSpace ℂ n)
      (WithLp.toLp 2 (U₂ *ᵥ F.col i)) = 0 := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, he]
    have hh : star e ⬝ᵥ ((U₁ᴴ * U₂) *ᵥ F.col i) =
        star (U₁ *ᵥ e) ⬝ᵥ (U₂ *ᵥ F.col i) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_conjTranspose, star_star]
    rw [← hh, hU, Matrix.zero_mulVec, dotProduct_zero]
  have hw : (WithLp.toLp 2 (U₁.col i) : EuclideanSpace ℂ n) +
      WithLp.toLp 2 (U₂ *ᵥ F.col i) ∈ complexColumnSpace B := by
    apply hRange
    refine ⟨WithLp.toLp 2 e, ?_⟩
    simp only [Matrix.toLpLin_apply, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, WithLp.toLp_add]
    simp [e]
  exact (complexVectorTangentToColumns_le_of_orthogonal_competitor B hu horth hw).trans_eq
    (norm_toLp_mulVec_eq_of_conjTranspose_mul_eq_one hU₂ _)

/-- Each complex graph column contracts at its own leading eigenvalue magnitude.
Source: manuscript `sa:subspace`, individual-rate clause. -/
theorem norm_complex_graph_col_le_of_diagonal
    (L₂ : Matrix r r ℂ) (F : Matrix r k ℂ) (eig : k → ℂ) (t : ℕ) (i : k) :
    ‖(WithLp.toLp 2 ((L₂ ^ t * F * (Matrix.diagonal fun j => (eig j)⁻¹) ^ t).col i) :
      EuclideanSpace ℂ r)‖ ≤ (‖L₂‖ / ‖eig i‖) ^ t *
        ‖(WithLp.toLp 2 (F.col i) : EuclideanSpace ℂ r)‖ := by
  have hcol : (L₂ ^ t * F * (Matrix.diagonal fun j => (eig j)⁻¹) ^ t).col i =
      ((eig i)⁻¹) ^ t • (L₂ ^ t *ᵥ F.col i) := by
    ext j
    change (L₂ ^ t * F * (Matrix.diagonal fun j => (eig j)⁻¹) ^ t) j i = _
    rw [Matrix.diagonal_pow, Matrix.mul_diagonal]
    change (L₂ ^ t * F) j i * ((eig i)⁻¹) ^ t =
      ((eig i)⁻¹) ^ t * (L₂ ^ t * F) j i
    ring
  have hp : ‖L₂ ^ t‖ ≤ ‖L₂‖ ^ t := by
    cases t with
    | zero => simpa only [pow_zero] using
        (norm_le_one_of_isHermitian_of_isIdempotentElem
          (P := (1 : Matrix r r ℂ)) Matrix.isHermitian_one
          (by change (1 : Matrix r r ℂ) * 1 = 1; exact Matrix.mul_one _))
    | succ t => exact norm_pow_le' L₂ (Nat.succ_pos t)
  have hv : ‖(WithLp.toLp 2 (L₂ ^ t *ᵥ F.col i) : EuclideanSpace ℂ r)‖ ≤
      ‖L₂‖ ^ t * ‖(WithLp.toLp 2 (F.col i) : EuclideanSpace ℂ r)‖ :=
    (Matrix.l2_opNorm_mulVec (L₂ ^ t) (WithLp.toLp 2 (F.col i))).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  rw [hcol, WithLp.toLp_smul, norm_smul, norm_pow, norm_inv]
  calc ‖eig i‖⁻¹ ^ t * ‖(WithLp.toLp 2 (L₂ ^ t *ᵥ F.col i) : EuclideanSpace ℂ r)‖ ≤
      ‖eig i‖⁻¹ ^ t * (‖L₂‖ ^ t * ‖(WithLp.toLp 2 (F.col i) : EuclideanSpace ℂ r)‖) :=
        mul_le_mul_of_nonneg_left hv (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

omit [Fintype n] [DecidableEq n] in
/-- Actual complex column spaces decrease under right multiplication.
Source: operator composition; supports manuscript `sa:subspace`. -/
theorem complexColumnSpace_mul_le {l : Type*} [Fintype l] [DecidableEq l]
    (B : Matrix n k ℂ) (R : Matrix k l ℂ) : complexColumnSpace (B * R) ≤ complexColumnSpace B := by
  change LinearMap.range (Matrix.toEuclideanLin (B * R)) ≤
    LinearMap.range (Matrix.toEuclideanLin B)
  rw [Matrix.toLpLin_mul_same]
  exact LinearMap.range_comp_le_range _ _

omit [Fintype n] [DecidableEq n] in
/-- A right-invertible coordinate change preserves the actual complex column space.
Source: manuscript `sa:graph`, right normalization. -/
theorem complexColumnSpace_mul_eq_of_right_inverse
    (B : Matrix n k ℂ) {R T : Matrix k k ℂ} (hRT : R * T = 1) :
    complexColumnSpace (B * R) = complexColumnSpace B := by
  apply le_antisymm (complexColumnSpace_mul_le B R)
  have he : B = (B * R) * T := by rw [Matrix.mul_assoc, hRT, Matrix.mul_one]
  conv_lhs => rw [he]
  exact complexColumnSpace_mul_le (B * R) T
/-- Every leading eigenvector has the corrected complex individual magnitude-gap
angle rate to the actual subspace iterate. The initial factor is its graph-column
norm. Source: manuscript `sa:subspace`, final clause; Saad (2011), §5.1.
atlas: subspace-iteration-convergence (partial) -/
theorem complexVectorTangentToColumns_subspaceIterate_le_of_diagonal
    {A : Matrix n n ℂ} {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (eig₁ : k → ℂ) (L₂ : Matrix r r ℂ)
    (hA₁ : A * U₁ = U₁ * Matrix.diagonal eig₁) (hA₂ : A * U₂ = U₂ * L₂)
    {Ω : Matrix n k ℂ} {Ω₁ R : Matrix k k ℂ} {Ω₂ : Matrix r k ℂ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    (hEigen : ∀ i, eig₁ i ≠ 0) (t : ℕ) (i : k) :
    complexVectorTangentToColumns (A ^ t * Ω) (WithLp.toLp 2 (U₁.col i)) ≤
      (‖L₂‖ / ‖eig₁ i‖) ^ t *
        ‖(WithLp.toLp 2 ((Ω₂ * R).col i) : EuclideanSpace ℂ r)‖ := by
  let Linv : Matrix k k ℂ := Matrix.diagonal fun i => (eig₁ i)⁻¹
  have hL : Matrix.diagonal eig₁ * Linv = 1 := by
    dsimp only [Linv]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact mul_inv_cancel₀ (hEigen j)
  have hpow : (Matrix.diagonal eig₁) ^ t * Linv ^ t = 1 := by
    have hc : Commute (Matrix.diagonal eig₁) Linv := by change (Matrix.diagonal eig₁) * Linv = Linv * (Matrix.diagonal eig₁); rw [hL, mul_eq_one_comm.1 hL]
    rw [← hc.mul_pow, hL, one_pow]
  have hY : A ^ t * Ω = U₁ * (Matrix.diagonal eig₁) ^ t * Ω₁ + U₂ * L₂ ^ t * Ω₂ := by
    rw [hΩ, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      pow_mul_eq_mul_pow_of_mul_eq hA₁, pow_mul_eq_mul_pow_of_mul_eq hA₂]
  have hN : A ^ t * Ω * (R * Linv ^ t) = U₁ + U₂ * (L₂ ^ t * Ω₂ * R * Linv ^ t) := by
    rw [hY, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ω₁, hR, Matrix.one_mul, hpow, Matrix.mul_one]
  have hRT : (R * Linv ^ t) * ((Matrix.diagonal eig₁) ^ t * Ω₁) = 1 := by
    have hpow' : Linv ^ t * (Matrix.diagonal eig₁) ^ t = 1 := mul_eq_one_comm.1 hpow
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Linv ^ t), hpow', Matrix.one_mul, mul_eq_one_comm.1 hR]
  have hSpace := complexColumnSpace_mul_eq_of_right_inverse (A ^ t * Ω) hRT
  rw [hN] at hSpace
  have hh := complexVectorTangentToColumns_graph_col_le (A ^ t * Ω) hU₁ hU₂ hU
    (L₂ ^ t * Ω₂ * R * Linv ^ t) hSpace.le i
  exact hh.trans (by simpa only [Matrix.mul_assoc] using
    norm_complex_graph_col_le_of_diagonal L₂ (Ω₂ * R) eig₁ t i)

/-- Complex subspace iteration satisfies both the largest principal-angle bound
and the corrected individual leading-eigenvector bounds. These are actual native
complex ranges and Hilbert projection tangents; the initial individual constants
are graph-column norms. Source: manuscript `sa:subspace-theorem` and its final
individual-angle clause; Saad (2011), §5.1. Empty blocks and all times are included.
atlas: subspace-iteration-convergence -/
theorem complexSubspaceTangent_and_complexVectorTangentToColumns_le
    {A : Matrix n n ℂ} {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (eig₁ : k → ℂ) (eig₂ : r → ℂ)
    (hA₁ : A * U₁ = U₁ * Matrix.diagonal eig₁)
    (hA₂ : A * U₂ = U₂ * Matrix.diagonal eig₂)
    {Ω : Matrix n k ℂ} {Ω₁ R : Matrix k k ℂ} {Ω₂ : Matrix r k ℂ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    {α : ℝ} (hα : 0 < α) (hgap : ∀ i, α ≤ ‖eig₁ i‖) (t : ℕ) :
    complexSubspaceTangent U₁ U₂ (complexSubspaceIterate A Ω t) ≤
        (‖Matrix.diagonal eig₂‖ / α) ^ t *
          complexSubspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) ∧
      ∀ i, complexVectorTangentToColumns (A ^ t * Ω) (WithLp.toLp 2 (U₁.col i)) ≤
        (‖Matrix.diagonal eig₂‖ / ‖eig₁ i‖) ^ t *
          ‖(WithLp.toLp 2 ((Ω₂ * R).col i) : EuclideanSpace ℂ r)‖ := by
  refine ⟨complexSubspaceTangent_complexSubspaceIterate_le_of_diagonal hU₁ hU₂ hU
    eig₁ eig₂ hA₁ hA₂ hΩ hR hα hgap t, ?_⟩
  have heig : ∀ i, eig₁ i ≠ 0 := by
    intro i hi
    have hh := hgap i
    rw [hi, norm_zero] at hh
    linarith
  exact fun i => complexVectorTangentToColumns_subspaceIterate_le_of_diagonal
    hU₁ hU₂ hU eig₁ _ hA₁ hA₂ hΩ hR heig t i

end NLAlib
