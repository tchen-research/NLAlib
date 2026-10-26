import NLAlib.Krylov.Solvers.GMRESIterate

/-!
# Petrov--Galerkin characterization of real and complex GMRES

The residual is orthogonal to the image of the Krylov space. Conversely, this
orthogonality implies residual minimality by Pythagoras, over either scalar field.
Source: Saad (2003), Proposition 5.3 and Section 6.5.1.
atlas: gmres-def (partial)
-/

noncomputable section
open scoped Matrix InnerProductSpace
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜} {c x₀ x : n → 𝕜} {q : ℕ}

/-- The GMRES residual is orthogonal to the image of the Krylov space, with the
Hermitian inner product for complex data.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.star_dotProduct_eq_zero (hx : IsGMRESIterate A c x₀ q x)
    {z : n → 𝕜} (hz : z ∈ krylovSpace A (c - A *ᵥ x₀) q) :
    star (A *ᵥ z) ⬝ᵥ (c - A *ᵥ x) = 0 := by
  let X := krylovMatrix A (c - A *ᵥ x₀) q
  let B := A * X
  have hzX : z ∈ LinearMap.range X.mulVecLin := (range_krylovMatrix A _ q).symm ▸ hz
  obtain ⟨v, hv⟩ := hzX
  change X *ᵥ v = z at hv
  have hBP : Bᴴ * rangeProjector B = Bᴴ := by
    have h := congrArg Matrix.conjTranspose (rangeProjector_mul B)
    simpa only [Matrix.conjTranspose_mul, (rangeProjector_isHermitian B).eq] using h
  have hzero : Bᴴ *ᵥ ((c - A *ᵥ x₀) - rangeProjector B *ᵥ (c - A *ᵥ x₀)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hBP, sub_self]
  rw [hx.residual_eq_rangeProjector, ← hv, Matrix.mulVec_mulVec]
  change star (B *ᵥ v) ⬝ᵥ ((c - A *ᵥ x₀) - rangeProjector B *ᵥ (c - A *ᵥ x₀)) = 0
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hzero, dotProduct_zero]

/-- Petrov--Galerkin orthogonality is equivalent to GMRES minimality over real or
complex scalars. Singular matrices and the zero Krylov space are included.
atlas: gmres-def (partial) -/
theorem isGMRESIterate_iff_forall_star_dotProduct_eq_zero :
    IsGMRESIterate A c x₀ q x ↔ x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q ∧
      ∀ z ∈ krylovSpace A (c - A *ᵥ x₀) q, star (A *ᵥ z) ⬝ᵥ (c - A *ᵥ x) = 0 := by
  refine ⟨fun hx => ⟨hx.1, fun _ hz => hx.star_dotProduct_eq_zero hz⟩, ?_⟩
  rintro ⟨hx, ho⟩
  refine ⟨hx, fun y hy => ?_⟩
  have hd := (krylovSpace A (c - A *ᵥ x₀) q).sub_mem hy hx
  have h0 := ho _ hd
  have hi : ⟪WithLp.toLp 2 (c - A *ᵥ x),
      WithLp.toLp 2 (A *ᵥ (y - (x - x₀)))⟫_𝕜 = 0 := by
    rw [inner_eq_zero_symm]
    simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using h0
  have hr : c - A *ᵥ (x₀ + y) = (c - A *ᵥ x) - A *ᵥ (y - (x - x₀)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  dsimp only
  rw [← norm_toLp_sq_eq_re_star_dotProduct, ← norm_toLp_sq_eq_re_star_dotProduct, hr]
  change ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ^ 2 ≤
    ‖WithLp.toLp 2 (c - A *ᵥ x) - WithLp.toLp 2 (A *ᵥ (y - (x - x₀)))‖ ^ 2
  rw [norm_sub_sq (𝕜 := 𝕜), hi, map_zero, mul_zero, sub_zero]
  exact le_add_of_nonneg_right (sq_nonneg _)

end NLAlib
