import NLAlib.Matrix.Subspaces.OrthogonalProducts
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Flexible Arnoldi residuals and least-squares minimization

For a realized relation `A Z = V H` with orthonormal `V`, the full
residual of `x₀ + Z y` is the isometric image of `g - H y`. This
identifies reduced least-squares minimizers with residual minimizers on
the whole trial space, including rank-deficient trial and reduced matrices.
Source: Saad (2003), §9.4.1, equations (9.22)--(9.26), Proposition 9.2.
Atlas: `flexible-gmres-residual-minimization`.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq q]
variable {A : Matrix n n 𝕜} {Z : Matrix n p 𝕜} {V : Matrix n q 𝕜}
variable {H : Matrix q p 𝕜} {b x₀ : n → 𝕜} {g : q → 𝕜}

omit [DecidableEq q] in
/-- A realized flexible Arnoldi relation gives the full vector residual.
Source: Saad (2003), §9.4.1; helper for
`flexible-gmres-residual-minimization`. -/
theorem sub_mulVec_add_mulVec_eq_mulVec_sub_of_mul_eq_mul
    (hAZ : A * Z = V * H) (hr : b - A *ᵥ x₀ = V *ᵥ g) (y : p → 𝕜) :
    b - A *ᵥ (x₀ + Z *ᵥ y) = V *ᵥ (g - H *ᵥ y) := by
  rw [Matrix.mulVec_add, ← sub_sub, hr, Matrix.mulVec_mulVec, hAZ,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]

/-- Orthonormal flexible Arnoldi coordinates preserve the exact residual
2-norm. No independence of `Z` or invertibility of `A` is required.
Source: Saad (2003), equations (9.22)--(9.26), Proposition 9.2.
atlas: flexible-gmres-residual-minimization (partial) -/
theorem HasOrthonormalCols.norm_sub_mulVec_add_mulVec_eq_of_mul_eq_mul
    (hV : HasOrthonormalCols V) (hAZ : A * Z = V * H)
    (hr : b - A *ᵥ x₀ = V *ᵥ g) (y : p → 𝕜) :
    ‖WithLp.toLp 2 (b - A *ᵥ (x₀ + Z *ᵥ y))‖ =
      ‖WithLp.toLp 2 (g - H *ᵥ y)‖ := by
  rw [sub_mulVec_add_mulVec_eq_mulVec_sub_of_mul_eq_mul hAZ hr]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_toLp_sq_eq_re_star_dotProduct,
    star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hV,
    norm_toLp_sq_eq_re_star_dotProduct]

/-- Reduced least-squares minimization is equivalent to full residual
minimization on the affine trial space `x₀ + range Z`.
Source: Saad (2003), Proposition 9.2; the theorem applies equally to
varying, nonlinear or inexact preconditioners once their realized
Arnoldi relation is supplied.
atlas: flexible-gmres-residual-minimization (partial) -/
theorem HasOrthonormalCols.forall_norm_sub_mulVec_add_mulVec_le_iff
    (hV : HasOrthonormalCols V) (hAZ : A * Z = V * H)
    (hr : b - A *ᵥ x₀ = V *ᵥ g) (y : p → 𝕜) :
    (∀ y' : p → 𝕜, ‖WithLp.toLp 2 (g - H *ᵥ y)‖ ≤
      ‖WithLp.toLp 2 (g - H *ᵥ y')‖) ↔
    ∀ z ∈ LinearMap.range Z.mulVecLin,
      ‖WithLp.toLp 2 (b - A *ᵥ (x₀ + Z *ᵥ y))‖ ≤
        ‖WithLp.toLp 2 (b - A *ᵥ (x₀ + z))‖ := by
  constructor
  · intro hy z hz
    obtain ⟨y', rfl⟩ := hz
    simp only [Matrix.mulVecLin_apply]
    rw [hV.norm_sub_mulVec_add_mulVec_eq_of_mul_eq_mul hAZ hr,
      hV.norm_sub_mulVec_add_mulVec_eq_of_mul_eq_mul hAZ hr]
    exact hy y'
  · intro hy y'
    have h := hy (Z *ᵥ y') ⟨y', rfl⟩
    simpa only [hV.norm_sub_mulVec_add_mulVec_eq_of_mul_eq_mul hAZ hr] using h

/-- Every finite-dimensional reduced least-squares problem attains its
minimum, so a realized flexible Arnoldi relation has a full residual
minimizer on its affine trial space. Empty and rank-deficient reduced
systems are included. Source: Saad (2003), Proposition 9.2, with
finite-dimensional orthogonal projection providing attainment.
atlas: flexible-gmres-residual-minimization (partial) -/
theorem HasOrthonormalCols.exists_norm_sub_mulVec_add_mulVec_le
    (hV : HasOrthonormalCols V) (hAZ : A * Z = V * H)
    (hr : b - A *ᵥ x₀ = V *ᵥ g) :
    ∃ y : p → 𝕜, ∀ z ∈ LinearMap.range Z.mulVecLin,
      ‖WithLp.toLp 2 (b - A *ᵥ (x₀ + Z *ᵥ y))‖ ≤
        ‖WithLp.toLp 2 (b - A *ᵥ (x₀ + z))‖ := by
  classical
  let L : EuclideanSpace 𝕜 p →ₗ[𝕜] EuclideanSpace 𝕜 q := H.toEuclideanLin
  let S : Submodule 𝕜 (EuclideanSpace 𝕜 q) := LinearMap.range L
  obtain ⟨u, hu⟩ := S.starProjection_apply_mem (WithLp.toLp 2 g)
  refine ⟨u.ofLp, (hV.forall_norm_sub_mulVec_add_mulVec_le_iff hAZ hr _).mp ?_⟩
  intro y
  change ‖(WithLp.toLp 2 g : EuclideanSpace 𝕜 q) - L u‖ ≤
    ‖(WithLp.toLp 2 g : EuclideanSpace 𝕜 q) - L (WithLp.toLp 2 y)‖
  rw [hu, Submodule.starProjection_minimal]
  refine ciInf_le (f := fun w : S => ‖(WithLp.toLp 2 g : EuclideanSpace 𝕜 q) - w‖)
    ?_ ⟨L (WithLp.toLp 2 y), ⟨_, rfl⟩⟩
  exact ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩

end NLAlib
