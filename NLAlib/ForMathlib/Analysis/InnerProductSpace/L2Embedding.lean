import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometric extension along an embedding of Hilbert coordinate indices

An injection of coordinate types gives an actual isometry of their scalar
ℓ² spaces, by extending coefficients by zero. Its native adjoint restricts
coordinates along the injection. Empty coordinate types are included.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct

namespace lp

variable {𝕜 ι κ : Type*} [RCLike 𝕜]

private theorem orthonormal_single_embedding (e : ι ↪ κ) :
    Orthonormal 𝕜 (fun i => (lp.single 2 (e i) (1 : 𝕜) : ℓ²(κ, 𝕜))) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply, e.injective.eq_iff]

/-- An injection of indices induces the zero-extension linear isometry of
their scalar ℓ² spaces. No countability or nonempty-index assumption is needed. -/
def embeddingLinearIsometry (e : ι ↪ κ) : ℓ²(ι, 𝕜) →ₗᵢ[𝕜] ℓ²(κ, 𝕜) := by
  classical
  exact (orthonormal_single_embedding (𝕜 := 𝕜) e).orthogonalFamily.linearIsometry

/-- Zero extension sends a single coordinate to the corresponding injected
coordinate, with the same coefficient. -/
@[simp]
theorem embeddingLinearIsometry_apply_single (e : ι ↪ κ) (i : ι) (z : 𝕜) :
    embeddingLinearIsometry (𝕜 := 𝕜) e (lp.single 2 i z) = lp.single 2 (e i) z := by
  classical
  unfold embeddingLinearIsometry
  rw [OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply]
  ext k
  by_cases hk : k = e i <;> simp [lp.single_apply, hk]

/-- The native Hilbert adjoint of zero extension restricts the coordinate
function along the original index injection. -/
@[simp]
theorem embeddingLinearIsometry_adjoint_apply (e : ι ↪ κ) (f : ℓ²(κ, 𝕜)) (i : ι) :
    ((embeddingLinearIsometry (𝕜 := 𝕜) e).toContinuousLinearMap.adjoint f) i = f (e i) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right
    (embeddingLinearIsometry (𝕜 := 𝕜) e).toContinuousLinearMap (lp.single 2 i (1 : 𝕜)) f
  simpa [embeddingLinearIsometry_apply_single, lp.inner_single_left, RCLike.inner_apply] using h

end lp
