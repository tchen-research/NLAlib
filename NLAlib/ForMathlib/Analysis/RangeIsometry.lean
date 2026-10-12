import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Extending the isometry identified by equal norms

Two linear maps with the same pointwise norms differ by an ambient linear
isometry when their codomain is finite dimensional. Kernels are included.
-/

noncomputable section
namespace NLAlib

/-- Equal pointwise norms identify the two ranges isometrically, and the
range isometry extends to the entire finite-dimensional codomain. This
works over the real or complex field, including zero maps. Horn–Johnson
2013, Section 2.1; equal-Gram helper for complex CS. -/
theorem exists_linearIsometry_comp_eq_of_norm_eq {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A B : E →ₗ[𝕜] F) (h : ∀ x, ‖A x‖ = ‖B x‖) :
    ∃ U : F →ₗᵢ[𝕜] F, U.toLinearMap.comp B = A := by
  have hker : LinearMap.ker B ≤ LinearMap.ker A := by
    intro x hx
    apply norm_eq_zero.mp
    rw [h x, show B x = 0 from hx, norm_zero]
  let L₀ := (LinearMap.ker B).liftQ A hker
  let L₁ := L₀.comp B.quotKerEquivRange.symm.toLinearMap
  have happly (x : E) : L₁ ⟨B x, LinearMap.mem_range_self B x⟩ = A x := by
    change L₀ (B.quotKerEquivRange.symm (B.quotKerEquivRange (Submodule.Quotient.mk x))) = A x
    rw [LinearEquiv.symm_apply_apply]
    rfl
  let L : LinearMap.range B →ₗᵢ[𝕜] F :=
    { toLinearMap := L₁
      norm_map' := by
        intro y
        obtain ⟨x, hx⟩ := y.property
        have hy : y = ⟨B x, LinearMap.mem_range_self B x⟩ := Subtype.ext hx.symm
        rw [hy, happly]
        exact h x }
  refine ⟨L.extend, ?_⟩
  ext x
  exact (L.extend_apply ⟨B x, LinearMap.mem_range_self B x⟩).trans (happly x)

end NLAlib
