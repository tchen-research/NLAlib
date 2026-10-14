import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Kernel dimension of a composition

Restricting the second map to the kernel of the composition gives the usual
kernel-dimension subadditivity inequality. This supports the finite proof of
the geometric nonderogatory criterion without Jordan form.
-/

noncomputable section
namespace LinearMap

variable {K V W U : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable [AddCommGroup U] [Module K U]

/-- The kernel dimension of a composition is at most the sum of the two kernel dimensions. -/
theorem finrank_ker_comp_le (f : W →ₗ[K] U) (g : V →ₗ[K] W) :
    Module.finrank K (LinearMap.ker (f.comp g)) ≤
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g) := by
  let S := LinearMap.ker (f.comp g)
  let L := g.comp S.subtype
  have hr : LinearMap.range L ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  let J : LinearMap.ker L →ₗ[K] LinearMap.ker g :=
    { toFun := fun x => ⟨(x : S).val, x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hJ : Function.Injective J := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker g => z.val) hxy
  have hker := LinearMap.finrank_le_finrank_of_injective hJ
  have hrange := Submodule.finrank_mono hr
  have hdim := L.finrank_range_add_finrank_ker
  change Module.finrank K S ≤ _
  omega

end LinearMap
