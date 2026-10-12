import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A common image line for a complex square pencil

Every square pencil has a nonzero domain vector whose two images lie in one
codomain line, including singular pencils and a common zero image.
-/

noncomputable section
open Module
namespace NLAlib

/-- Two complex linear maps between equal positive finite dimensions admit
nonzero vectors `x,y` with both images of `x` scalar multiples of `y`.
If the second map is singular choose a kernel vector; otherwise use an
eigenvector of its inverse times the first map. Horn–Johnson 2013,
Theorem 2.6.1; supports the singular-pencil QZ form. -/
theorem exists_nonzero_pencil_image_line {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F] [Nontrivial F]
    (A B : E →ₗ[ℂ] F) (hdim : finrank ℂ E = finrank ℂ F) :
    ∃ x : E, ∃ y : F, ∃ a b : ℂ,
      x ≠ 0 ∧ y ≠ 0 ∧ A x = a • y ∧ B x = b • y := by
  classical
  by_cases hB : Function.Injective B
  · let e := B.linearEquivOfInjective hB hdim
    let T : Module.End ℂ E := e.symm.toLinearMap.comp A
    obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
    obtain ⟨x, hx, hx0⟩ := ha.exists_hasEigenvector
    have hTx : T x = a • x := Module.End.mem_eigenspace_iff.mp hx
    have hAx := congrArg e hTx
    have hBx : B x ≠ 0 := fun h => hx0 (hB (h.trans B.map_zero.symm))
    refine ⟨x, B x, a, 1, hx0, hBx, ?_, by simp⟩
    simpa only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      map_smul, e, LinearMap.linearEquivOfInjective_apply] using hAx
  · have hKer : LinearMap.ker B ≠ ⊥ := fun h => hB (LinearMap.ker_eq_bot.mp h)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKer
    have hBx : B x = 0 := hx
    by_cases hAx : A x = 0
    · obtain ⟨y, hy⟩ := exists_ne (0 : F)
      exact ⟨x, y, 0, 0, hx0, hy, by simpa using hAx, by simpa using hBx⟩
    · exact ⟨x, A x, 1, 0, hx0, hAx, by simp, by simpa using hBx⟩

end NLAlib
