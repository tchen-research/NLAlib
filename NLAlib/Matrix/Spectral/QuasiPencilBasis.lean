import NLAlib.Matrix.Spectral.QuasiTriangular
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Orthogonal pencil reduction from a quasitriangular basis

For an invertible second map, Gram–Schmidt applied to the images of a Schur
basis makes that second factor upper triangular and preserves the first
factor's quasitriangular pattern. A singular second map supplies a scalar
leading block through one kernel vector.
-/

noncomputable section
open Module
open scoped Matrix InnerProductSpace

namespace NLAlib

/-- A supplied quasitriangular basis for `B⁻¹A` gives a two-sided orthonormal
pencil form whose second factor is upper triangular and first factor is
upper quasitriangular. Source: Horn–Johnson (2013), Theorem 2.6.2;
Gram–Schmidt is applied to the `B`-images of the given basis. -/
theorem exists_orthonormalBasis_pencil_of_quasi_basis
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {k : ℕ} (A : E →ₗ[𝕜] F) (B : E ≃ₗ[𝕜] F)
    (e : OrthonormalBasis (Fin k) 𝕜 E) (hF : finrank 𝕜 F = k)
    (hT : IsUpperQuasiTriangular
      ((B.symm.toLinearMap.comp A).toMatrix e.toBasis e.toBasis)) :
    ∃ f : OrthonormalBasis (Fin k) 𝕜 F,
      IsUpperQuasiTriangular (A.toMatrix e.toBasis f.toBasis) ∧
      (B.toLinearMap.toMatrix e.toBasis f.toBasis).IsUpperTriangular := by
  let hdim : finrank 𝕜 F = Fintype.card (Fin k) := hF.trans (Fintype.card_fin k).symm
  let f := InnerProductSpace.gramSchmidtOrthonormalBasis hdim (fun i => B (e i))
  have hR : (B.toLinearMap.toMatrix e.toBasis f.toBasis).IsUpperTriangular := by
    have h := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular
      hdim (fun i => B (e i))
    intro i j hij
    simpa only [f, LinearMap.toMatrix_apply, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      LinearEquiv.coe_coe] using h (i := i) (j := j) hij
  have hcomp : B.toLinearMap.comp (B.symm.toLinearMap.comp A) = A := by
    ext x
    exact B.apply_symm_apply (A x)
  have hmat : A.toMatrix e.toBasis f.toBasis =
      B.toLinearMap.toMatrix e.toBasis f.toBasis *
        (B.symm.toLinearMap.comp A).toMatrix e.toBasis e.toBasis := by
    rw [← LinearMap.toMatrix_comp, hcomp]
  refine ⟨f, ?_, hR⟩
  rw [hmat]
  exact hT.upperTriangular_mul hR

/-- A singular second pencil map gives unit domain and image vectors with
its image zero and the first map's image on the chosen image line.
Horn–Johnson (2013), Theorem 2.6.2; a common zero image is allowed. -/
theorem exists_unit_pencil_image_line_of_not_injective
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Nontrivial F]
    (A B : E →ₗ[𝕜] F) (hB : ¬ Function.Injective B) :
    ∃ (u : E) (v : F) (a : 𝕜), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ A u = a • v ∧ B u = 0 := by
  classical
  have hker : B.ker ≠ ⊥ := fun h => hB (LinearMap.ker_eq_bot.mp h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hBx : B x = 0 := hx
  obtain ⟨y, c, hy, hAx⟩ : ∃ (y : F) (c : 𝕜), y ≠ 0 ∧ A x = c • y := by
    by_cases hAx : A x = 0
    · obtain ⟨y, hy⟩ := exists_ne (0 : F)
      exact ⟨y, 0, hy, by simp [hAx]⟩
    · exact ⟨A x, 1, hAx, by simp⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hynK : (‖y‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hyn.ne'
  let u := (‖x‖ : 𝕜)⁻¹ • x
  let v := (‖y‖ : 𝕜)⁻¹ • y
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hxn.le,
      inv_mul_cancel₀ hxn.ne']
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hyn.le,
      inv_mul_cancel₀ hyn.ne']
  refine ⟨u, v, (‖x‖ : 𝕜)⁻¹ * c * ‖y‖, hu, hv, ?_, ?_⟩
  · simp only [u, v, map_smul, hAx, smul_smul, mul_assoc,
      mul_inv_cancel₀ hynK, mul_one]
  · simp only [u, map_smul, hBx, smul_zero]

end NLAlib
