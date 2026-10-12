import NLAlib.ForMathlib.Analysis.OrthonormalCons
import NLAlib.ForMathlib.LinearAlgebra.PencilLine

/-!
# Two orthonormal bases simultaneously triangularizing a complex pencil

One common image line is removed from the domain and codomain independently.
Their orthogonal complements have equal dimension, allowing induction for
every complex square pencil, including singular and zero pencils.
-/

noncomputable section
open Module
open scoped InnerProductSpace
namespace NLAlib

/-- A square complex pencil admits unit domain and image vectors whose two
images are scalar multiples of the image vector. Zero images are allowed.
Horn–Johnson 2013, Theorem 2.6.1; QZ deflation helper. -/
theorem exists_unit_pencil_image_line {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [Nontrivial F]
    (A B : E →ₗ[ℂ] F) (hdim : finrank ℂ E = finrank ℂ F) :
    ∃ u : E, ∃ v : F, ∃ a b : ℂ,
      ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ A u = a • v ∧ B u = b • v := by
  obtain ⟨x, y, a, b, hx, hy, hAx, hBx⟩ := exists_nonzero_pencil_image_line A B hdim
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let u := (‖x‖ : ℂ)⁻¹ • x
  let v := (‖y‖ : ℂ)⁻¹ • y
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hxn.le, inv_mul_cancel₀ hxn.ne']
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hyn.le, inv_mul_cancel₀ hyn.ne']
  refine ⟨u, v, (‖x‖ : ℂ)⁻¹ * a * ‖y‖, (‖x‖ : ℂ)⁻¹ * b * ‖y‖, hu, hv, ?_, ?_⟩
  · simp only [u, v, map_smul, hAx, smul_smul, mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hyn.ne'), mul_one]
  · simp only [u, v, map_smul, hBx, smul_smul, mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hyn.ne'), mul_one]

/-- Every pair of complex maps between finite-dimensional spaces of equal
dimension is upper triangular in a pair of orthonormal bases. The maps may
be singular, the pencil may be identically singular, and dimension zero is
included. Horn–Johnson 2013, Theorem 2.6.1; derivations §gen:schur. -/
theorem exists_orthonormalBases_pencil_upper_triangular {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (k : ℕ) (A B : E →ₗ[ℂ] F) (hE : finrank ℂ E = k) (hF : finrank ℂ F = k) :
    ∃ e : OrthonormalBasis (Fin k) ℂ E, ∃ f : OrthonormalBasis (Fin k) ℂ F,
      (∀ i j, j < i → inner ℂ (f i) (A (e j)) = 0) ∧
      (∀ i j, j < i → inner ℂ (f i) (B (e j)) = 0) := by
  classical
  induction k generalizing E F with
  | zero =>
    exact ⟨(stdOrthonormalBasis ℂ E).reindex (finCongr hE),
      (stdOrthonormalBasis ℂ F).reindex (finCongr hF),
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    have : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hE]; omega)
    have : Nontrivial F := Module.finrank_pos_iff.mp (by rw [hF]; omega)
    obtain ⟨u, v, a, b, hu, hv, hAu, hBu⟩ := exists_unit_pencil_image_line A B (hE.trans hF.symm)
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
    let E' : Submodule ℂ E := (ℂ ∙ u)ᗮ
    let F' : Submodule ℂ F := (ℂ ∙ v)ᗮ
    have hE' : finrank ℂ E' = k := by
      have hh := (ℂ ∙ u).finrank_add_finrank_orthogonal
      rw [finrank_span_singleton hu0, hE] at hh
      dsimp [E']; omega
    have hF' : finrank ℂ F' = k := by
      have hh := (ℂ ∙ v).finrank_add_finrank_orthogonal
      rw [finrank_span_singleton hv0, hF] at hh
      dsimp [F']; omega
    let comp (L : E →ₗ[ℂ] F) : E' →ₗ[ℂ] F' :=
      F'.orthogonalProjectionOnto.toLinearMap.comp (L.comp E'.subtype)
    obtain ⟨e', f', hA', hB'⟩ := ih (comp A) (comp B) hE' hF'
    obtain ⟨e, he0, heS⟩ := exists_orthonormalBasis_cons hE u hu e'
    obtain ⟨f, hf0, hfS⟩ := exists_orthonormalBasis_cons hF v hv f'
    have hCoeff (L : E →ₗ[ℂ] F) (c : ℂ) (hLu : L u = c • v)
        (hL' : ∀ i j, j < i → inner ℂ (f' i) (comp L (e' j)) = 0) :
        ∀ i j, j < i → inner ℂ (f i) (L (e j)) = 0 := by
      intro i j hij
      revert hij
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hi
        rw [he0, hLu, inner_smul_right]
        have hfv : inner ℂ (f i) v = 0 := by
          rw [← hf0]
          exact f.orthonormal.inner_eq_zero (ne_of_gt hi)
        rw [hfv, mul_zero]
      · refine Fin.cases ?_ (fun i => ?_) i
        · intro hi
          exact (not_lt_of_ge (Fin.zero_le _)) hi |>.elim
        · intro hi
          rw [hfS, heS]
          have hh := hL' i j (Fin.succ_lt_succ_iff.mp hi)
          simpa only [comp, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.subtype_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using hh
    exact ⟨e, f, hCoeff A a hAu hA', hCoeff B b hBu hB'⟩

end NLAlib
