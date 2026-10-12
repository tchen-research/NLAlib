import NLAlib.ForMathlib.Analysis.OrthonormalEigenline
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# An orthonormal Schur basis with prescribed characteristic-root order

Choose the requested first root, remove its eigenline, and cancel the
corresponding characteristic factor before dimension induction.
Source: Horn–Johnson (2013), Theorem 2.3.1.
-/

noncomputable section
open Module Polynomial
open scoped InnerProductSpace

namespace NLAlib

/-- Every complete ordering of the characteristic roots of a real or complex
endomorphism is realized by an orthonormal upper triangularizing basis.
Source: Horn–Johnson (2013), Theorem 2.3.1; repeated roots and dimension zero
are allowed. -/
theorem exists_orthonormalBasis_upper_triangular_with_charpoly
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (k : ℕ) (f : Module.End 𝕜 E) (hk : finrank 𝕜 E = k)
    (d : Fin k → 𝕜) (hchar : f.charpoly = ∏ i, (X - C (d i))) :
    ∃ b : OrthonormalBasis (Fin k) 𝕜 E,
      (∀ i j, j < i → inner 𝕜 (b i) (f (b j)) = 0) ∧
      ∀ i, inner 𝕜 (b i) (f (b i)) = d i := by
  classical
  induction k generalizing E with
  | zero =>
    let b : OrthonormalBasis (Fin 0) 𝕜 E :=
      (stdOrthonormalBasis 𝕜 E).reindex (finCongr hk)
    exact ⟨b, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    have hμ : f.HasEigenvalue (d 0) := by
      apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      rw [hchar]
      simp only [Polynomial.IsRoot, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k + 1)))
      simp
    obtain ⟨x, hx, hxne⟩ := hμ.exists_hasEigenvector
    have hfx : f x = d 0 • x := Module.End.mem_eigenspace_iff.mp hx
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    let u : E := (‖x‖⁻¹ : 𝕜) • x
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_nonneg hxnorm.le, inv_mul_cancel₀ hxnorm.ne']
    have hune : u ≠ 0 := by intro h; simp [h] at hu
    have hfu : f u = d 0 • u := by simp only [u, map_smul, hfx, smul_smul, mul_comm]
    let W : Submodule 𝕜 E := (𝕜 ∙ u)ᗮ
    have hWdim : finrank 𝕜 W = k := by
      have hdim := (𝕜 ∙ u).finrank_add_finrank_orthogonal
      rw [finrank_span_singleton hune, hk] at hdim
      dsimp [W]
      omega
    let Cμ : Module.End 𝕜 W := W.orthogonalProjectionOnto.toLinearMap.comp (f.comp W.subtype)
    have hfactor : f.charpoly = (X - C (d 0)) * Cμ.charpoly :=
      charpoly_eq_X_sub_C_mul_orthogonal_compression f hu hfu hk
    have hCchar : Cμ.charpoly = ∏ i : Fin k, (X - C (d i.succ)) := by
      apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (d 0))
      rw [← hfactor, hchar, Fin.prod_univ_succ]
    obtain ⟨bW, htriW, hdiagW⟩ := ih Cμ hWdim (fun i => d i.succ) hCchar
    obtain ⟨b, hb₀, hbS⟩ := exists_orthonormalBasis_cons hk u hu bW
    refine ⟨b, ?_, ?_⟩
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        rw [hb₀, hfu, inner_smul_right]
        have hiu : inner 𝕜 (b i) u = 0 := by
          rw [← hb₀]
          exact b.orthonormal.inner_eq_zero (ne_of_gt hij)
        rw [hiu, mul_zero]
      · refine Fin.cases ?_ (fun i => ?_) i
        · intro hij
          exact (not_lt_of_ge (Fin.zero_le _)) hij |>.elim
        · intro hij
          rw [hbS, hbS]
          simpa only [Cμ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.subtype_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using
              htriW i j (Fin.succ_lt_succ_iff.mp hij)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [hb₀, hfu, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
        simp
      · rw [hbS]
        simpa only [Cμ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Submodule.subtype_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using hdiagW i

end NLAlib
