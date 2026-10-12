import NLAlib.ForMathlib.LinearAlgebra.OrderedCommonEigenvector
import NLAlib.ForMathlib.Analysis.InvariantCompression
import NLAlib.ForMathlib.Analysis.OrthonormalEigenline

/-!
# Simultaneous Schur bases with a designated characteristic-root order

A common eigenline can be chosen inside the designated first eigenspace.
Its removal cancels exactly one characteristic factor, so induction preserves
any prescribed full root order while triangularizing the entire family.
-/

noncomputable section
set_option autoImplicit false
open Module Polynomial
open scoped InnerProductSpace
namespace NLAlib

/-- An arbitrary commuting complex family admits one common orthonormal
upper triangularizing basis with any prescribed complete characteristic-root
order for a designated member. Repeated roots and empty dimension are allowed;
the family may be infinite and no member is assumed normal or diagonalizable.
Horn–Johnson 2013, Theorem 2.3.3; derivations gen:simultaneous. -/
theorem exists_orthonormalBasis_simultaneous_upper_triangular_with_charpoly
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (k : ℕ) (T : ι → Module.End ℂ E)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) (hk : finrank ℂ E = k)
    (a₀ : ι) (d : Fin k → ℂ) (hchar : (T a₀).charpoly = ∏ i, (X - C (d i))) :
    ∃ b : OrthonormalBasis (Fin k) ℂ E,
      (∀ a i j, j < i → inner ℂ (b i) (T a (b j)) = 0) ∧
      ∀ i, inner ℂ (b i) (T a₀ (b i)) = d i := by
  classical
  induction k generalizing E with
  | zero =>
    exact ⟨(stdOrthonormalBasis ℂ E).reindex (finCongr hk),
      fun _ i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    have hμ : (T a₀).HasEigenvalue (d 0) := by
      apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      rw [hchar]
      simp only [Polynomial.IsRoot, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k + 1)))
      simp
    obtain ⟨x, χ, hx, hTx, hT₀x⟩ := exists_common_eigenvector_with_eigenvalue T hcomm a₀ (d 0) hμ
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let u : E := (‖x‖⁻¹ : ℂ) • x
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hxnorm.le, inv_mul_cancel₀ hxnorm.ne']
    have hune : u ≠ 0 := by intro h; simp [h] at hu
    have hTu (a : ι) : T a u = χ a • u := by
      simp only [u, map_smul, hTx, smul_smul, mul_comm]
    have hT₀u : T a₀ u = d 0 • u := by
      simp only [u, map_smul, hT₀x, smul_smul, mul_comm]
    let W : Submodule ℂ E := (ℂ ∙ u)ᗮ
    have hWdim : finrank ℂ W = k := by
      have h := (ℂ ∙ u).finrank_add_finrank_orthogonal
      rw [finrank_span_singleton hune, hk] at h
      dsimp [W]; omega
    have hpres (a : ι) : Set.MapsTo (T a) Wᗮ Wᗮ := by
      dsimp [W]
      rw [Submodule.orthogonal_orthogonal]
      intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul, hTu, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    let S (a : ι) : Module.End ℂ W :=
      W.orthogonalProjectionOnto.toLinearMap.comp ((T a).comp W.subtype)
    have hScomm : Pairwise fun a b => Commute (S a) (S b) := by
      intro a b hab
      exact commute_orthogonal_compressions_of_invariant W (T a) (T b) (hpres a) (hpres b) (hcomm hab)
    have hfactor : (T a₀).charpoly = (X - C (d 0)) * (S a₀).charpoly :=
      charpoly_eq_X_sub_C_mul_orthogonal_compression (T a₀) hu hT₀u hk
    have hSchar : (S a₀).charpoly = ∏ i : Fin k, (X - C (d i.succ)) := by
      apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (d 0))
      rw [← hfactor, hchar, Fin.prod_univ_succ]
    obtain ⟨bW, htriW, hdiagW⟩ := ih S hScomm hWdim (fun i => d i.succ) hSchar
    obtain ⟨b, hb₀, hbS⟩ := exists_orthonormalBasis_cons hk u hu bW
    refine ⟨b, ?_, ?_⟩
    · intro a i j hij
      revert hij
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        rw [hb₀, hTu, inner_smul_right]
        have hiu : inner ℂ (b i) u = 0 := by
          rw [← hb₀]
          exact b.orthonormal.inner_eq_zero (ne_of_gt hij)
        rw [hiu, mul_zero]
      · refine Fin.cases ?_ (fun i => ?_) i
        · intro hij; exact (not_lt_of_ge (Fin.zero_le _)) hij |>.elim
        · intro hij
          rw [hbS, hbS]
          simpa only [S, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.subtype_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using
              htriW a i j (Fin.succ_lt_succ_iff.mp hij)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [hb₀, hT₀u, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
        simp
      · rw [hbS]
        simpa only [S, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Submodule.subtype_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using hdiagW i

end NLAlib
