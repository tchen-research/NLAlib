import NLAlib.ForMathlib.LinearAlgebra.CommonEigenvector
import NLAlib.ForMathlib.Analysis.InvariantCompression
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# One orthonormal triangularizing basis for a commuting family

A common eigenline is invariant under every member. Compressions onto its
orthogonal complement commute, so dimension induction produces one basis
for an arbitrary family.
Source: Horn–Johnson (2013), Theorem 2.3.3.
-/

noncomputable section
open Module
open scoped InnerProductSpace

namespace NLAlib

/-- An arbitrary commuting complex family shares one orthonormal upper
triangularizing basis. Source: Horn–Johnson (2013), Theorem 2.3.3;
the family can be infinite or empty, and dimension zero is included. -/
theorem exists_orthonormalBasis_simultaneous_upper_triangular
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (k : ℕ) (T : ι → Module.End ℂ E)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) (hk : finrank ℂ E = k) :
    ∃ b : OrthonormalBasis (Fin k) ℂ E,
      ∀ a i j, j < i → inner ℂ (b i) (T a (b j)) = 0 := by
  classical
  induction k generalizing E with
  | zero =>
    let b : OrthonormalBasis (Fin 0) ℂ E :=
      (stdOrthonormalBasis ℂ E).reindex (finCongr hk)
    exact ⟨b, fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    have : Nontrivial E := finrank_pos_iff.mp (by rw [hk]; omega)
    obtain ⟨x, χ, hxne, hTx⟩ := exists_common_eigenvector_of_pairwise_commute T hcomm
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    let u : E := (‖x‖⁻¹ : ℂ) • x
    have hunorm : ‖u‖ = 1 := by
      simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hxnorm.le, inv_mul_cancel₀ hxnorm.ne']
    have hune : u ≠ 0 := by intro hu; rw [hu, norm_zero] at hunorm; exact zero_ne_one hunorm
    have hTu (a : ι) : T a u = χ a • u := by
      simp only [u, map_smul, hTx, smul_smul, mul_comm]
    let W : Submodule ℂ E := (ℂ ∙ u)ᗮ
    have hWdim : finrank ℂ W = k := by
      have hdim := (ℂ ∙ u).finrank_add_finrank_orthogonal
      rw [finrank_span_singleton hune, hk] at hdim
      dsimp [W]
      omega
    have hpres (a : ι) : Set.MapsTo (T a) Wᗮ Wᗮ := by
      dsimp [W]
      rw [Submodule.orthogonal_orthogonal]
      intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [map_smul, hTu, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    let C (a : ι) : Module.End ℂ W :=
      W.orthogonalProjectionOnto.toLinearMap.comp ((T a).comp W.subtype)
    have hCcomm : Pairwise fun a b => Commute (C a) (C b) := by
      intro a b hab
      exact commute_orthogonal_compressions_of_invariant W (T a) (T b) (hpres a) (hpres b) (hcomm hab)
    obtain ⟨bW, htri⟩ := ih C hCcomm hWdim
    let v : Fin (k + 1) → E := Fin.cons u (fun i => (bW i : E))
    have hv : Orthonormal ℂ v := by
      rw [orthonormal_iff_ite]
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [v, inner_self_eq_norm_sq_to_K, hunorm]
        · have hinner : inner ℂ u (bW j : E) = 0 :=
            Submodule.mem_orthogonal_singleton_iff_inner_right.mp (bW j).property
          simpa only [v, Fin.cons_zero, Fin.cons_succ, (Fin.succ_ne_zero j).symm,
            ite_false] using hinner
      · refine Fin.cases ?_ (fun j => ?_) j
        · have hinner : inner ℂ (bW i : E) u = 0 :=
            Submodule.mem_orthogonal_singleton_iff_inner_left.mp (bW i).property
          simpa only [v, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ite_false] using hinner
        · simpa only [v, Fin.cons_succ, Fin.succ_inj, Submodule.coe_inner] using
            (orthonormal_iff_ite.mp bW.orthonormal i j)
    let c : Basis (Fin (k + 1)) ℂ E :=
      basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent (by simpa using hk.symm)
    let b : OrthonormalBasis (Fin (k + 1)) ℂ E :=
      c.toOrthonormalBasis (by simpa only [c, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv)
    have hb (i : Fin (k + 1)) : b i = v i := by
      simp only [b, Basis.coe_toOrthonormalBasis, c, coe_basisOfLinearIndependentOfCardEqFinrank']
    refine ⟨b, fun a i j hij => ?_⟩
    rw [hb, hb]
    revert hij
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      have hi : i ≠ 0 := ne_of_gt hij
      rw [show v 0 = u from rfl, hTu, inner_smul_right]
      have hiu : inner ℂ (v i) u = 0 := by
        simpa only [v, Fin.cons_zero] using hv.inner_eq_zero hi
      rw [hiu, mul_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro hij
        exact (not_lt_of_ge (Fin.zero_le _)) hij |>.elim
      · intro hij
        have hh := htri a i j (Fin.succ_lt_succ_iff.mp hij)
        simpa only [C, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Submodule.subtype_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
          v, Fin.cons_succ] using hh

end NLAlib
