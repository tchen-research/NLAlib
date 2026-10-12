import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Prepending a unit vector to a basis of its orthogonal complement

The construction preserves the supplied complement basis pointwise and works
over both real and complex inner-product spaces.
-/

noncomputable section
open Module
open scoped InnerProductSpace
namespace NLAlib

/-- A unit vector followed by an orthonormal basis of its orthogonal
complement is an orthonormal basis of the whole finite-dimensional space.
This exact-coordinate version supports Schur and QZ induction. -/
theorem exists_orthonormalBasis_cons {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {k : ℕ} (hk : finrank 𝕜 E = k + 1) (u : E) (hu : ‖u‖ = 1)
    (bW : OrthonormalBasis (Fin k) 𝕜 (𝕜 ∙ u)ᗮ) :
    ∃ b : OrthonormalBasis (Fin (k + 1)) 𝕜 E,
      b 0 = u ∧ ∀ i, b i.succ = (bW i : E) := by
  classical
  let v : Fin (k + 1) → E := Fin.cons u (fun i => (bW i : E))
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [v, inner_self_eq_norm_sq_to_K, hu]
      · have hinner : inner 𝕜 u (bW j : E) = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (bW j).property
        simpa only [v, Fin.cons_zero, Fin.cons_succ, (Fin.succ_ne_zero j).symm, ite_false] using hinner
    · refine Fin.cases ?_ (fun j => ?_) j
      · have hinner : inner 𝕜 (bW i : E) u = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_left.mp (bW i).property
        simpa only [v, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ite_false] using hinner
      · simpa only [v, Fin.cons_succ, Fin.succ_inj, Submodule.coe_inner] using
          (orthonormal_iff_ite.mp bW.orthonormal i j)
  let c : Basis (Fin (k + 1)) 𝕜 E :=
    basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent (by simpa using hk.symm)
  let b : OrthonormalBasis (Fin (k + 1)) 𝕜 E :=
    c.toOrthonormalBasis (by simpa only [c, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv)
  have hb (i : Fin (k + 1)) : b i = v i := by
    simp only [b, Basis.coe_toOrthonormalBasis, c, coe_basisOfLinearIndependentOfCardEqFinrank']
  exact ⟨b, hb 0, fun i => hb i.succ⟩

end NLAlib
