import NLAlib.Matrix.Spectral.GeneralizedEigenPairing
/-!
# Simplicity from geometric multiplicity and left–right pairing

For a one-dimensional eigenspace, nonzero left–right pairing excludes
generalized eigenvectors outside the eigenline. Algebraic simplicity is
therefore equivalent to nonzero pairing.
Source: Horn–Johnson (2013), Theorem 1.4.12.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A one-dimensional eigenspace with nonzero left–right pairing is
algebraically simple. Source: Horn–Johnson (2013), Theorem 1.4.12; the
reverse implication needs no algebraic closure of the scalar field.
atlas: left-right-eigenvectors (partial) -/
theorem rootMultiplicity_eq_one_of_finrank_eigenspace_eq_one_of_pairing_ne_zero
    {A : Matrix n n K} {x y : n → K} {μ : K}
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hdim : finrank K (Module.End.eigenspace A.toLin' μ) = 1)
    (hpair : y ⬝ᵥ x ≠ 0) : A.charpoly.rootMultiplicity μ = 1 := by
  have hx : x ≠ 0 := by intro hx; simp [hx] at hpair
  have hspan : K ∙ x = Module.End.eigenspace A.toLin' μ :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem x _).mpr (Module.End.mem_eigenspace_iff.mpr hAx))
      (by rw [finrank_span_singleton hx, hdim])
  let N := A - μ • 1
  have hpairN (z : n → K) : y ⬝ᵥ (N *ᵥ z) = 0 := by
    simp only [N, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, Matrix.dotProduct_mulVec, hyA, smul_dotProduct,
      dotProduct_smul, sub_self]
  have hstep (z : n → K) (hz : N *ᵥ (N *ᵥ z) = 0) : N *ᵥ z = 0 := by
    have hmem : N *ᵥ z ∈ Module.End.eigenspace A.toLin' μ := by
      apply Module.End.mem_eigenspace_iff.mpr
      change A *ᵥ (N *ᵥ z) = μ • (N *ᵥ z)
      apply sub_eq_zero.mp
      simpa only [N, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hz
    rw [← hspan] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c = 0 := by
      have hp := hpairN z
      rw [← hc, dotProduct_smul, smul_eq_mul] at hp
      exact (mul_eq_zero.mp hp).resolve_right hpair
    rw [← hc, hc0, zero_smul]
  have hpower (k : ℕ) (z : n → K) (hz : N ^ k *ᵥ z = 0) : N *ᵥ z = 0 := by
    induction k generalizing z with
    | zero =>
      have hz0 : z = 0 := by simpa only [pow_zero, Matrix.one_mulVec] using hz
      rw [hz0, Matrix.mulVec_zero]
    | succ k ih =>
      apply hstep z
      apply ih (N *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← pow_succ]
      exact hz
  have hmax : Module.End.maxGenEigenspace A.toLin' μ = Module.End.eigenspace A.toLin' μ := by
    apply le_antisymm _ Module.End.eigenspace_le_maxGenEigenspace
    intro z hz
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace A.toLin' μ z).mp hz
    have hkM : N ^ k *ᵥ z = 0 := by
      change (N ^ k).toLin' z = 0
      simpa only [N, Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one,
        Module.End.one_eq_id] using hk
    apply Module.End.mem_eigenspace_iff.mpr
    change A *ᵥ z = μ • z
    apply sub_eq_zero.mp
    simpa only [N, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hpower k z hkM
  have hm := LinearMap.finrank_maxGenEigenspace_eq A.toLin' μ
  rw [hmax, hdim, Matrix.charpoly_toLin'] at hm
  exact hm.symm

/-- When geometric multiplicity is one, algebraic simplicity is equivalent
to nonzero pairing of nonzero left and right eigenvectors. Source:
Horn–Johnson (2013), Theorem 1.4.12.
atlas: left-right-eigenvectors (partial) -/
theorem rootMultiplicity_eq_one_iff_pairing_ne_zero_of_finrank_eigenspace_eq_one
    [IsAlgClosed K] {A : Matrix n n K} {x y : n → K} {μ : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hdim : finrank K (Module.End.eigenspace A.toLin' μ) = 1) :
    A.charpoly.rootMultiplicity μ = 1 ↔ y ⬝ᵥ x ≠ 0 :=
  ⟨dotProduct_ne_zero_of_simple_eigenvalue hx hy hAx hyA,
    rootMultiplicity_eq_one_of_finrank_eigenspace_eq_one_of_pairing_ne_zero hAx hyA hdim⟩

end NLAlib
