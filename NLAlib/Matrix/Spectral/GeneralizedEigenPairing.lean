import NLAlib.Matrix.Spectral.EigenvectorPairing
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Generalized eigenspaces and simple left–right pairing

A left eigenvector annihilates generalized eigenspaces at every different
eigenvalue. When its own characteristic root is simple, its generalized
eigenspace is one-dimensional, so the pairing with a right eigenvector
cannot vanish. Source: Horn–Johnson (2013), Lemma 1.4.11;
atlas `left-right-eigenvectors` and `simple-eigenvalue-perturbation`.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Pairing with a left eigenvector turns shifted matrix powers into scalar
powers. Source: Horn–Johnson (2013), proof of Lemma 1.4.11. -/
theorem dotProduct_shift_pow_mulVec_of_left_eigenvector {A : Matrix n n K}
    {y : n → K} {α : K} (hy : y ᵥ* A = α • y) (μ : K) (k : ℕ) (z : n → K) :
    y ⬝ᵥ ((A - μ • 1) ^ k *ᵥ z) = (α - μ) ^ k * (y ⬝ᵥ z) := by
  have hshift : y ᵥ* (A - μ • 1) = (α - μ) • y := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hy, sub_smul]
  induction k with
  | zero => simp only [pow_zero, Matrix.one_mulVec, one_mul]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hshift,
      smul_dotProduct, smul_eq_mul, ih, pow_succ', mul_assoc]

/-- A left eigenvector annihilates every generalized eigenspace at a
different eigenvalue. Source: Horn–Johnson (2013), proof of Lemma 1.4.11;
the proof works over any field.
atlas: left-right-eigenvectors (partial) -/
theorem dotProduct_eq_zero_of_mem_maxGenEigenspace_of_left_eigenvalue_ne
    {A : Matrix n n K} {y z : n → K} {α μ : K}
    (hy : y ᵥ* A = α • y) (hαμ : α ≠ μ)
    (hz : z ∈ Module.End.maxGenEigenspace A.toLin' μ) : y ⬝ᵥ z = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace A.toLin' μ z).mp hz
  have hkM : (A - μ • 1) ^ k *ᵥ z = 0 := by
    change ((A - μ • 1) ^ k).toLin' z = 0
    simpa only [Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one,
      Module.End.one_eq_id] using hk
  have hpair := dotProduct_shift_pow_mulVec_of_left_eigenvector hy μ k z
  rw [hkM, dotProduct_zero] at hpair
  exact (mul_eq_zero.mp hpair.symm).resolve_left (pow_ne_zero k (sub_ne_zero.mpr hαμ))

/-- Algebraic simplicity forces nonzero left–right eigenvector pairing.
Source: Horn–Johnson (2013), Lemma 1.4.11; algebraic multiplicity one is
expressed by the characteristic polynomial's root multiplicity.
atlas: left-right-eigenvectors (partial), simple-eigenvalue-perturbation (partial) -/
theorem dotProduct_ne_zero_of_simple_eigenvalue [IsAlgClosed K] {A : Matrix n n K}
    {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) : y ⬝ᵥ x ≠ 0 := by
  intro hpair
  let ℓ : (n → K) →ₗ[K] K :=
    { toFun z := y ⬝ᵥ z
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' c z := by rw [dotProduct_smul]; rfl }
  have hdim : Module.finrank K (Module.End.maxGenEigenspace A.toLin' μ) = 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', hμ]
  have hxgen : x ∈ Module.End.maxGenEigenspace A.toLin' μ :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hAx)
  have hspan : K ∙ x = Module.End.maxGenEigenspace A.toLin' μ :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x _).mpr hxgen)
      (by rw [finrank_span_singleton hx, hdim])
  have hline : K ∙ x ≤ ℓ.ker := (Submodule.span_singleton_le_iff_mem x _).mpr hpair
  have hgen (ν : K) : Module.End.maxGenEigenspace A.toLin' ν ≤ ℓ.ker := by
    by_cases hν : ν = μ
    · rw [hν, ← hspan]
      exact hline
    · intro z hz
      exact dotProduct_eq_zero_of_mem_maxGenEigenspace_of_left_eigenvalue_ne
        hyA (Ne.symm hν) hz
  have htop : (⊤ : Submodule K (n → K)) ≤ ℓ.ker := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top A.toLin']
    exact iSup_le hgen
  have hℓ : ℓ = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp htop)
  apply hy
  funext i
  have hi := LinearMap.congr_fun hℓ (Pi.single i 1)
  simpa only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_single, mul_one,
    LinearMap.zero_apply, Pi.zero_apply] using hi

end NLAlib
