import NLAlib.Matrix.Norms.Frobenius
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef

/-!
# Hermitian matrices with the real Frobenius Hilbert structure

This type synonym isolates the Frobenius topology and inner product from
the spectral norm used for matrix functional calculus. Its underlying
space is Mathlib's native self-adjoint submodule.
-/

noncomputable section
namespace NLAlib
variable (𝕜 n : Type*) [RCLike 𝕜] [Fintype n]

/-- The native Hermitian real vector space, equipped below with its
Frobenius Hilbert norm rather than its spectral matrix norm. -/
def HermitianFrobenius : Type _ := ↥(selfAdjoint.submodule ℝ (Matrix n n 𝕜))

instance : AddCommGroup (HermitianFrobenius 𝕜 n) :=
  inferInstanceAs (AddCommGroup (selfAdjoint.submodule ℝ (Matrix n n 𝕜)))
instance : Module ℝ (HermitianFrobenius 𝕜 n) :=
  inferInstanceAs (Module ℝ (selfAdjoint.submodule ℝ (Matrix n n 𝕜)))

/-- The identity linear equivalence to the native self-adjoint submodule. -/
def hermitianFrobeniusEquiv : HermitianFrobenius 𝕜 n ≃ₗ[ℝ]
    selfAdjoint.submodule ℝ (Matrix n n 𝕜) := LinearEquiv.refl ℝ _

/-- The actual Hermitian matrix represented by a Frobenius Hilbert vector. -/
def hermitianFrobeniusMatrix (x : HermitianFrobenius 𝕜 n) : Matrix n n 𝕜 :=
  (hermitianFrobeniusEquiv 𝕜 n x).val

variable {𝕜 n}

/-- Matrix realization is real-linear. -/
def hermitianFrobeniusMatrixLinear : HermitianFrobenius 𝕜 n →ₗ[ℝ] Matrix n n 𝕜 :=
  (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtype.comp
    (hermitianFrobeniusEquiv 𝕜 n).toLinearMap

@[instance_reducible]
private def hermitianFrobeniusCore : InnerProductSpace.Core ℝ (HermitianFrobenius 𝕜 n) where
  inner x y := frobInner (hermitianFrobeniusMatrix 𝕜 n x) (hermitianFrobeniusMatrix 𝕜 n y)
  conj_inner_symm x y := frobInner_comm _ _
  re_inner_nonneg x := frobSq_nonneg _
  add_left x y z := frobInner_add_left _ _ _
  smul_left x y r := frobInner_smul_left r _ _
  definite x hx := by
    apply (hermitianFrobeniusEquiv 𝕜 n).injective
    apply Subtype.ext
    exact (frobSq_eq_zero_iff _).mp hx

instance : NormedAddCommGroup (HermitianFrobenius 𝕜 n) :=
  hermitianFrobeniusCore.toNormedAddCommGroup
instance : InnerProductSpace ℝ (HermitianFrobenius 𝕜 n) :=
  InnerProductSpace.ofCore hermitianFrobeniusCore.toCore

/-- The Hilbert inner product is exactly the library's real Frobenius pairing. -/
theorem inner_hermitianFrobenius (x y : HermitianFrobenius 𝕜 n) :
    inner ℝ x y = frobInner (hermitianFrobeniusMatrix 𝕜 n x)
      (hermitianFrobeniusMatrix 𝕜 n y) := rfl

/-- The Hilbert norm is exactly the named Frobenius matrix norm. -/
theorem norm_hermitianFrobenius (x : HermitianFrobenius 𝕜 n) :
    ‖x‖ = frobNorm (hermitianFrobeniusMatrix 𝕜 n x) := rfl

instance : FiniteDimensional ℝ (HermitianFrobenius 𝕜 n) :=
  FiniteDimensional.of_injective hermitianFrobeniusMatrixLinear
    (fun _ _ h => (hermitianFrobeniusEquiv 𝕜 n).injective (Subtype.ext h))

instance : CompleteSpace (HermitianFrobenius 𝕜 n) := FiniteDimensional.complete ℝ _

omit [Fintype n] in
/-- Every realized vector is an actual Hermitian matrix. -/
theorem isHermitian_hermitianFrobeniusMatrix (x : HermitianFrobenius 𝕜 n) :
    (hermitianFrobeniusMatrix 𝕜 n x).IsHermitian :=
  (hermitianFrobeniusEquiv 𝕜 n x).property

/-- A Hermitian matrix as a vector in the Frobenius Hilbert realization. -/
def toHermitianFrobenius {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    HermitianFrobenius 𝕜 n := (hermitianFrobeniusEquiv 𝕜 n).symm ⟨H,hH⟩

omit [Fintype n] in
/-- Matrix realization of the canonical Hermitian inclusion. -/
@[simp] theorem hermitianFrobeniusMatrix_toHermitianFrobenius
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    hermitianFrobeniusMatrix 𝕜 n (toHermitianFrobenius hH)=H := rfl

/-- A real-linear Hermitian-preserving matrix map acts continuously on
the Frobenius Hilbert realization, by finite dimensionality. -/
def hermitianFrobeniusMap (L : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜)
    (hL : ∀ A : Matrix n n 𝕜, A.IsHermitian → (L A).IsHermitian) :
    HermitianFrobenius 𝕜 n →L[ℝ] HermitianFrobenius 𝕜 n :=
  LinearMap.toContinuousLinearMap {
    toFun x := toHermitianFrobenius (hL _ (isHermitian_hermitianFrobeniusMatrix x))
    map_add' x y := by
      apply (hermitianFrobeniusEquiv 𝕜 n).injective
      apply Subtype.ext
      exact L.map_add _ _
    map_smul' r x := by
      apply (hermitianFrobeniusEquiv 𝕜 n).injective
      apply Subtype.ext
      exact L.map_smul r _ }

/-- The lifted map has exactly the original matrix action. -/
@[simp] theorem hermitianFrobeniusMatrix_map
    (L : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜)
    (hL : ∀ A : Matrix n n 𝕜, A.IsHermitian → (L A).IsHermitian)
    (x : HermitianFrobenius 𝕜 n) :
    hermitianFrobeniusMatrix 𝕜 n (hermitianFrobeniusMap L hL x)=
      L (hermitianFrobeniusMatrix 𝕜 n x) := rfl

instance [DecidableEq n] [Nonempty n] : Nontrivial (HermitianFrobenius 𝕜 n) := by
  refine ⟨⟨0,toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n 𝕜).IsHermitian),?_⟩⟩
  intro h
  have hm := congrArg (hermitianFrobeniusMatrix 𝕜 n) h
  exact zero_ne_one hm

end NLAlib
