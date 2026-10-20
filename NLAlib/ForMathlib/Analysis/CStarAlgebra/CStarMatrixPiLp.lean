import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical operator-valued C*-matrices on finite Hilbert direct sums

An actual matrix of bounded operators acts on `PiLp 2` by the usual finite
column sums. This action is a faithful star-algebra homomorphism from native
`CStarMatrix`, so its native C*-norm agrees with the Hilbert operator norm.
No norm or order instance on the raw `Matrix` type is introduced.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical InnerProduct

namespace CStarMatrix

section EntryMaps

variable {D A C : Type*} [Fintype D] [DecidableEq D]
  [Semiring A] [Algebra ℂ A] [Star A] [Semiring C] [Algebra ℂ C] [Star C]

/-- Applying a unital star-algebra map entrywise to native C*-matrices.
This is the unital counterpart of the existing native `CStarMatrix.mapₙₐ`. -/
def mapStarAlgHom (φ : A →⋆ₐ[ℂ] C) : CStarMatrix D D A →⋆ₐ[ℂ] CStarMatrix D D C where
  toFun M := M.map φ
  map_one' := by
    ext i j
    by_cases hij : i = j <;> simp [map_apply, one_apply, hij]
  map_mul' M N := by
    ext i j
    simp only [map_apply, mul_apply, map_sum, map_mul]
  map_zero' := by ext; simp
  map_add' M N := by ext; simp
  commutes' z := by
    ext i j
    by_cases hij : i = j
    · simp only [map_apply, algebraMap_apply, hij, ite_true]
      exact φ.commutes' z
    · simp [map_apply, algebraMap_apply, hij]
  map_star' M := by ext; simp only [map_apply, star_apply, map_star]

/-- Coordinates of the unital native entrywise star-algebra map. -/
@[simp]
theorem mapStarAlgHom_apply (φ : A →⋆ₐ[ℂ] C) (M : CStarMatrix D D A) (i j : D) :
    mapStarAlgHom φ M i j = φ (M i j) := rfl

/-- An injective entry map induces an injective native C*-matrix map. -/
theorem mapStarAlgHom_injective (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) :
    Function.Injective (mapStarAlgHom (D := D) φ) := map_injective hφ

end EntryMaps

variable {D H : Type*} [Fintype D] [DecidableEq D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "B" => H →L[ℂ] H
local notation "K" => PiLp 2 (fun _ : D => H)

/-- The actual finite column action of a native operator-valued C*-matrix
on the Hilbert direct sum. The empty matrix dimension is included. -/
def toPiLpCLM (M : CStarMatrix D D B) : K →L[ℂ] K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : D => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j, (M i j).comp (PiLp.proj 2 (fun _ : D => H) j)))

omit [DecidableEq D] [CompleteSpace H] in
/-- Coordinates of the actual bounded block operator are the usual finite
sums of operator entries applied to vector coordinates. -/
@[simp]
theorem toPiLpCLM_apply (M : CStarMatrix D D B) (v : K) (i : D) :
    toPiLpCLM M v i = ∑ j, M i j (v j) := by
  simp [toPiLpCLM, ContinuousLinearMap.comp_apply]

omit [CompleteSpace H] in
/-- A single-coordinate test vector recovers any chosen operator entry. -/
@[simp]
theorem toPiLpCLM_apply_single (M : CStarMatrix D D B) (j : D) (x : H) (i : D) :
    toPiLpCLM M (PiLp.single 2 j x) i = M i j x := by
  rw [toPiLpCLM_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

omit [DecidableEq D] in
private theorem toPiLpCLM_star (M : CStarMatrix D D B) :
    toPiLpCLM (star M) = star (toPiLpCLM M) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, toPiLpCLM_apply, star_apply, sum_inner, inner_sum,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [Finset.sum_comm]

/-- The genuine block representation of native C*-matrices of bounded
operators on the finite Hilbert direct sum, bundled as a star-algebra map. -/
def toPiLpStarAlgHom : CStarMatrix D D B →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := toPiLpCLM
  map_one' := by
    ext v i
    rw [toPiLpCLM_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_mul' M N := by
    ext v i
    simp only [toPiLpCLM_apply, mul_apply, sum_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, map_sum]
    rw [Finset.sum_comm]
  map_zero' := by
    ext v i
    simp
  map_add' M N := by
    ext v i
    simp [Finset.sum_add_distrib]
  commutes' z := by
    ext v i
    rw [toPiLpCLM_apply, Finset.sum_eq_single i]
    · simp [algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    · intro j _ hji
      simp [algebraMap_apply, Ne.symm hji]
    · simp
  map_star' := toPiLpCLM_star

/-- Evaluating the bundled representation gives the actual column-sum action. -/
@[simp]
theorem toPiLpStarAlgHom_apply (M : CStarMatrix D D B) (v : K) (i : D) :
    toPiLpStarAlgHom (D := D) (H := H) M v i = ∑ j, M i j (v j) :=
  toPiLpCLM_apply M v i

/-- The block representation is faithful: its values on actual single
coordinates recover every bounded-operator entry. No nonempty-dimension or
nontrivial-Hilbert-space assumption is needed. -/
theorem toPiLpStarAlgHom_injective :
    Function.Injective (toPiLpStarAlgHom (D := D) (H := H)) := by
  intro M N hMN
  apply CStarMatrix.ext
  intro i j
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T : K →L[ℂ] K => T (PiLp.single 2 j x) i) hMN
  exact (toPiLpCLM_apply_single M j x i).symm.trans
    (h.trans (toPiLpCLM_apply_single N j x i))

/-- The native C*-matrix norm is exactly the operator norm of its actual
Hilbert block representation. This uses the canonical existing C*-norm. -/
theorem norm_toPiLpStarAlgHom (M : CStarMatrix D D B) :
    ‖toPiLpStarAlgHom (D := D) (H := H) M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (toPiLpStarAlgHom (D := D) (H := H))
    toPiLpStarAlgHom_injective M

/-- The faithful block representation is isometric for the native norms. -/
theorem isometry_toPiLpStarAlgHom : Isometry (toPiLpStarAlgHom (D := D) (H := H)) :=
  NonUnitalStarAlgHom.isometry toPiLpStarAlgHom toPiLpStarAlgHom_injective

/-- Self-adjointness of the actual block operator is equivalent to native
self-adjointness of the C*-matrix of bounded-operator entries. -/
theorem isSelfAdjoint_toPiLpStarAlgHom_iff (M : CStarMatrix D D B) :
    IsSelfAdjoint (toPiLpStarAlgHom (D := D) (H := H) M) ↔ IsSelfAdjoint M := by
  constructor
  · intro hM
    apply toPiLpStarAlgHom_injective
    simpa only [map_star] using hM.star_eq
  · exact fun hM => hM.map toPiLpStarAlgHom

/-- The real spectrum of an actual self-adjoint block operator equals the
native real spectrum of its operator-valued C*-matrix. -/
theorem spectrum_real_toPiLpStarAlgHom {M : CStarMatrix D D B} (hM : IsSelfAdjoint M) :
    spectrum ℝ (toPiLpStarAlgHom (D := D) (H := H) M) = spectrum ℝ M :=
  hM.map_spectrum_real (toPiLpStarAlgHom (D := D) (H := H)) toPiLpStarAlgHom_injective

open scoped ComplexOrder Matrix.Norms.L2Operator in
/-- For actual scalar complex matrices, the canonical native C*-matrix
norm agrees with the existing scalar ℓ² operator norm. -/
theorem norm_ofMatrix_complex (M : Matrix D D ℂ) :
    ‖CStarMatrix.ofMatrix M‖ = ‖M‖ :=
  StarAlgEquiv.norm_map (CStarMatrix.ofMatrixStarAlgEquiv (n := D) (A := ℂ)) M

end CStarMatrix
