import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Actual matrix evaluation of native free-algebra polynomials

Entrywise evaluation is bundled as a genuine ring homomorphism into the
native C*-matrix ring, so it preserves actual matrix powers and products.
The universal affine matrix polynomial evaluates to the literal affine
coefficient combination. No realization or moment premise is required.
-/

noncomputable section
set_option autoImplicit false
namespace CStarMatrix
variable (R : Type*) [CommRing R] {D ι A : Type*} [Fintype D] [DecidableEq D]
  [Ring A] [Algebra R A]

/-- Genuine entrywise free-algebra evaluation into the native C*-matrix ring. -/
def freeAlgebraEvaluation (X : ι → A) :
    Matrix D D (FreeAlgebra R ι) →+* CStarMatrix D D A :=
  CStarMatrix.ofMatrixRingEquiv.toRingHom.comp (FreeAlgebra.lift R X).toRingHom.mapMatrix

/-- Actual entry evaluation is the native universal free-algebra lift. -/
@[simp] theorem freeAlgebraEvaluation_apply (X : ι → A)
    (P : Matrix D D (FreeAlgebra R ι)) (i j : D) :
    freeAlgebraEvaluation R X P i j=FreeAlgebra.lift R X (P i j) := rfl

/-- The actual affine matrix with arbitrary coefficients and actual algebra generators. -/
def affineCombination [Fintype ι] (A₀ : Matrix D D R) (C : ι → Matrix D D R)
    (X : ι → A) : CStarMatrix D D A :=
  CStarMatrix.ofMatrix (fun i j => algebraMap R A (A₀ i j)+∑ k, C k i j•X k)

end CStarMatrix
namespace FreeAlgebra
variable {R D ι : Type*} [CommRing R] [Fintype ι]

/-- The actual coefficient-matrix affine polynomial in the universal free generators. -/
def matrixLinearPolynomial (A₀ : Matrix D D R) (A : ι → Matrix D D R) :
    Matrix D D (FreeAlgebra R ι) :=
  fun i j => algebraMap R (FreeAlgebra R ι) (A₀ i j)+∑ k, A k i j•FreeAlgebra.ι R k

end FreeAlgebra
namespace CStarMatrix
variable (R : Type*) [CommRing R] {D ι A : Type*} [Fintype D] [DecidableEq D]
  [Fintype ι] [Ring A] [Algebra R A]

/-- Evaluating the universal affine coefficient polynomial gives the actual affine matrix combination. -/
theorem freeAlgebraEvaluation_matrixLinearPolynomial
    (A₀ : Matrix D D R) (C : ι → Matrix D D R) (X : ι → A) :
    freeAlgebraEvaluation R X (FreeAlgebra.matrixLinearPolynomial A₀ C)=affineCombination R A₀ C X := by
  apply CStarMatrix.ext
  intro i j
  simp only [freeAlgebraEvaluation_apply,FreeAlgebra.matrixLinearPolynomial,map_add,map_sum,map_smul,
    AlgHom.commutes,FreeAlgebra.lift_ι_apply,affineCombination]
  rfl

end CStarMatrix

namespace CStarMatrix
variable {D ι A : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

omit [Fintype D] [DecidableEq D] in
/-- Hermitian scalar coefficients and actual self-adjoint generators give a genuine self-adjoint affine matrix combination. -/
theorem isSelfAdjoint_affineCombination
    (A₀ : Matrix D D ℂ) (hA₀ : A₀.IsHermitian) (C : ι → Matrix D D ℂ)
    (hC : ∀ i, (C i).IsHermitian) (X : ι → A) (hX : ∀ i, IsSelfAdjoint (X i)) :
    IsSelfAdjoint (affineCombination ℂ A₀ C X) := by
  change star (affineCombination ℂ A₀ C X)=affineCombination ℂ A₀ C X
  apply CStarMatrix.ext
  intro i j
  change star (algebraMap ℂ A (A₀ j i)+∑ k, C k j i•X k)=
    algebraMap ℂ A (A₀ i j)+∑ k, C k i j•X k
  simp only [Algebra.algebraMap_eq_smul_one,star_add,star_sum,star_smul,star_one,hA₀.apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [(hC k).apply,(hX k).star_eq]

end CStarMatrix
