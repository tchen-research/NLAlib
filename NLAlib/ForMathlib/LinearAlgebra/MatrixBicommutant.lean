import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# The inverse-closed commutative bicommutant of one matrix

Rational identities in one matrix can be proved in this commutative
subalgebra and then mapped back to the full matrix algebra. The
inverse is the ordinary total nonsingular matrix inverse.
-/

noncomputable section
namespace Commute
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Commutation with a square matrix implies commutation with its total
nonsingular inverse, including the singular zero-inverse case. -/
theorem matrix_inv_right {A B : Matrix n n K} (h : Commute A B) : Commute A B⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  by_cases hu : IsUnit B
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right _

end Commute

namespace Matrix
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- The bicommutant of a singleton matrix, as a scalar subalgebra. -/
def bicommutantAlgebra (A : Matrix n n K) : Subalgebra K (Matrix n n K) :=
  Subalgebra.centralizer K (Subalgebra.centralizer K ({A} : Set (Matrix n n K)))

/-- The generator belongs to its bicommutant. -/
theorem self_mem_bicommutantAlgebra (A : Matrix n n K) : A ∈ bicommutantAlgebra A := by
  intro B hB
  exact (hB A (Set.mem_singleton A)).symm

/-- A singleton bicommutant is commutative. -/
instance bicommutantAlgebraIsMulCommutative (A : Matrix n n K) :
    IsMulCommutative (bicommutantAlgebra A) := by
  apply IsMulCommutative.of_comm
  intro X Y
  apply Subtype.ext
  exact Y.property X.val (by
    intro B hB
    have hBA : B=A := Set.mem_singleton_iff.mp hB
    rw [hBA]
    exact X.property A (by intro B hB; have hBA : B=A := Set.mem_singleton_iff.mp hB; rw [hBA]))

open scoped IsMulCommutative in
/-- The singleton bicommutant carries its canonical commutative-ring structure. -/
instance bicommutantAlgebraCommRing (A : Matrix n n K) : CommRing (bicommutantAlgebra A) :=
  inferInstance

/-- The ordinary inverse stays in the bicommutant, without any unit
assumption on the matrix being inverted. -/
theorem inv_mem_bicommutantAlgebra {A X : Matrix n n K}
    (hX : X ∈ bicommutantAlgebra A) : X⁻¹ ∈ bicommutantAlgebra A := by
  intro B hB
  exact (Commute.matrix_inv_right (show Commute B X from hX B hB)).eq

/-- Inversion in the bicommutant, with the same total convention as matrices. -/
def bicommutantInverse {A : Matrix n n K} (X : bicommutantAlgebra A) : bicommutantAlgebra A :=
  ⟨X.val⁻¹, inv_mem_bicommutantAlgebra X.property⟩

/-- Units in the bicommutant are exactly the matrices that are units in
the ambient full matrix algebra. -/
theorem isUnit_bicommutant_iff {A : Matrix n n K} (X : bicommutantAlgebra A) :
    IsUnit X ↔ IsUnit X.val := by
  constructor
  · exact fun h => h.map (bicommutantAlgebra A).val
  · intro h
    exact ⟨⟨X, bicommutantInverse X,
      Subtype.ext (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)),
      Subtype.ext (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h))⟩, rfl⟩

end Matrix
