import NLAlib.Matrix.DistanceToSingularity

/-!
# Complete condition-number characterizations

The native singular-value ratio, rank/zero branches, all invariances, positive
definite eigenvalue ratio, and attained absolute/relative singular distances.
Source: Golub--Van Loan, Section 2.6.2; Higham, Theorem 6.5.
Atlas: `condition-number-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- The full condition-number contract uses the actual Moore--Penrose inverse
and actual native singular/eigenvalue lists. Distances are attained and their
positive-dimension condition is explicit. Golub--Van Loan, Section 2.6.2;
Higham, Theorem 6.5.
atlas: condition-number-def -/
theorem condition_number_characterizations (A : Matrix m n ℝ) :
    conditionNumber (0 : Matrix m n ℝ) = 0 ∧
    (A ≠ 0 → 1 ≤ conditionNumber A) ∧
    (0 < A.rank → conditionNumber A = A.toEuclideanLin.singularValues 0 /
      A.toEuclideanLin.singularValues (A.rank - 1)) ∧
    (∀ c : ℝ, c ≠ 0 → conditionNumber (c • A) = conditionNumber A) ∧
    conditionNumber Aᵀ = conditionNumber A ∧
    conditionNumber (Aᵀ * A) = conditionNumber A ^ 2 ∧
    (∀ Q : Matrix p m ℝ, HasOrthonormalCols Q → conditionNumber (Q * A) = conditionNumber A) ∧
    (∀ B : Matrix n n ℝ, ∀ hB : B.PosDef, ∀ hDim : 0 < Fintype.card n,
      conditionNumber B = hB.isHermitian.eigenvalues₀ ⟨0, hDim⟩ /
        hB.isHermitian.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hDim (by decide : 0 < 1)⟩) ∧
    (∀ B : Matrix n n ℝ, IsUnit B → 0 < Fintype.card n →
      IsLeast (specNorm '' {E : Matrix n n ℝ | ¬ IsUnit (B + E)}) (1 / specNorm B⁻¹) ∧
      IsLeast ((fun E : Matrix n n ℝ => specNorm E / specNorm B) ''
        {E | ¬ IsUnit (B + E)}) (1 / conditionNumber B)) := by
  refine ⟨conditionNumber_zero, fun hA => one_le_conditionNumber hA,
    fun hr => conditionNumber_eq_toEuclideanLin_singularValues_ratio A hr,
    fun c hc => conditionNumber_smul (c := c) hc A, conditionNumber_transpose A,
    conditionNumber_transpose_mul_self A,
    fun Q hQ => conditionNumber_mul_left_of_hasOrthonormalCols Q A hQ, ?_, ?_⟩
  · intro B hB hDim
    let : Nonempty n := Fintype.card_pos_iff.mp hDim
    exact conditionNumber_eq_eigenvalues₀_ratio B hB
  · intro B hB hDim
    let : Nonempty n := Fintype.card_pos_iff.mp hDim
    exact ⟨isLeast_specNorm_singular_perturbations B hB,
      isLeast_relative_singular_perturbations B hB⟩

end NLAlib
