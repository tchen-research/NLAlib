import NLAlib.Matrix.Inequalities.ColumnDeterminantBound
import NLAlib.Matrix.Inequalities.PrincipalOverlapDeterminant
import NLAlib.Matrix.Inequalities.SzaszDeterminant
/-!
# Complete Hadamard, Fischer, Koteljanski, and Szász inequalities

All weak determinant bounds include the PSD boundary. Positive definite
equality cases are exact; the square-column bound includes zero-column
equality. Source: Horn--Johnson (2013), Section 7.8;
atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

/-- Complete principal determinant toolkit: Hadamard, the square-column
norm bound, Fischer, Koteljanski union/intersection, and Szász normalized
products, with their stated equality cases and all singular/empty weak
inequality extensions. The block matrix and ambient principal-minor matrix
may have independent dimensions. Horn--Johnson (2013), Theorem 7.8.1,
Corollary 7.8.3, and Theorems 7.8.5, 7.8.9 and 7.8.11.
atlas: hadamard-fischer-inequalities -/
theorem hadamard_fischer_principal_minor_inequalities
    {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {P : Matrix m m ℝ} {B : Matrix m r ℝ} {C : Matrix r r ℝ}
    (hH : (fromBlocks P B Bᵀ C).PosSemidef) :
    (A.det ≤ ∏ i, A i i) ∧
    (A.PosDef → (A.det = (∏ i, A i i) ↔ A.IsDiag)) ∧
    (∀ X : Matrix n n ℝ,
      |X.det| ≤ ∏ i, ‖(WithLp.toLp 2 (X.col i) : EuclideanSpace ℝ n)‖ ∧
      (|X.det| = (∏ i, ‖(WithLp.toLp 2 (X.col i) : EuclideanSpace ℝ n)‖) ↔
        X.HasOrthogonalCols ∨ ∃ i, X.col i = 0)) ∧
    ((fromBlocks P B Bᵀ C).det ≤ P.det * C.det) ∧
    ((fromBlocks P B Bᵀ C).PosDef →
      ((fromBlocks P B Bᵀ C).det = P.det * C.det ↔ B = 0)) ∧
    (∀ α β : Finset n, principalMinor A (α ∪ β) * principalMinor A (α ∩ β) ≤
      principalMinor A α * principalMinor A β) ∧
    (A.PosDef → ∀ α β : Finset n,
      (principalMinor A (α ∪ β) * principalMinor A (α ∩ β) =
        principalMinor A α * principalMinor A β ↔
        A.toBlock (· ∈ α \ β) (· ∈ β \ α) -
          A.toBlock (· ∈ α \ β) (· ∈ α ∩ β) * (A.toBlock (· ∈ α ∩ β) (· ∈ α ∩ β))⁻¹ *
            A.toBlock (· ∈ α ∩ β) (· ∈ β \ α) = 0)) ∧
    (∀ k : ℕ, 1 ≤ k → k < Fintype.card n →
      principalMinorProduct A (k + 1) ^ (1 / ((Fintype.card n - 1).choose k : ℝ)) ≤
        principalMinorProduct A k ^ (1 / ((Fintype.card n - 1).choose (k - 1) : ℝ))) ∧
    (A.PosDef → ∀ k : ℕ, 1 ≤ k → k < Fintype.card n →
      (principalMinorProduct A (k + 1) ^ (1 / ((Fintype.card n - 1).choose k : ℝ)) =
        principalMinorProduct A k ^ (1 / ((Fintype.card n - 1).choose (k - 1) : ℝ)) ↔ A.IsDiag)) ∧
    (∀ k l : ℕ, 1 ≤ k → k ≤ l → l ≤ Fintype.card n →
      principalMinorProduct A l ^ (1 / ((Fintype.card n - 1).choose (l - 1) : ℝ)) ≤
        principalMinorProduct A k ^ (1 / ((Fintype.card n - 1).choose (k - 1) : ℝ))) := by
  exact ⟨det_le_prod_diag_of_posSemidef hA, det_eq_prod_diag_iff_isDiag_of_posDef,
    abs_det_le_prod_column_norm_and_eq_iff, det_fromBlocks_le_mul_det_of_posSemidef hH,
    det_fromBlocks_eq_mul_det_iff_of_posDef,
    det_principal_union_mul_inter_le_of_posSemidef hA,
    fun hAPD α β => (det_principal_union_mul_inter_le_and_eq_iff_of_posDef hAPD α β).2,
    fun _ hk hkn => principalMinorProduct_normalized_succ_le hA hk hkn,
    fun hAPD _ hk hkn => principalMinorProduct_normalized_succ_eq_iff_isDiag hAPD hk hkn,
    fun _ _ hk hkl hln => principalMinorProduct_normalized_antitone hA hk hkl hln⟩

end NLAlib
