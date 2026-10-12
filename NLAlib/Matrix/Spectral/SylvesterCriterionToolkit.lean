import NLAlib.Matrix.Spectral.SylvesterCriterion
import NLAlib.Matrix.Spectral.PrincipalMinorPSD
/-!
# Complete Sylvester criterion toolkit

Leading and trailing positive minors characterize positive definiteness.
All nonnegative principal minors, or nonnegative characteristic coefficients
with signs assigned by degree, characterize positive semidefiniteness.
The positive-first-minors and nonnegative-last-determinant boundary case is
included. Source: Horn--Johnson (2013), Theorem 7.2.5 and Corollary 7.2.4;
frontier correction `herm:coefficient-correct`.
Atlas: `sylvester-criterion`.
-/

noncomputable section

namespace NLAlib

/-- The complete Sylvester contract includes both positive-definite tests,
the all-principal-minor PSD test, the degree-dependent characteristic sign
test, and the semidefinite boundary case. Horn--Johnson (2013), Theorem 7.2.5
and Corollary 7.2.4. The characteristic test is the corrected frontier
equation `herm:coefficient-correct`; zero coefficients keep their degree.
atlas: sylvester-criterion -/
theorem sylvester_criterion {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A.PosDef ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < leadingMinor A k) ∧
    (A.PosDef ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < trailingMinor A k) ∧
    (A.PosSemidef ↔ ∀ S : Finset (Fin n),
      0 ≤ (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det) ∧
    (A.PosSemidef ↔ ∀ k, k ≤ n →
      0 ≤ (-1 : ℝ) ^ k * A.charpoly.coeff (n - k)) ∧
    ((∀ k, 1 ≤ k → k < n → 0 < leadingMinor A k) → 0 ≤ A.det → A.PosSemidef) :=
  ⟨posDef_iff_leadingMinor_pos hA, posDef_iff_trailingMinor_pos hA,
    posSemidef_iff_principal_minors_nonneg hA,
    by simpa only [Fintype.card_fin] using posSemidef_iff_signed_charpoly_coeff_nonneg hA,
    posSemidef_of_leadingMinor_pos_and_det_nonneg hA⟩

end NLAlib
