import NLAlib.Matrix.Inequalities.PrincipalMinorProductBounds
import NLAlib.ForMathlib.Analysis.BinomialRootComparison
/-!
# Szász's normalized principal-minor products

The integer-power inequality is converted by the exact binomial exponent
ratio. Weak monotonicity includes the PSD boundary; equality between
consecutive nontrivial orders on positive definite input is diagonal structure.
Source: Horn--Johnson (2013), Theorem 7.8.11;
atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Szász's normalized principal-minor products decrease between consecutive
orders throughout the PSD cone, including zero products and repeated
eigenvalues. The valid index conditions make both binomial normalizers
positive. Horn--Johnson (2013), Theorem 7.8.11.
atlas: hadamard-fischer-inequalities (partial) -/
theorem principalMinorProduct_normalized_succ_le {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card n) :
    principalMinorProduct A (k + 1) ^ (1 / ((Fintype.card n - 1).choose k : ℝ)) ≤
      principalMinorProduct A k ^ (1 / ((Fintype.card n - 1).choose (k - 1) : ℝ)) := by
  apply (rpow_inv_choose_compare_iff_pow_compare hk hkn
    (principalMinorProduct_nonneg hA k) (principalMinorProduct_nonneg hA (k + 1))).1.mpr
  exact principalMinorProduct_succ_pow_le_of_posSemidef hA k

/-- Equality in any nontrivial consecutive normalized Szász comparison for
a positive definite matrix holds exactly for diagonal matrices.
No equality characterization is imposed on singular PSD input.
Horn--Johnson (2013), Theorem 7.8.11.
atlas: hadamard-fischer-inequalities (partial) -/
theorem principalMinorProduct_normalized_succ_eq_iff_isDiag {A : Matrix n n ℝ}
    (hA : A.PosDef) {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card n) :
    principalMinorProduct A (k + 1) ^ (1 / ((Fintype.card n - 1).choose k : ℝ)) =
      principalMinorProduct A k ^ (1 / ((Fintype.card n - 1).choose (k - 1) : ℝ)) ↔ A.IsDiag := by
  rw [(rpow_inv_choose_compare_iff_pow_compare hk hkn
    (principalMinorProduct_pos hA k).le (principalMinorProduct_pos hA (k + 1)).le).2]
  exact principalMinorProduct_succ_pow_eq_iff_isDiag hA hk hkn

/-- The entire normalized principal-minor product sequence is antitone
between any two valid positive orders, including all PSD boundary cases.
For dimensions zero and one there is no nontrivial comparison.
Horn--Johnson (2013), Theorem 7.8.11.
atlas: hadamard-fischer-inequalities (partial) -/
theorem principalMinorProduct_normalized_antitone {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hln : l ≤ Fintype.card n) :
    principalMinorProduct A l ^ (1 / ((Fintype.card n - 1).choose (l - 1) : ℝ)) ≤
      principalMinorProduct A k ^ (1 / ((Fintype.card n - 1).choose (k - 1) : ℝ)) := by
  revert hln
  induction l, hkl using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ l hkl ih =>
    intro hln
    have hstep := principalMinorProduct_normalized_succ_le hA (hk.trans hkl)
      (show l < Fintype.card n by omega)
    simp only [Nat.add_sub_cancel] at hstep ⊢
    exact hstep.trans (ih (by omega))

end NLAlib
