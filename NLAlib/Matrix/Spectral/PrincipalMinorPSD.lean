import NLAlib.ForMathlib.Algebra.SignedCoefficients
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive semidefiniteness from principal minors and characteristic coefficients

All principal minors characterize PSD membership. The characteristic-polynomial
criterion assigns signs by degree and permits zero coefficients; deleting zero
coefficients and merely checking alternation is insufficient.
Source: Horn--Johnson (2013), Theorem 7.2.5 and Corollary 7.2.4;
frontier derivations, corrected equation `herm:coefficient-correct`.
Atlas: `sylvester-criterion`.
-/

noncomputable section
open Polynomial Matrix
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The signed characteristic coefficient is exactly the sum of the
corresponding principal minors. Mathlib's characteristic coefficient formula;
helper for `sylvester-criterion`. -/
theorem signed_charpoly_coeff_eq_sum_principal_minors (A : Matrix n n ℝ)
    (k : ℕ) (hk : k ≤ Fintype.card n) :
    (-1 : ℝ) ^ k * A.charpoly.coeff (Fintype.card n - k) =
      ∑ S ∈ Finset.univ.powersetCard k,
        (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det := by
  rw [Matrix.charpoly_coeff_eq_sum_minors A k hk, ← mul_assoc,
    ← pow_add, show k + k = 2 * k by omega, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Every degree-dependent signed characteristic coefficient of a PSD
matrix is nonnegative. Horn--Johnson (2013), Theorem 7.2.5;
corrected frontier equation `herm:coefficient-correct`.
atlas: sylvester-criterion (partial) -/
theorem signed_charpoly_coeff_nonneg_of_posSemidef {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (k : ℕ) (hk : k ≤ Fintype.card n) :
    0 ≤ (-1 : ℝ) ^ k * A.charpoly.coeff (Fintype.card n - k) := by
  rw [signed_charpoly_coeff_eq_sum_principal_minors A k hk]
  exact Finset.sum_nonneg fun S _ => (hA.submatrix (Subtype.val : S → n)).det_nonneg

/-- Nonnegative degree-dependent signed characteristic coefficients
force every real symmetric eigenvalue to be nonnegative.
Horn--Johnson (2013), Theorem 7.2.5; corrected frontier equation
`herm:coefficient-correct`. The argument excludes negative roots directly.
atlas: sylvester-criterion (partial) -/
theorem posSemidef_of_signed_charpoly_coeff_nonneg {A : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hcoeff : ∀ k, k ≤ Fintype.card n →
      0 ≤ (-1 : ℝ) ^ k * A.charpoly.coeff (Fintype.card n - k)) : A.PosSemidef := by
  apply hA.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  by_contra h
  have hneg : hA.eigenvalues i < 0 := lt_of_not_ge h
  have hc : ∀ j, j ≤ Fintype.card n →
      0 ≤ (-1 : ℝ) ^ (Fintype.card n - j) * A.charpoly.coeff j := by
    intro j hj
    simpa only [Nat.sub_sub_self hj] using hcoeff (Fintype.card n - j) (Nat.sub_le _ _)
  have hpos := mul_eval_neg_pos_of_signed_coeff_nonneg A.charpoly_natDegree_eq_dim
    A.charpoly_monic hc (neg_pos.mpr hneg)
  have hroot : A.charpoly.eval (hA.eigenvalues i) = 0 := by
    rw [hA.charpoly_eq, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      RCLike.ofReal_real_eq_id, id_eq]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  simp only [neg_neg, hroot, mul_zero, lt_self_iff_false] at hpos

/-- The corrected characteristic-polynomial PSD test assigns signs by
degree, with zero coefficients allowed. Horn--Johnson (2013), Theorem 7.2.5;
frontier equation `herm:coefficient-correct` repairs the catalogue's
nonzero-coefficient wording.
atlas: sylvester-criterion -/
theorem posSemidef_iff_signed_charpoly_coeff_nonneg {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ k, k ≤ Fintype.card n →
      0 ≤ (-1 : ℝ) ^ k * A.charpoly.coeff (Fintype.card n - k) :=
  ⟨fun h k hk => signed_charpoly_coeff_nonneg_of_posSemidef h k hk,
    posSemidef_of_signed_charpoly_coeff_nonneg hA⟩

/-- PSD membership is equivalent to nonnegativity of every principal
minor, including the empty principal minor. Horn--Johnson (2013),
Theorem 7.2.5 and Corollary 7.2.4.
atlas: sylvester-criterion -/
theorem posSemidef_iff_principal_minors_nonneg {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ S : Finset n,
      0 ≤ (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det := by
  constructor
  · exact fun h S => (h.submatrix (Subtype.val : S → n)).det_nonneg
  · intro h
    apply posSemidef_of_signed_charpoly_coeff_nonneg hA
    intro k hk
    rw [signed_charpoly_coeff_eq_sum_principal_minors A k hk]
    exact Finset.sum_nonneg fun S _ => h S

/-- The diagonal matrix with entries one and minus one has characteristic
polynomial `X²-1`. This is the gap-coefficient counterexample in frontier
equation `herm:coefficient-correct`, correcting `sylvester-criterion`. -/
theorem charpoly_diagonal_one_neg_one_eq :
    (Matrix.diagonal ![(1 : ℝ), -1]).charpoly = (X : ℝ[X]) ^ 2 - 1 := by
  simp [Matrix.charpoly_diagonal, Fin.prod_univ_two]
  ring

/-- The diagonal matrix with entries one and minus one is not PSD,
although the two nonzero characteristic coefficients alternate in sign.
Frontier equation `herm:coefficient-correct`, correcting `sylvester-criterion`. -/
theorem not_posSemidef_diagonal_one_neg_one :
    ¬ (Matrix.diagonal ![(1 : ℝ), -1]).PosSemidef := by
  intro h
  have hdiag := h.diag_nonneg (i := (1 : Fin 2))
  norm_num at hdiag

end NLAlib
