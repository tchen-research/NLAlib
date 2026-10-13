import NLAlib.Matrix.Spectral.NormalSpectral
import NLAlib.Matrix.Norms.Frobenius
/-!
# Schur's Frobenius identity and equality criterion

The triangular diagonal and its strictly upper complement have disjoint Frobenius supports
(`frobSq_eq_sum_diag_add_frobSq_sub_diagonal`), so a Schur factor obeys
`∑ |λᵢ|² ≤ ‖A‖_F²` (`sum_norm_sq_schur_diagonal_le_frobSq`), with equality exactly for normal
`A` (`sum_norm_sq_schur_diagonal_eq_frobSq_iff_normal`). Source: Horn–Johnson (2013),
Theorem 2.3.4 and Theorem 2.5.3; atlas `normal-matrices` (the identity itself is a helper of
`schur-triangularization`).
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Two complete lists of the same characteristic roots have the same sum of squared moduli.
Horn–Johnson (2013), §2.3; root multiplicities are retained by the polynomial factorization. -/
theorem sum_norm_sq_eq_of_prod_X_sub_C_eq (a b : n → ℂ)
    (hab : (∏ i, (Polynomial.X - Polynomial.C (a i))) =
      ∏ i, (Polynomial.X - Polynomial.C (b i))) :
    (∑ i, ‖a i‖ ^ 2) = ∑ i, ‖b i‖ ^ 2 := by
  classical
  have hroots (d : n → ℂ) :
      (∏ i, (Polynomial.X - Polynomial.C (d i))).roots = Finset.univ.val.map d := by
    rw [Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (d i))
  have h := congrArg (fun p : ℂ[X] => (p.roots.map (fun z => ‖z‖ ^ 2)).sum) hab
  simpa only [hroots, Multiset.map_map, Function.comp_def, Finset.sum_map_val] using h

/-- A unitary similarity preserves the squared Frobenius norm: `‖U T Uᴴ‖_F² = ‖T‖_F²`.
Horn–Johnson (2013), §2.3; applies to arbitrary square matrices and empty index types. -/
theorem frobSq_unitary_similarity (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ) :
    frobSq ((U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ) = frobSq T := by
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  rw [frobSq_mul_right_of_orthonormal hUt, frobSq_mul_left_of_orthonormal hUt]

/-- A normal matrix's squared Frobenius norm is the sum of the squared moduli of a complete
characteristic eigenvalue list (in any order). Horn–Johnson (2013), Theorem 2.5.3.
atlas: normal-matrices (partial) -/
theorem frobSq_eq_sum_norm_sq_of_normal {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (d : n → ℂ)
    (hd : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i))) :
    frobSq A = ∑ i, ‖d i‖ ^ 2 := by
  obtain ⟨U, a, hUa⟩ := exists_unitary_diagonalization_of_normal hA
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have ha : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    rw [hUa, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUt, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  rw [hUa, frobSq_unitary_similarity, frobSq_diagonal]
  exact sum_norm_sq_eq_of_prod_X_sub_C_eq a d (ha.symm.trans hd)

/-- The squared Frobenius norm splits into the diagonal mass and the off-diagonal mass:
`‖T‖_F² = ∑ᵢ |Tᵢᵢ|² + ‖T − diag T‖_F²`. Horn–Johnson (2013), proof of Theorem 2.3.4; this
algebraic identity holds for any matrix (for a Schur factor the off-diagonal part is strictly
upper). Helper for `schur-triangularization`. -/
theorem frobSq_eq_sum_diag_add_frobSq_sub_diagonal (T : Matrix n n ℂ) :
    frobSq T = (∑ i, ‖T i i‖ ^ 2) + frobSq (T - Matrix.diagonal T.diag) := by
  have hsplit : frobSq T = frobSq (Matrix.diagonal T.diag) + frobSq (T - Matrix.diagonal T.diag) := by
    rw [frobSq_eq_sum_norm_sq, frobSq_eq_sum_norm_sq, frobSq_eq_sum_norm_sq,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.diag_apply, Matrix.sub_apply,
        sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply, sub_zero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [hsplit, frobSq_diagonal]
  rfl

/-- **Schur's inequality.** The diagonal of a Schur factor `T` of `A = U T Uᴴ` satisfies
`∑ᵢ |Tᵢᵢ|² ≤ ‖A‖_F²`. Horn–Johnson (2013), Theorem 2.3.4; for a Schur factor the diagonal is the
complete eigenvalue list.
atlas: schur-triangularization -/
theorem sum_norm_sq_schur_diagonal_le_frobSq
    (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ) :
    (∑ i, ‖T i i‖ ^ 2) ≤ frobSq A := by
  rw [hA, frobSq_unitary_similarity, frobSq_eq_sum_diag_add_frobSq_sub_diagonal]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- Equality in Schur's inequality is equivalent to normality. Horn–Johnson (2013), Theorems
2.3.4 and 2.5.3; the characteristic factorization certifies that the Schur diagonal contains
every eigenvalue with its multiplicity.
atlas: normal-matrices (partial) -/
theorem sum_norm_sq_schur_diagonal_eq_frobSq_iff_normal
    (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ)
    (hchar : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i))) :
    (∑ i, ‖T i i‖ ^ 2) = frobSq A ↔ A * Aᴴ = Aᴴ * A := by
  constructor
  · intro heq
    have hmass := frobSq_eq_sum_diag_add_frobSq_sub_diagonal T
    have hnorm : frobSq A = frobSq T := by rw [hA, frobSq_unitary_similarity]
    have hzero : frobSq (T - Matrix.diagonal T.diag) = 0 := by linarith
    have hT : T = Matrix.diagonal T.diag := sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hzero)
    exact mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization U T.diag
      (hA.trans (congrArg (fun M : Matrix n n ℂ =>
        (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ) hT))
  · intro hnormal
    exact (frobSq_eq_sum_norm_sq_of_normal hnormal T.diag hchar).symm

end NLAlib
