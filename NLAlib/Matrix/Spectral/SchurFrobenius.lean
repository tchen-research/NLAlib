import NLAlib.Matrix.Spectral.SchurTriangularization
import NLAlib.Matrix.Spectral.NormalSpectral
import NLAlib.Matrix.Subspaces.ComplexProjectionBounds
/-!
# Schur's Frobenius identity and equality criterion

The triangular diagonal and its strictly upper complement have disjoint
Frobenius supports. Equality in the eigenvalue bound characterizes normality.
Source: Horn–Johnson (2013), Theorem 2.3.4 and Theorem 2.5.3;
atlas `schur-triangularization` and `normal-matrices`.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.Frobenius

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Two complete lists of the same characteristic roots have the same sum
of squared magnitudes. Source: Horn–Johnson (2013), §2.3; root multiplicities
are retained by the polynomial factorization. -/
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

/-- A unitary similarity preserves squared Frobenius mass. Source:
Horn–Johnson (2013), §2.3; applies to arbitrary square matrices and empty
index types. -/
theorem frobenius_norm_sq_unitary_similarity (U : Matrix.unitaryGroup n ℂ)
    (T : Matrix n n ℂ) :
    ‖(U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ‖ ^ 2 = ‖T‖ ^ 2 := by
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  rw [frobenius_norm_sq_mul_conjTranspose_right_of_conjTranspose_mul_eq_one hUt,
    frobenius_norm_sq_mul_left_of_conjTranspose_mul_eq_one hUt]

/-- A normal matrix's squared Frobenius norm is the sum of squared magnitudes
of a complete characteristic eigenvalue list. Source: Horn–Johnson (2013),
Theorem 2.5.3; the list may be in any order.
atlas: normal-matrices (partial) -/
theorem frobenius_norm_sq_eq_sum_norm_sq_of_normal {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (d : n → ℂ)
    (hd : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i))) :
    ‖A‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
  obtain ⟨U, a, hUa⟩ := exists_unitary_diagonalization_of_normal hA
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have ha : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    rw [hUa, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUt, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  rw [hUa, frobenius_norm_sq_unitary_similarity, Matrix.frobenius_norm_diagonal,
    EuclideanSpace.norm_sq_eq]
  exact sum_norm_sq_eq_of_prod_X_sub_C_eq a d (ha.symm.trans hd)

/-- Diagonal Frobenius mass and off-diagonal Frobenius mass add exactly.
Source: Horn–Johnson (2013), proof of Theorem 2.3.4; this algebraic identity
holds for any matrix, and the off-diagonal part is strictly upper for a
Schur triangular factor.
atlas: schur-triangularization (partial) -/
theorem frobenius_norm_sq_eq_diagonal_add_off_diagonal (T : Matrix n n ℂ) :
    ‖T‖ ^ 2 = (∑ i, ‖T i i‖ ^ 2) + ‖T - Matrix.diagonal T.diag‖ ^ 2 := by
  have hsplit : ‖T‖ ^ 2 = ‖Matrix.diagonal T.diag‖ ^ 2 +
      ‖T - Matrix.diagonal T.diag‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_norm_sq, frobenius_norm_sq_eq_sum_norm_sq,
      frobenius_norm_sq_eq_sum_norm_sq, ← Finset.sum_add_distrib]
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
  rw [hsplit, Matrix.frobenius_norm_diagonal, EuclideanSpace.norm_sq_eq]
  rfl

/-- Schur's diagonal squared-eigenvalue bound. Source: Horn–Johnson (2013),
Theorem 2.3.4; for an actual Schur factor its diagonal is the complete
eigenvalue list, and its off-diagonal part is strictly upper.
atlas: schur-triangularization (partial) -/
theorem sum_norm_sq_schur_diagonal_le_frobenius_norm_sq
    (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ) :
    (∑ i, ‖T i i‖ ^ 2) ≤ ‖A‖ ^ 2 := by
  rw [hA, frobenius_norm_sq_unitary_similarity, frobenius_norm_sq_eq_diagonal_add_off_diagonal]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality in Schur's squared-eigenvalue bound is equivalent to normality.
Source: Horn–Johnson (2013), Theorems 2.3.4 and 2.5.3; the characteristic
factorization explicitly certifies that the Schur diagonal contains every
eigenvalue with its multiplicity.
atlas: schur-triangularization (partial), normal-matrices (partial) -/
theorem sum_norm_sq_schur_diagonal_eq_iff_normal
    (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ)
    (hchar : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i))) :
    (∑ i, ‖T i i‖ ^ 2) = ‖A‖ ^ 2 ↔ A * Aᴴ = Aᴴ * A := by
  constructor
  · intro heq
    have hmass := frobenius_norm_sq_eq_diagonal_add_off_diagonal T
    have hnorm : ‖A‖ ^ 2 = ‖T‖ ^ 2 := by rw [hA, frobenius_norm_sq_unitary_similarity]
    have hzero : ‖T - Matrix.diagonal T.diag‖ ^ 2 = 0 := by linarith
    have hT : T = Matrix.diagonal T.diag :=
      sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
    exact mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization U T.diag
      (hA.trans (congrArg (fun M : Matrix n n ℂ =>
        (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ) hT))
  · intro hnormal
    exact (frobenius_norm_sq_eq_sum_norm_sq_of_normal hnormal T.diag hchar).symm

end NLAlib
