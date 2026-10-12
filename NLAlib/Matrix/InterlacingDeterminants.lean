import NLAlib.Matrix.RankOneEigenvalue

/-!
# Characteristic polynomials of diagonal arrowheads and rank-one updates

The determinant lemma and Schur complement are applied away from the
finite set of diagonal values. Polynomial extensionality then gives
unconditional identities, including repeated roots and empty dimensions.
Source: Horn–Johnson (2013), §4.3, converse interlacing constructions.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- For a diagonal matrix with nonzero entries, its inverse is the diagonal
of the scalar inverses. This explicit field form is used in the Schur
complement proof of the converse-interlacing determinant identities. -/
theorem inv_diagonal_of_forall_ne_zero (d : n → K) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (hd _), Matrix.diagonal_one]

/-- Multiplying the diagonal resolvent sum by the full product cancels
one factor in each summand. Source: the finite-product identity underlying
both converse-interlacing characteristic-polynomial formulas. -/
theorem prod_mul_sum_div_eq_sum_prod_erase (d w : n → K) (hd : ∀ i, d i ≠ 0) :
    (∏ i, d i) * (∑ i, w i / d i) =
      ∑ i, w i * ∏ j ∈ Finset.univ.erase i, d j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
  field_simp [hd i]

/-- The Schur complement determinant of a diagonal arrowhead away from
zero diagonal entries. Source: Horn–Johnson (2013), converse interlacing;
the final characteristic-polynomial theorem removes this restriction. -/
theorem det_fromBlocks_diagonal_of_forall_ne_zero
    {l : Type*} [Unique l] [Fintype l] [DecidableEq l]
    (d v : n → K) (a : K) (hd : ∀ i, d i ≠ 0) :
    (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol l v)
      (Matrix.replicateRow l v) (Matrix.of fun _ _ : l => a)).det =
      (∏ i, d i) * (a - ∑ i, (v i) ^ 2 / d i) := by
  have hdet : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  let := ((Matrix.isUnit_iff_isUnit_det _).mpr hdet).nonempty_invertible.some
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_diagonal, Matrix.det_unique,
    Matrix.invOf_eq_nonsing_inv, inv_diagonal_of_forall_ne_zero d hd]
  congr 1
  rw [Matrix.sub_apply]
  congr 1
  conv_lhs => rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A diagonal matrix plus an arbitrary rank-one term has this determinant
when the diagonal entries are nonzero. Source: the determinant lemma;
converse interlacing uses the unrestricted polynomial extension below. -/
theorem det_diagonal_add_vecMulVec_of_forall_ne_zero
    (d u v : n → K) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).det =
      (∏ i, d i) * (1 + ∑ i, u i * v i / d i) := by
  have hdet : IsUnit (Matrix.diagonal d).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  rw [det_add_vecMulVec hdet, Matrix.det_diagonal,
    inv_diagonal_of_forall_ne_zero d hd]
  congr 2
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring




/-- The characteristic polynomial of a real or infinite-field diagonal
arrowhead is the diagonal product times its last linear factor, minus the
sum of squared couplings times the products with one factor erased.
Source: Horn–Johnson (2013), converse interlacing; the formula is
unconditional, including repeated diagonal entries and empty leading blocks.
atlas: interlacing-converse (partial) -/
theorem charpoly_fromBlocks_diagonal_replicate
    [Infinite K] {l : Type*} [Unique l] [Fintype l] [DecidableEq l]
    (d v : n → K) (a : K) :
    (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol l v)
      (Matrix.replicateRow l v) (Matrix.of fun _ _ : l => a)).charpoly =
      (X - C a) * (∏ i, (X - C (d i))) -
        ∑ i, C ((v i) ^ 2) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_range d).infinite_compl.mono
  intro z hz
  have hzd (i : n) : z - d i ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hz ⟨i, h.symm⟩
  simp only [Set.mem_ofPred_eq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  rw [Matrix.eval_charpoly, Matrix.scalar_apply]
  have hblocks : Matrix.diagonal (fun _ : n ⊕ l => z) -
      Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol l v)
        (Matrix.replicateRow l v) (Matrix.of fun _ _ : l => a) =
      Matrix.fromBlocks (Matrix.diagonal (fun i => z - d i))
        (Matrix.replicateCol l (-v)) (Matrix.replicateRow l (-v))
        (Matrix.of fun _ _ : l => z - a) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · by_cases hij : i = j <;> simp [Matrix.fromBlocks, hij]
    · simp [Matrix.fromBlocks]
    · simp [Matrix.fromBlocks]
    · have hij : i = j := Subsingleton.elim _ _
      simp [Matrix.fromBlocks, hij]
  rw [hblocks, det_fromBlocks_diagonal_of_forall_ne_zero _ _ _ hzd, mul_sub,
    prod_mul_sum_div_eq_sum_prod_erase _ _ hzd]
  simp only [Pi.neg_apply, neg_sq]
  rw [mul_comm]

/-- The characteristic polynomial of a diagonal matrix plus `v vᵀ` is its
diagonal product minus the sum of squared couplings times products with
one factor erased. Source: Horn–Johnson (2013), converse interlacing;
no distinctness, nonzero-entry or invertibility assumption is required,
and the empty matrix has characteristic polynomial one.
atlas: interlacing-converse (partial) -/
theorem charpoly_diagonal_add_vecMulVec
    [Infinite K] (d v : n → K) :
    (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly =
      (∏ i, (X - C (d i))) -
        ∑ i, C ((v i) ^ 2) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_range d).infinite_compl.mono
  intro z hz
  have hzd (i : n) : z - d i ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hz ⟨i, h.symm⟩
  simp only [Set.mem_ofPred_eq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  rw [Matrix.eval_charpoly, Matrix.scalar_apply]
  have hmat : Matrix.diagonal (fun _ : n => z) - (Matrix.diagonal d + Matrix.vecMulVec v v) =
      Matrix.diagonal (fun i => z - d i) + Matrix.vecMulVec (-v) v := by
    rw [Matrix.neg_vecMulVec, ← Matrix.diagonal_sub]
    abel
  rw [hmat, det_diagonal_add_vecMulVec_of_forall_ne_zero _ _ _ hzd, mul_add, mul_one,
    prod_mul_sum_div_eq_sum_prod_erase _ _ hzd]
  simp only [Pi.neg_apply, neg_mul, ← pow_two, neg_mul, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]

end NLAlib
