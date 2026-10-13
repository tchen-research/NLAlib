import NLAlib.Matrix.Inequalities.PositiveSpectralEndpoints
/-!
# Hadamard products and Loewner order

Schur positivity preserves order, strengthens to positive definiteness when
one factor is positive definite and the other has positive diagonal, and
preserves absolute quadratic dominance for Hermitian comparands.
Source: Horn--Johnson (2013), Theorems 7.5.3 and 7.8.16;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Hadamard multiplication by a PSD real matrix preserves Loewner order.
Horn--Johnson (2013), Section 7.5; helper for Schur inequalities. -/
theorem hadamard_le_hadamard_of_posSemidef_left {A B C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hBC : B ≤ C) : A ⊙ B ≤ A ⊙ C := by
  have h := hA.hadamard (Matrix.le_iff.mp hBC)
  have he : A ⊙ (C - B) = A ⊙ C - A ⊙ B := by ext i j; simp [Matrix.hadamard_apply, mul_sub]
  rw [he] at h
  exact h

/-- The Hadamard product is positive definite when the first factor is
positive definite and the PSD second factor has strictly positive diagonal.
Empty dimensions are included. Horn--Johnson (2013), Theorem 7.5.3.
atlas: schur-product-inequalities (partial) -/
theorem posDef_hadamard_of_posDef_of_diag_pos {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) (hdiag : ∀ i, 0 < B i i) : (A ⊙ B).PosDef := by
  rcases isEmpty_or_nonempty n with hEmpty | hNonempty
  · let : IsEmpty n := hEmpty
    have he : A ⊙ B = (1 : Matrix n n ℝ) := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosDef.one
  · let : Nonempty n := hNonempty
    obtain ⟨ha, -, hlo, -⟩ := posDef_extreme_eigenvalues_sandwich hA Fintype.card_pos
    have hle := hadamard_le_hadamard_of_posSemidef_left hB hlo
    rw [Matrix.hadamard_comm B A, Matrix.hadamard_smul, Matrix.hadamard_one] at hle
    exact posDef_of_posDef_le ((Matrix.PosDef.diagonal hdiag).smul ha) hle

omit [DecidableEq n] in
/-- For Hermitian `A`, `B`: `|xᵀ B x| ≤ xᵀ A x` for every `x` iff `-A ≤ B ≤ A` in the Loewner
order. Horn–Johnson 2013, Lemma 7.8.15. -/
theorem abs_quadForm_le_iff_neg_le_and_le {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∀ x, |quadForm B x| ≤ quadForm A x) ↔ -A ≤ B ∧ B ≤ A := by
  rw [Matrix.le_iff, Matrix.le_iff, sub_neg_eq_add, add_comm]
  constructor
  · intro h
    constructor
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.add hB)
      intro x
      have hx := (abs_le.mp (h x)).1
      simpa only [quadForm, star_trivial, Matrix.add_mulVec, dotProduct_add,
        neg_le_iff_add_nonneg, add_comm] using hx
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.sub hB)
      intro x
      have hx := (abs_le.mp (h x)).2
      simpa only [quadForm, star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using hx
  · rintro ⟨hp, hm⟩ x
    have hp' := hp.dotProduct_mulVec_nonneg x
    have hm' := hm.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub] at hp' hm'
    rw [abs_le]
    simp only [quadForm_def, star_trivial]
    constructor <;> linarith

omit [Fintype n] [DecidableEq n] in
/-- **Hadamard products preserve Loewner sandwiches, lower bound.** If `-A ≤ B ≤ A` and
`-C ≤ D ≤ C` then `-(A ⊙ C) ≤ B ⊙ D`. Horn–Johnson 2013, Theorem 7.8.16.
atlas: schur-product-inequalities (partial) -/
theorem neg_hadamard_le_hadamard_of_neg_le_of_le {A B C D : Matrix n n ℝ}
    (hAB : -A ≤ B) (hBA : B ≤ A) (hCD : -C ≤ D) (hDC : D ≤ C) : -(A ⊙ C) ≤ B ⊙ D := by
  have hABp : (A + B).PosSemidef := by
    rw [Matrix.le_iff, sub_neg_eq_add, add_comm] at hAB; exact hAB
  have hABm : (A - B).PosSemidef := Matrix.le_iff.mp hBA
  have hCDp : (C + D).PosSemidef := by
    rw [Matrix.le_iff, sub_neg_eq_add, add_comm] at hCD; exact hCD
  have hCDm : (C - D).PosSemidef := Matrix.le_iff.mp hDC
  rw [Matrix.le_iff, sub_neg_eq_add]
  have he : (1 / 2 : ℝ) • ((A + B) ⊙ (C + D) + (A - B) ⊙ (C - D)) = B ⊙ D + A ⊙ C := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      smul_eq_mul]
    ring
  rw [← he]
  exact ((hABp.hadamard hCDp).add (hABm.hadamard hCDm)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

omit [Fintype n] [DecidableEq n] in
/-- **Hadamard products preserve Loewner sandwiches, upper bound.** If `-A ≤ B ≤ A` and
`-C ≤ D ≤ C` then `B ⊙ D ≤ A ⊙ C`. Horn–Johnson 2013, Theorem 7.8.16.
atlas: schur-product-inequalities (partial) -/
theorem hadamard_le_hadamard_of_neg_le_of_le {A B C D : Matrix n n ℝ}
    (hAB : -A ≤ B) (hBA : B ≤ A) (hCD : -C ≤ D) (hDC : D ≤ C) : B ⊙ D ≤ A ⊙ C := by
  have hABp : (A + B).PosSemidef := by
    rw [Matrix.le_iff, sub_neg_eq_add, add_comm] at hAB; exact hAB
  have hABm : (A - B).PosSemidef := Matrix.le_iff.mp hBA
  have hCDp : (C + D).PosSemidef := by
    rw [Matrix.le_iff, sub_neg_eq_add, add_comm] at hCD; exact hCD
  have hCDm : (C - D).PosSemidef := Matrix.le_iff.mp hDC
  rw [Matrix.le_iff]
  have he : (1 / 2 : ℝ) • ((A + B) ⊙ (C - D) + (A - B) ⊙ (C + D)) = A ⊙ C - B ⊙ D := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      smul_eq_mul]
    ring
  rw [← he]
  exact ((hABp.hadamard hCDm).add (hABm.hadamard hCDp)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

omit [DecidableEq n] in
/-- Absolute quadratic dominance `|xᵀ B x| ≤ xᵀ A x` is preserved by the Hadamard product of
two Hermitian pairs. Horn–Johnson 2013, Theorem 7.8.16.
atlas: schur-product-inequalities (partial) -/
theorem abs_quadForm_hadamard_le_of_abs_quadForm_le {A B C D : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (hD : D.IsHermitian)
    (hAB : ∀ x, |quadForm B x| ≤ quadForm A x) (hCD : ∀ x, |quadForm D x| ≤ quadForm C x) :
    ∀ x, |quadForm (B ⊙ D) x| ≤ quadForm (A ⊙ C) x := by
  have hp := (abs_quadForm_le_iff_neg_le_and_le hA hB).mp hAB
  have hq := (abs_quadForm_le_iff_neg_le_and_le hC hD).mp hCD
  exact (abs_quadForm_le_iff_neg_le_and_le (hA.hadamard hC) (hB.hadamard hD)).mpr
    ⟨neg_hadamard_le_hadamard_of_neg_le_of_le hp.1 hp.2 hq.1 hq.2,
      hadamard_le_hadamard_of_neg_le_of_le hp.1 hp.2 hq.1 hq.2⟩

end NLAlib
