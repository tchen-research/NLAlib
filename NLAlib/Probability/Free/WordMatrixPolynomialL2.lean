import NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixEntryBound
import NLAlib.Probability.Free.WordPolynomialUltracontractivity
import NLAlib.Probability.Free.WordMatrixVacuum

/-!
# Actual matrix-polynomial vacuum-L² bound

The matrix entries are actual native free-algebra polynomials. Their degree
bounds are read from their canonical free-monoid coefficient supports. Scalar
ultracontractivity and the actual amplified Gram identity give precisely
`d*sqrt(d)*(k+1)*sqrt(k+1)`, the two factors in source Lemma 4.6 combined
with Lemma 4.5 of arXiv:2406.11453v2.

This polynomial bound permits an unrestricted constant coefficient. The
later module `WordMatrixMeanResolventMoments` removes the deterministic
mean from the resolvent approximation error by actual continuous mean
clipping and genuine tracial Gram-moment perturbation.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

omit [DecidableEq D] in
/-- The actual state-defined amplified L² quantity is nonnegative before
taking a square root. This follows from the literal finite Gram identity. -/
theorem wordMatrixVacuumExpectation_star_mul_re_nonneg (T : M) :
    0 ≤ (wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re := by
  rw [wordMatrixVacuumExpectation_star_mul, Complex.ofReal_re]
  positivity

omit [DecidableEq D] in
/-- Every actual entry's vacuum norm is bounded by the square root of
dimension times the actual normalized amplified L² norm. Empty D is included. -/
theorem norm_entry_wordVacuum_le_sqrt_card_mul (T : M) (i j : D) :
    ‖T i j (wordVacuum ι)‖ ≤ Real.sqrt (Fintype.card D) *
      Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re) := by
  have h := norm_entry_wordVacuum_sq_le_card_mul_wordMatrixVacuumExpectation_star_mul_re T i j
  have hm := wordMatrixVacuumExpectation_star_mul_re_nonneg T
  have hc : 0 ≤ (Fintype.card D : ℝ) := Nat.cast_nonneg _
  have hright : 0 ≤ Real.sqrt (Fintype.card D) *
      Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re) := by positivity
  have hsq : (Real.sqrt (Fintype.card D) *
      Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re)) ^ 2 =
      (Fintype.card D : ℝ) *
        (wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re := by
    rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hm]
  nlinarith [norm_nonneg (T i j (wordVacuum ι))]

/-- Actual matrix evaluation of native noncommutative scalar polynomials,
with the canonical C*-matrix target norm. -/
def wordMatrixPolynomialEvaluation (P : Matrix D D (FreeAlgebra ℂ ι)) : M :=
  CStarMatrix.ofMatrix (fun i j => FreeAlgebra.lift ℂ (wordField : ι → B) (P i j))

omit [Fintype D] [DecidableEq D] in
/-- Entry evaluation is the genuine native free-algebra lift. -/
@[simp]
theorem wordMatrixPolynomialEvaluation_apply (P : Matrix D D (FreeAlgebra ℂ ι)) (i j : D) :
    wordMatrixPolynomialEvaluation P i j = FreeAlgebra.lift ℂ (wordField : ι → B) (P i j) := rfl

/-- The actual matrix-polynomial L² estimate with exact source dimension
and degree factors. No entrywise operator-norm or Wick-degree conclusion is
a premise. The zero polynomial, empty dimension and empty alphabet are included. -/
theorem norm_wordMatrixPolynomialEvaluation_le [Fintype ι] (k : ℕ)
    (P : Matrix D D (FreeAlgebra ℂ ι))
    (hdeg : ∀ i j, ∀ w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι) (P i j)).coeff.support,
        w.toList.length ≤ k) :
    ‖wordMatrixPolynomialEvaluation P‖ ≤
      ((Fintype.card D : ℝ) * Real.sqrt (Fintype.card D)) *
        ((k + 1 : ℝ) * Real.sqrt (k + 1)) *
          Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι)
            (star (wordMatrixPolynomialEvaluation P) * wordMatrixPolynomialEvaluation P)).re) := by
  let T := wordMatrixPolynomialEvaluation P
  let r := ((k + 1 : ℝ) * Real.sqrt (k + 1)) *
    (Real.sqrt (Fintype.card D) *
      Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re))
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hT (i j : D) : ‖T i j‖ ≤ r := by
    exact (norm_freeAlgebra_lift_wordField_le k (P i j) (hdeg i j)).trans
      (mul_le_mul_of_nonneg_left (norm_entry_wordVacuum_le_sqrt_card_mul T i j) (by positivity))
  have h := CStarMatrix.norm_le_card_mul_of_forall_norm_entry_le T hr hT
  change ‖T‖ ≤ _
  convert! h using 1
  dsimp only [r]
  ring

end NLAlib
