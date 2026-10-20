import NLAlib.Probability.Free.WordDegreeOperations
import NLAlib.Probability.Free.WordMatrixPolynomialL2
import NLAlib.ForMathlib.Analysis.CStarAlgebra.SelfAdjointPositivePowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Genuine amplified word degree and high even vacuum moments

Actual entry degrees are preserved by adjoint and added by multiplication.
Thus the actual Gram power `(T* T)^q` has degree at most `2*q*k`. Applying
the matrix L² estimate to this power gives the exact source high-moment
ultracontractive dependence. No polynomial adjoint convention or assumed
entry-degree conclusion is used.

Source: Theorem 4.1 of arXiv:2406.11453v2. The later offset-uniform resolvent
approximation is a separate statement.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

/-- Native scalar free-algebra evaluation genuinely lies in the bounded
word degree space, derived from its canonical coefficient support. -/
theorem freeAlgebra_lift_wordField_mem_wordWickDegreeSpan (k : ℕ) (P : FreeAlgebra ℂ ι)
    (hdeg : ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι) P).coeff.support,
      w.toList.length ≤ k) :
    FreeAlgebra.lift ℂ (wordField : ι → B) P ∈ wordWickDegreeSpan (ι := ι) k := by
  have hEval : FreeAlgebra.lift ℂ (wordField : ι → B) =
      (MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField)).comp
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι)).toAlgHom := by
    ext i
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hEval, AlgHom.comp_apply, MonoidAlgebra.lift_apply]
  simp only [FreeMonoid.lift_apply]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordWickDegreeSpan_mono (hdeg w hw) (list_prod_wordField_mem_wordWickDegreeSpan w.toList)

omit [Fintype D] [DecidableEq D] in
/-- Native matrix-polynomial entries genuinely have the claimed degree. -/
theorem wordMatrixPolynomialEvaluation_mem_wordWickDegreeSpan (k : ℕ)
    (P : Matrix D D (FreeAlgebra ℂ ι))
    (hdeg : ∀ i j, ∀ w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι) (P i j)).coeff.support,
        w.toList.length ≤ k) (i j : D) :
    wordMatrixPolynomialEvaluation P i j ∈ wordWickDegreeSpan (ι := ι) k :=
  freeAlgebra_lift_wordField_mem_wordWickDegreeSpan k (P i j) (hdeg i j)

omit [DecidableEq D] in
/-- Matrix multiplication adds actual entry degrees, by the literal
finite entry product formula. -/
theorem mul_entries_mem_wordWickDegreeSpan {j k : ℕ} {S T : M}
    (hS : ∀ i l, S i l ∈ wordWickDegreeSpan (ι := ι) j)
    (hT : ∀ l i, T l i ∈ wordWickDegreeSpan (ι := ι) k) :
    ∀ i l, (S * T) i l ∈ wordWickDegreeSpan (ι := ι) (j + k) := by
  intro i l
  rw [CStarMatrix.mul_apply]
  exact Submodule.sum_mem _ (fun a _ => mul_mem_wordWickDegreeSpan (hS i a) (hT a l))

omit [Fintype D] [DecidableEq D] in
/-- Actual matrix adjoint preserves actual entry degree. -/
theorem star_entries_mem_wordWickDegreeSpan {k : ℕ} {T : M}
    (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k) :
    ∀ i j, star T i j ∈ wordWickDegreeSpan (ι := ι) k := by
  intro i j
  rw [CStarMatrix.star_apply]
  exact star_mem_wordWickDegreeSpan (hT j i)

/-- Actual matrix powers multiply actual entry degree by their exponent,
including the genuine degree-zero identity matrix. -/
theorem pow_entries_mem_wordWickDegreeSpan {k : ℕ} {T : M}
    (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k) (q : ℕ) :
    ∀ i j, (T ^ q) i j ∈ wordWickDegreeSpan (ι := ι) (q * k) := by
  induction q with
  | zero =>
    intro i j
    simp only [pow_zero, zero_mul, CStarMatrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij]
      simpa only [wordWickOperator] using
        wordWickOperator_mem_wordWickDegreeSpan ([] : List ι) (by simp : ([] : List ι).length ≤ 0)
    · rw [if_neg hij]
      exact Submodule.zero_mem _
  | succ q hq =>
    simpa only [pow_succ, Nat.succ_mul] using mul_entries_mem_wordWickDegreeSpan hq hT

/-- The actual matrix L² estimate applies to genuine bounded-degree
operators, with actual entry membership and no norm-comparison premise. -/
theorem norm_le_wordMatrixVacuumL2_of_entries_mem_wordWickDegreeSpan [Fintype ι]
    (k : ℕ) (T : M) (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k) :
    ‖T‖ ≤ ((Fintype.card D : ℝ) * Real.sqrt (Fintype.card D)) *
      ((k + 1 : ℝ) * Real.sqrt (k + 1)) *
        Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re) := by
  let r := ((k + 1 : ℝ) * Real.sqrt (k + 1)) *
    (Real.sqrt (Fintype.card D) *
      Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re))
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hbound (i j : D) : ‖T i j‖ ≤ r :=
    (norm_le_mul_sqrt_vacuum_of_mem_wordWickDegreeSpan (hT i j)).trans
      (mul_le_mul_of_nonneg_left (norm_entry_wordVacuum_le_sqrt_card_mul T i j) (by positivity))
  have h := CStarMatrix.norm_le_card_mul_of_forall_norm_entry_le T hr hbound
  convert! h using 1
  dsimp only [r]
  ring

/-- The unrooted high even vacuum-moment bound obtained by applying the
actual degree estimate to `(T* T)^q`. Positive q retains empty matrix dimension. -/
theorem norm_pow_le_wordMatrixVacuum_evenMoment [Fintype ι] (k q : ℕ) (hq : 0 < q)
    (T : M) (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k) :
    ‖T‖ ^ (2 * q) ≤ ((Fintype.card D : ℝ) * Real.sqrt (Fintype.card D)) *
      ((2 * q * k + 1 : ℝ) * Real.sqrt (2 * q * k + 1)) *
        Real.sqrt ((wordMatrixVacuumExpectation (D := D) (ι := ι)
          ((star T * T) ^ (2 * q))).re) := by
  have hGram : ∀ i j, (star T * T) i j ∈ wordWickDegreeSpan (ι := ι) (2 * k) := by
    simpa only [two_mul] using
      mul_entries_mem_wordWickDegreeSpan (star_entries_mem_wordWickDegreeSpan hT) hT
  have hQ := pow_entries_mem_wordWickDegreeSpan hGram q
  have hQ' : ∀ i j, ((star T * T) ^ q) i j ∈
      wordWickDegreeSpan (ι := ι) (2 * q * k) := by
    have hdegree : q * (2 * k) = 2 * q * k := by ring
    simpa only [hdegree] using hQ
  have h := norm_le_wordMatrixVacuumL2_of_entries_mem_wordWickDegreeSpan
    (2 * q * k) ((star T * T) ^ q) hQ'
  have hSA : IsSelfAdjoint (star T * T) := IsSelfAdjoint.star_mul_self T
  have hnormGram : ‖star T * T‖ = ‖T‖ * ‖T‖ :=
    CStarRing.norm_star_mul_self (x := T)
  have hnorm : ‖(star T * T) ^ q‖ = ‖T‖ ^ (2 * q) := by
    rw [hSA.norm_pow_of_pos hq, hnormGram, ← pow_two, ← pow_mul]
  have hstar : star ((star T * T) ^ q) * (star T * T) ^ q = (star T * T) ^ (2 * q) := by
    rw [(hSA.pow q).star_eq, ← pow_add, ← two_mul]
  simpa only [hnorm, hstar, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

private theorem rpow_inv_two_mul_mul_sqrt {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    (x * Real.sqrt x) ^ ((2 * q)⁻¹) = x ^ (3 / (4 * q)) := by
  have hr : 0 ≤ (2 * q)⁻¹ := by positivity
  rw [Real.mul_rpow hx (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hx,
    ← Real.rpow_add_of_nonneg hx hr (by positivity)]
  congr 1
  field_simp
  ring

private theorem rpow_inv_two_mul_sqrt {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    (Real.sqrt x) ^ ((2 * q)⁻¹) = x ^ (1 / (4 * q)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  field_simp
  ring

/-- The source high-moment ultracontractive bound for actual amplified
operators of genuine degree at most k. The normalized even moment is the
actual amplified vacuum value. Empty dimension and zero operators are included. -/
theorem norm_le_wordMatrixVacuum_evenMoment_rpow [Fintype ι] (k q : ℕ) (hq : 0 < q)
    (T : M) (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k) :
    ‖T‖ ≤ (Fintype.card D : ℝ) ^ (3 / (4 * q : ℝ)) *
      (2 * q * k + 1 : ℝ) ^ (3 / (4 * q : ℝ)) *
        ((wordMatrixVacuumExpectation (D := D) (ι := ι)
          ((star T * T) ^ (2 * q))).re) ^ (1 / (4 * q : ℝ)) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hSA : IsSelfAdjoint (star T * T) := IsSelfAdjoint.star_mul_self T
  have hstar : star ((star T * T) ^ q) * (star T * T) ^ q = (star T * T) ^ (2 * q) := by
    rw [(hSA.pow q).star_eq, ← pow_add, ← two_mul]
  have hm : 0 ≤ (wordMatrixVacuumExpectation (D := D) (ι := ι)
      ((star T * T) ^ (2 * q))).re := by
    rw [← hstar]
    exact wordMatrixVacuumExpectation_star_mul_re_nonneg _
  have h := Real.rpow_le_rpow (z := (((2 * q : ℕ) : ℝ)⁻¹)) (by positivity)
    (norm_pow_le_wordMatrixVacuum_evenMoment k q hq T hT) (by positivity)
  rw [Real.pow_rpow_inv_natCast (norm_nonneg T) (by omega)] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _),
    Real.mul_rpow (by positivity) (by positivity),
    rpow_inv_two_mul_mul_sqrt (Nat.cast_nonneg _) hqR,
    rpow_inv_two_mul_mul_sqrt (by positivity) hqR,
    rpow_inv_two_mul_sqrt hm hqR] at h
  exact h

/-- Actual native matrix-coefficient polynomial evaluation satisfies the
literal source high-moment bound. Degree comes only from the original
canonical coefficient supports; all powered entry degrees are derived.

Source: Theorem 4.1 of arXiv:2406.11453v2. -/
theorem norm_wordMatrixPolynomialEvaluation_le_evenMoment_rpow [Fintype ι]
    (k q : ℕ) (hq : 0 < q) (P : Matrix D D (FreeAlgebra ℂ ι))
    (hdeg : ∀ i j, ∀ w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι) (P i j)).coeff.support,
        w.toList.length ≤ k) :
    ‖wordMatrixPolynomialEvaluation P‖ ≤
      (Fintype.card D : ℝ) ^ (3 / (4 * q : ℝ)) *
        (2 * q * k + 1 : ℝ) ^ (3 / (4 * q : ℝ)) *
          ((wordMatrixVacuumExpectation (D := D) (ι := ι)
            ((star (wordMatrixPolynomialEvaluation P) *
              wordMatrixPolynomialEvaluation P) ^ (2 * q))).re) ^ (1 / (4 * q : ℝ)) :=
  norm_le_wordMatrixVacuum_evenMoment_rpow k q hq _
    (wordMatrixPolynomialEvaluation_mem_wordWickDegreeSpan k P hdeg)

end NLAlib
