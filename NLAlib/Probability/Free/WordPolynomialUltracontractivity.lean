import NLAlib.Probability.Free.WordWickUltracontractivity
import Mathlib.Algebra.FreeAlgebra

/-!
# Scalar noncommutative polynomial ultracontractivity for actual word fields

Multiplication of a Wick word by a field creates its initial letter and
contracts at most its initial letter. Consequently every genuine ordinary
word of length at most `k` belongs to the actual degree-`k` Wick span. This
derives the scalar source estimate for native free-algebra evaluation, with
degree expressed by the support of its canonical free-monoid coefficients.

Source: Lemma 4.5 of arXiv:2406.11453v2. Neither a Wick expansion nor an
operator-norm comparison is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace NLAlib

variable {ι : Type*}
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W

/-- Every actual Wick word is in the actual degree span up to its length. -/
theorem wordWickOperator_mem_wordWickDegreeSpan (w : List ι) {k : ℕ}
    (hlen : w.length ≤ k) : wordWickOperator w ∈ wordWickDegreeSpan (ι := ι) k := by
  apply Submodule.subset_span
  exact ⟨⟨⟨w.length, Nat.lt_succ_of_le hlen⟩, ⟨w, rfl⟩⟩, rfl⟩

/-- Genuine degree spans are nested. -/
theorem wordWickDegreeSpan_mono {j k : ℕ} (hjk : j ≤ k) :
    wordWickDegreeSpan (ι := ι) j ≤ wordWickDegreeSpan (ι := ι) k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨m, w⟩, rfl⟩
  apply wordWickOperator_mem_wordWickDegreeSpan
  have hw : w.toList.length = (m : ℕ) := by simp
  rw [hw]
  exact (Nat.le_of_lt_succ m.isLt).trans hjk

/-- The actual field times a nonempty Wick word has precisely one possible
initial-letter contraction. This is a literal operator identity. -/
theorem wordField_mul_wordWickOperator_cons (i j : ι) (w : List ι) :
    wordField i * wordWickOperator (j :: w) =
      wordWickOperator (i :: j :: w) + if i = j then wordWickOperator w else 0 := by
  change wordField i * wordWickOperator (j :: w) =
    (wordField i * wordWickOperator (j :: w) -
      if i = j then wordWickOperator w else 0) +
        if i = j then wordWickOperator w else 0
  exact (sub_add_cancel _ _).symm

private theorem wordField_mul_wordWickOperator_mem (i : ι) (w : List ι) :
    wordField i * wordWickOperator w ∈ wordWickDegreeSpan (ι := ι) (w.length + 1) := by
  cases w with
  | nil =>
    simpa only [wordWickOperator, mul_one, List.length_nil, zero_add] using
      (wordWickOperator_mem_wordWickDegreeSpan [i] (by simp : [i].length ≤ 1))
  | cons j w =>
    rw [wordField_mul_wordWickOperator_cons]
    apply Submodule.add_mem
    · exact wordWickOperator_mem_wordWickDegreeSpan _ (by simp)
    · by_cases hij : i = j
      · rw [if_pos hij]
        exact wordWickOperator_mem_wordWickDegreeSpan _ (by simp; omega)
      · rw [if_neg hij]
        exact Submodule.zero_mem _

/-- Multiplication by an actual field raises genuine Wick degree by at
most one. This conclusion is proved from the literal contraction identity. -/
theorem wordField_mul_mem_wordWickDegreeSpan (i : ι) {k : ℕ} {T : B}
    (hT : T ∈ wordWickDegreeSpan (ι := ι) k) :
    wordField i * T ∈ wordWickDegreeSpan (ι := ι) (k + 1) := by
  let L : B →ₗ[ℂ] B :=
    { toFun := fun T => wordField i * T
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  have hspan : wordWickDegreeSpan (ι := ι) k ≤
      (wordWickDegreeSpan (ι := ι) (k + 1)).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨m, w⟩, rfl⟩
    change wordField i * wordWickOperator w.toList ∈ wordWickDegreeSpan (ι := ι) (k + 1)
    apply wordWickDegreeSpan_mono (k := k + 1) _ (wordField_mul_wordWickOperator_mem i w.toList)
    have hw : w.toList.length = (m : ℕ) := by simp
    rw [hw]
    exact Nat.succ_le_succ (Nat.le_of_lt_succ m.isLt)
  exact hspan hT

/-- An actual ordered product of fields has genuine Wick degree at most
its number of factors. No expansion or norm conclusion is a premise. -/
theorem list_prod_wordField_mem_wordWickDegreeSpan (w : List ι) :
    (w.map wordField).prod ∈ wordWickDegreeSpan (ι := ι) w.length := by
  induction w with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, List.length_nil, wordWickOperator] using
      (wordWickOperator_mem_wordWickDegreeSpan ([] : List ι)
        (by simp : ([] : List ι).length ≤ 0))
  | cons i w hw =>
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.succ_eq_add_one] using
      wordField_mul_mem_wordWickDegreeSpan i hw

/-- Actual finite word-polynomial evaluation obeys the source scalar
ultracontractive estimate, with degree read from the genuine finite support. -/
theorem norm_finsupp_sum_list_prod_wordField_le [Fintype ι] (k : ℕ)
    (a : List ι →₀ ℂ) (hdeg : ∀ w ∈ a.support, w.length ≤ k) :
    ‖a.sum (fun w z => z • (w.map wordField).prod)‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(a.sum (fun w z => z • (w.map wordField).prod)) (wordVacuum ι)‖ := by
  apply norm_le_mul_sqrt_vacuum_of_mem_wordWickDegreeSpan
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordWickDegreeSpan_mono (hdeg w hw) (list_prod_wordField_mem_wordWickDegreeSpan w)

/-- Native free-monoid algebra evaluation has the scalar degree-dependent
bound, with its actual canonical finite coefficient support. -/
theorem norm_monoidAlgebra_lift_wordField_le [Fintype ι] (k : ℕ)
    (P : MonoidAlgebra ℂ (FreeMonoid ι))
    (hdeg : ∀ w ∈ P.coeff.support, w.toList.length ≤ k) :
    ‖MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField) P‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField) P) (wordVacuum ι)‖ := by
  simp only [MonoidAlgebra.lift_apply, FreeMonoid.lift_apply]
  apply norm_le_mul_sqrt_vacuum_of_mem_wordWickDegreeSpan
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordWickDegreeSpan_mono (hdeg w hw) (list_prod_wordField_mem_wordWickDegreeSpan w.toList)

/-- Genuine native free-algebra evaluation satisfies the scalar source
degree-`k` ultracontractive estimate. The degree premise is exactly a bound
on the lengths in the canonical free-monoid coefficient support. -/
theorem norm_freeAlgebra_lift_wordField_le [Fintype ι] (k : ℕ) (P : FreeAlgebra ℂ ι)
    (hdeg : ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι) P).coeff.support,
      w.toList.length ≤ k) :
    ‖FreeAlgebra.lift ℂ (wordField : ι → B) P‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(FreeAlgebra.lift ℂ (wordField : ι → B) P) (wordVacuum ι)‖ := by
  have hEval : FreeAlgebra.lift ℂ (wordField : ι → B) =
      (MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField)).comp
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι)).toAlgHom := by
    ext i
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hEval, AlgHom.comp_apply]
  exact norm_monoidAlgebra_lift_wordField_le k _ hdeg

end NLAlib
