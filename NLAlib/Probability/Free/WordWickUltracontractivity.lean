import NLAlib.Probability.Free.WordWickHomogeneous
import NLAlib.ForMathlib.Analysis.NormSumSq
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual bounded-degree Wick ultracontractivity

The estimate is in terms of the actual Hilbert norm of the operator applied
to the vacuum. The finite coefficient mass is identified with that norm
using the actual orthonormal word vectors. No comparison norm is a premise.
The constant `(k+1)*sqrt(k+1)` is `(k+1)^(3/2)` in source Lemma 4.5 of
arXiv:2406.11453v2.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical lp InnerProduct

namespace NLAlib

/-- Native indices for all words of degree at most `k`. -/
abbrev WordWickDegreeIndex (ι : Type*) (k : ℕ) :=
  Σ m : Fin (k + 1), List.Vector ι m

variable {ι : Type*}
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W

private theorem wordWickDegreeIndex_toList_injective (k : ℕ) :
    Function.Injective (fun w : WordWickDegreeIndex ι k => w.2.toList) := by
  rintro ⟨m, u⟩ ⟨n, v⟩ h
  have hmn : m = n := Fin.ext (by
    have hlen := congrArg List.length h
    simpa using hlen)
  subst n
  congr 1
  exact Subtype.ext h

private theorem orthonormal_wordWickDegreeBasis (k : ℕ) :
    Orthonormal ℂ (fun w : WordWickDegreeIndex ι k =>
      (lp.single 2 w.2.toList 1 : W)) := by
  rw [orthonormal_iff_ite]
  intro u v
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply,
    (wordWickDegreeIndex_toList_injective (ι := ι) k).eq_iff]

/-- The actual vacuum squared norm is exactly the coefficient ℓ² mass
for a bounded-degree Wick sum, with no distribution premise. -/
theorem norm_sum_wordWickOperator_wordVacuum_sq [Fintype ι] (k : ℕ)
    (a : WordWickDegreeIndex ι k → ℂ) :
    ‖(∑ w, a w • wordWickOperator w.2.toList) (wordVacuum ι)‖ ^ 2 =
      ∑ w, ‖a w‖ ^ 2 := by
  have h := (orthonormal_wordWickDegreeBasis (ι := ι) k).orthogonalFamily.norm_sum
    a Finset.univ
  simpa only [sum_apply, smul_apply, wordWickOperator_wordVacuum,
    LinearIsometry.toSpanSingleton_apply] using h

/-- The genuine bounded-degree Wick estimate in terms of actual vacuum L².
Degree zero and an empty alphabet are both included. -/
theorem norm_sum_wordWickOperator_le_mul_sqrt_vacuum [Fintype ι] (k : ℕ)
    (a : WordWickDegreeIndex ι k → ℂ) :
    ‖∑ w, a w • wordWickOperator w.2.toList‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(∑ w, a w • wordWickOperator w.2.toList) (wordVacuum ι)‖ := by
  let b : Fin (k + 1) → ℝ := fun m => Real.sqrt (∑ w : List.Vector ι m, ‖a ⟨m, w⟩‖ ^ 2)
  let T : B := ∑ w, a w • wordWickOperator w.2.toList
  have hb (m : Fin (k + 1)) : 0 ≤ b m := Real.sqrt_nonneg _
  have hb2 (m : Fin (k + 1)) : (b m) ^ 2 = ∑ w : List.Vector ι m, ‖a ⟨m, w⟩‖ ^ 2 := by
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hmass : ∑ m, (b m) ^ 2 = ‖T (wordVacuum ι)‖ ^ 2 := by
    simp_rw [hb2]
    rw [← Fintype.sum_sigma']
    exact (norm_sum_wordWickOperator_wordVacuum_sq k a).symm
  have hcs : (∑ m, b m) ^ 2 ≤ (k + 1 : ℝ) * ‖T (wordVacuum ι)‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, hmass] using h
  have hsum : ∑ m, b m ≤ Real.sqrt (k + 1) * ‖T (wordVacuum ι)‖ := by
    have hk : 0 ≤ (k + 1 : ℝ) := by positivity
    have hright : 0 ≤ Real.sqrt (k + 1) * ‖T (wordVacuum ι)‖ := by positivity
    have hrightsq : (Real.sqrt (k + 1) * ‖T (wordVacuum ι)‖) ^ 2 =
        (k + 1 : ℝ) * ‖T (wordVacuum ι)‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hk]
    nlinarith
  change ‖T‖ ≤ _
  calc
    ‖T‖ = ‖∑ m : Fin (k + 1), ∑ w : List.Vector ι m,
        a ⟨m, w⟩ • wordWickOperator w.toList‖ := by simp only [T, Fintype.sum_sigma]
    _ ≤ ∑ m : Fin (k + 1), ‖∑ w : List.Vector ι m,
        a ⟨m, w⟩ • wordWickOperator w.toList‖ := norm_sum_le _ _
    _ ≤ ∑ m : Fin (k + 1), (m + 1 : ℝ) * b m := by
      apply Finset.sum_le_sum
      intro m _
      exact norm_sum_wordWickOperator_le m (fun w => a ⟨m, w⟩)
    _ ≤ ∑ m : Fin (k + 1), (k + 1 : ℝ) * b m := by
      apply Finset.sum_le_sum
      intro m _
      apply mul_le_mul_of_nonneg_right _ (hb m)
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ m.isLt)
    _ = (k + 1 : ℝ) * ∑ m, b m := by rw [Finset.mul_sum]
    _ ≤ (k + 1 : ℝ) * (Real.sqrt (k + 1) * ‖T (wordVacuum ι)‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := mul_assoc _ _ _ |>.symm

/-- The actual finite-dimensional space of Wick polynomials of degree at
most `k`, inside the native bounded operators. -/
def wordWickDegreeSpan (k : ℕ) : Submodule ℂ B :=
  Submodule.span ℂ (Set.range (fun w : WordWickDegreeIndex ι k => wordWickOperator w.2.toList))

/-- Every actual bounded-degree Wick polynomial has the source scalar
ultracontractive bound; the right side is its genuine vacuum Hilbert norm. -/
theorem norm_le_mul_sqrt_vacuum_of_mem_wordWickDegreeSpan [Fintype ι]
    {k : ℕ} {T : B} (hT : T ∈ wordWickDegreeSpan (ι := ι) k) :
    ‖T‖ ≤ (k + 1 : ℝ) * Real.sqrt (k + 1) * ‖T (wordVacuum ι)‖ := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hT
  exact norm_sum_wordWickOperator_le_mul_sqrt_vacuum k a

end NLAlib
