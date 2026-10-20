import NLAlib.Probability.Free.WordPolynomialUltracontractivity

/-!
# Genuine degree operations on the concrete word-field algebra

The Wick degree space equals the span of actual ordered field monomials of
bounded length. Adjoint reverses those genuine products, and multiplication
concatenates them. These are proved operator statements, independent of any
star convention on a formal free algebra.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace NLAlib

variable {ι : Type*}
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W

private def wordFieldDegreeSpan (k : ℕ) : Submodule ℂ B :=
  Submodule.span ℂ {T | ∃ w : List ι, w.length ≤ k ∧ T = (w.map wordField).prod}

private theorem list_prod_mem_wordFieldDegreeSpan (w : List ι) {k : ℕ} (hw : w.length ≤ k) :
    (w.map wordField).prod ∈ wordFieldDegreeSpan (ι := ι) k :=
  Submodule.subset_span ⟨w, hw, rfl⟩

private theorem wordFieldDegreeSpan_mono {j k : ℕ} (hjk : j ≤ k) :
    wordFieldDegreeSpan (ι := ι) j ≤ wordFieldDegreeSpan (ι := ι) k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  exact list_prod_mem_wordFieldDegreeSpan w (hw.trans hjk)

private theorem mul_mem_wordFieldDegreeSpan {j k : ℕ} {S T : B}
    (hS : S ∈ wordFieldDegreeSpan (ι := ι) j)
    (hT : T ∈ wordFieldDegreeSpan (ι := ι) k) :
    S * T ∈ wordFieldDegreeSpan (ι := ι) (j + k) := by
  refine Submodule.span_induction₂
    (p := fun S T _ _ => S * T ∈ wordFieldDegreeSpan (ι := ι) (j + k))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS hT
  · rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    simpa only [List.map_append, List.prod_append] using
      list_prod_mem_wordFieldDegreeSpan (u ++ v) (by simp; omega : (u ++ v).length ≤ j + k)
  · intro _ _; simp only [zero_mul]; exact Submodule.zero_mem _
  · intro _ _; simp only [mul_zero]; exact Submodule.zero_mem _
  · intro _ _ _ _ _ _ h1 h2
    simpa only [add_mul] using Submodule.add_mem _ h1 h2
  · intro _ _ _ _ _ _ h1 h2
    simpa only [mul_add] using Submodule.add_mem _ h1 h2
  · intro c _ _ _ _ h
    simpa only [smul_mul_assoc] using Submodule.smul_mem _ c h
  · intro c _ _ _ _ h
    simpa only [mul_smul_comm] using Submodule.smul_mem _ c h

private theorem star_list_prod_wordField (w : List ι) :
    star (w.map wordField).prod = (w.reverse.map wordField).prod := by
  induction w with
  | nil => simp
  | cons i w hw =>
    simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, hw,
      (isSelfAdjoint_wordField i).star_eq]

private theorem star_mem_wordFieldDegreeSpan {k : ℕ} {T : B}
    (hT : T ∈ wordFieldDegreeSpan (ι := ι) k) :
    star T ∈ wordFieldDegreeSpan (ι := ι) k := by
  induction hT using Submodule.span_induction with
  | mem _ h =>
    rcases h with ⟨w, hw, rfl⟩
    rw [star_list_prod_wordField]
    exact list_prod_mem_wordFieldDegreeSpan w.reverse (by simpa using hw)
  | zero => simp only [star_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => simpa only [star_add] using Submodule.add_mem _ h1 h2
  | smul c _ _ h => simpa only [star_smul] using Submodule.smul_mem _ (star c) h

private theorem wordWickOperator_mem_wordFieldDegreeSpan (w : List ι) :
    wordWickOperator w ∈ wordFieldDegreeSpan (ι := ι) w.length := by
  induction w using List.twoStepInduction with
  | nil =>
    simpa only [wordWickOperator, List.map_nil, List.prod_nil] using
      list_prod_mem_wordFieldDegreeSpan ([] : List ι) le_rfl
  | singleton i =>
    simpa only [wordWickOperator, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using list_prod_mem_wordFieldDegreeSpan [i] le_rfl
  | cons_cons i j w hw hcons =>
    change wordField i * wordWickOperator (j :: w) -
      (if i = j then wordWickOperator w else 0) ∈ _
    apply Submodule.sub_mem
    · have hi : wordField i ∈ wordFieldDegreeSpan (ι := ι) 1 := by
        simpa using list_prod_mem_wordFieldDegreeSpan [i] le_rfl
      simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_comm 1] using
        mul_mem_wordFieldDegreeSpan hi (hcons j)
    · by_cases hij : i = j
      · rw [if_pos hij]
        exact wordFieldDegreeSpan_mono (by simp; omega) hw
      · rw [if_neg hij]
        exact Submodule.zero_mem _

private theorem wordFieldDegreeSpan_eq_wordWickDegreeSpan (k : ℕ) :
    wordFieldDegreeSpan (ι := ι) k = wordWickDegreeSpan (ι := ι) k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact wordWickDegreeSpan_mono hw (list_prod_wordField_mem_wordWickDegreeSpan w)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨m, w⟩, rfl⟩
    apply wordFieldDegreeSpan_mono _ (wordWickOperator_mem_wordFieldDegreeSpan w.toList)
    have hw : w.toList.length = (m : ℕ) := by simp
    rw [hw]
    exact Nat.le_of_lt_succ m.isLt

/-- Genuine bounded-degree word operators are closed under their actual
Hilbert adjoint; scalar coefficients are conjugated by the native star. -/
theorem star_mem_wordWickDegreeSpan {k : ℕ} {T : B}
    (hT : T ∈ wordWickDegreeSpan (ι := ι) k) :
    star T ∈ wordWickDegreeSpan (ι := ι) k := by
  rw [← wordFieldDegreeSpan_eq_wordWickDegreeSpan] at hT ⊢
  exact star_mem_wordFieldDegreeSpan hT

/-- Multiplication adds genuine word degree, proved by actual ordered-word
concatenation and equality with the Wick span. -/
theorem mul_mem_wordWickDegreeSpan {j k : ℕ} {S T : B}
    (hS : S ∈ wordWickDegreeSpan (ι := ι) j)
    (hT : T ∈ wordWickDegreeSpan (ι := ι) k) :
    S * T ∈ wordWickDegreeSpan (ι := ι) (j + k) := by
  rw [← wordFieldDegreeSpan_eq_wordWickDegreeSpan] at hS hT ⊢
  exact mul_mem_wordFieldDegreeSpan hS hT

end NLAlib
