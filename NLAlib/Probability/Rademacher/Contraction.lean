import NLAlib.ForMathlib.Order.SupremumContraction
import NLAlib.ForMathlib.MeasureTheory.LinearSupremum
import NLAlib.ForMathlib.MeasureTheory.ContinuousSupremum
import NLAlib.ForMathlib.MeasureTheory.Integral
import NLAlib.Probability.Rademacher.RademacherSymmetry
import Mathlib.Data.Real.Pointwise

/-!
# Rademacher contraction over bounded parameter classes

The actual product sign law decreases expected suprema under coordinatewise
pairwise contraction. Parameter classes may be uncountable. Squaring tests
bounded by R costs exactly 2R, including zero radius and empty coordinate
families. The supremum is of the signed sum, without an outer absolute value.
This supports the empirical-process step for independent-sum spectral
universality; the full spectral target remains separate.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace NLAlib
variable {ι T : Type*} [Fintype ι] [DecidableEq ι] [Nonempty T]

omit [DecidableEq ι] in
/-- Uniformly bounded finite linear tests have an integrable supremum under
the actual independent sign law; the parameter class need not be countable. -/
theorem integrable_ciSup_sum_mul_rademacherVector_of_bounded
    (X : ι → T → ℝ) {R : ℝ} (hX : ∀ i t, |X i t| ≤ R) :
    Integrable (fun r : ι → ℝ => ⨆ t, ∑ i, r i * X i t) (rademacherVector ι) := by
  apply Integrable.of_bound (measurable_ciSup_sum_mul_of_bounded X hX).aestronglyMeasurable
    ((Fintype.card ι : ℝ) * R)
  filter_upwards [ae_norm_le_one_rademacherVector (κ := ι)] with r hr
  have ht (t : T) : |∑ i, r i * X i t| ≤ (Fintype.card ι : ℝ) * R := by
    calc
      _ ≤ ∑ i, |r i * X i t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, R := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hi : |r i| ≤ 1 := by
          simpa only [Real.norm_eq_abs] using (norm_le_pi_norm r i).trans hr
        exact (mul_le_mul hi (hX i t) (abs_nonneg _) (by norm_num)).trans_eq (one_mul R)
      _ = _ := by simp
  simpa only [Real.norm_eq_abs] using Real.abs_ciSup_le_of_abs_le _ ht

/-- Coordinatewise contraction of pairwise test differences decreases the
expected supremum under the actual finite product Rademacher measure.
There is no finiteness, countability, or measurability requirement on the
parameter class itself; uniform bounds imply measurability of the suprema.
This is the elementary Rademacher contraction principle. -/
theorem integral_ciSup_sum_mul_rademacherVector_le_of_abs_sub_le
    (X Y : ι → T → ℝ) {R S : ℝ}
    (hX : ∀ i t, |X i t| ≤ R) (hY : ∀ i t, |Y i t| ≤ S)
    (hcontract : ∀ i t u, |Y i t - Y i u| ≤ |X i t - X i u|) :
    (∫ r : ι → ℝ, ⨆ t, ∑ i, r i * Y i t ∂rademacherVector ι) ≤
      ∫ r : ι → ℝ, ⨆ t, ∑ i, r i * X i t ∂rademacherVector ι := by
  classical
  let A (s : Finset ι) (i : ι) (t : T) := if i ∈ s then Y i t else X i t
  have hA (s : Finset ι) (i : ι) (t : T) : |A s i t| ≤ max R S := by
    dsimp [A]
    split_ifs
    · exact (hY i t).trans (le_max_right R S)
    · exact (hX i t).trans (le_max_left R S)
  have hI (s : Finset ι) : Integrable
      (fun r : ι → ℝ => ⨆ t, ∑ i, r i * A s i t) (rademacherVector ι) :=
    integrable_ciSup_sum_mul_rademacherVector_of_bounded (A s) (hA s)
  have hstep (s : Finset ι) (i : ι) (hi : i ∉ s) :
      (∫ r : ι → ℝ, ⨆ t, ∑ j, r j * A (insert i s) j t ∂rademacherVector ι) ≤
        ∫ r : ι → ℝ, ⨆ t, ∑ j, r j * A s j t ∂rademacherVector ι := by
    rw [← integral_integral_update_pi (fun _ : ι => rademacherMeasure) i (hI (insert i s)),
      ← integral_integral_update_pi (fun _ : ι => rademacherMeasure) i (hI s)]
    apply integral_mono
      (integrable_integral_update_pi (fun _ : ι => rademacherMeasure) i (hI (insert i s)))
      (integrable_integral_update_pi (fun _ : ι => rademacherMeasure) i (hI s))
    intro r
    dsimp only []
    rw [integral_rademacherMeasure, integral_rademacherMeasure]
    let b (t : T) := ∑ j ∈ Finset.univ.erase i, r j * A s j t
    have hsplit (q : Finset ι) (v : ℝ) (t : T) :
        (∑ j, Function.update r i v j * A q j t) =
          (∑ j ∈ Finset.univ.erase i, r j * A q j t) + v * A q i t := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    have hsamerest (v : ℝ) (t : T) :
        (∑ j, Function.update r i v j * A (insert i s) j t) = b t + v * Y i t := by
      rw [hsplit]
      have hs : A (insert i s) i t = Y i t := by simp [A]
      rw [hs]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [A, Finset.mem_insert, hji, false_or]
    have hsameold (v : ℝ) (t : T) :
        (∑ j, Function.update r i v j * A s j t) = b t + v * X i t := by
      rw [hsplit]
      simp only [A, hi, if_false]
      rfl
    simp_rw [hsamerest, hsameold, one_mul, neg_one_mul, ← sub_eq_add_neg]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.ciSup_add_ciSup_le_of_abs_sub_le b (X i) (Y i)
    · refine ⟨(∑ j ∈ Finset.univ.erase i, |r j| * max R S) + R, ?_⟩
      rintro _ ⟨t, rfl⟩
      apply add_le_add _ ((le_abs_self _).trans (hX i t))
      dsimp [b]
      apply Finset.sum_le_sum
      intro j _
      exact (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
        mul_le_mul_of_nonneg_left (hA s j t) (abs_nonneg _)
    · refine ⟨(∑ j ∈ Finset.univ.erase i, |r j| * max R S) + R, ?_⟩
      rintro _ ⟨t, rfl⟩
      change b t + -(X i t) ≤ _
      apply add_le_add _ ((neg_le_abs _).trans (hX i t))
      dsimp [b]
      apply Finset.sum_le_sum
      intro j _
      exact (le_abs_self _).trans <| (abs_mul _ _).trans_le <|
        mul_le_mul_of_nonneg_left (hA s j t) (abs_nonneg _)
    · exact hcontract i
  have hind (s : Finset ι) :
      (∫ r : ι → ℝ, ⨆ t, ∑ i, r i * A s i t ∂rademacherVector ι) ≤
        ∫ r : ι → ℝ, ⨆ t, ∑ i, r i * A ∅ i t ∂rademacherVector ι := by
    induction s using Finset.induction_on with
    | empty => exact le_rfl
    | @insert i s hi ih => exact (hstep s i hi).trans ih
  simpa only [A, Finset.mem_univ, Finset.notMem_empty, if_true, if_false] using hind Finset.univ

/-- Squaring bounded tests costs exactly twice their uniform radius in the
expected Rademacher supremum. The parameter class can be uncountable, and
the empty coordinate family and zero radius are included. -/
theorem integral_ciSup_sum_mul_sq_rademacherVector_le
    (X : ι → T → ℝ) {R : ℝ} (hR : 0 ≤ R) (hX : ∀ i t, |X i t| ≤ R) :
    (∫ r : ι → ℝ, ⨆ t, ∑ i, r i * X i t ^ 2 ∂rademacherVector ι) ≤
      2 * R * ∫ r : ι → ℝ, ⨆ t, ∑ i, r i * X i t ∂rademacherVector ι := by
  have hscaled (i : ι) (t : T) : |2 * R * X i t| ≤ 2 * R ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
    nlinarith [mul_le_mul_of_nonneg_left (hX i t) (by positivity : 0 ≤ 2 * R)]
  have hsquare (i : ι) (t : T) : |X i t ^ 2| ≤ R ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hX i t)
  have hdiff (i : ι) (t u : T) :
      |X i t ^ 2 - X i u ^ 2| ≤ |2 * R * X i t - 2 * R * X i u| := by
    have hs : |X i t + X i u| ≤ 2 * R :=
      (abs_add_le _ _).trans (by linarith [hX i t, hX i u])
    calc
      _ = |X i t - X i u| * |X i t + X i u| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |X i t - X i u| * (2 * R) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
        ring
  have h := integral_ciSup_sum_mul_rademacherVector_le_of_abs_sub_le
    (fun i t => 2 * R * X i t) (fun i t => X i t ^ 2) hscaled hsquare hdiff
  have he (r : ι → ℝ) :
      (⨆ t, ∑ i, r i * (2 * R * X i t)) = 2 * R * (⨆ t, ∑ i, r i * X i t) := by
    rw [Real.mul_iSup_of_nonneg (by positivity : 0 ≤ 2 * R)]
    congr 1
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he] at h
  rw [integral_const_mul] at h
  exact h

end NLAlib
