import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic

/-!
# Entry power sums and row variance profiles

Finite Hölder and weighted arithmetic--geometric mean convert the entry
`l^p` profile into the row-variance and row-maximum profiles. The estimates
hold for every real exponent at least two with a dimension-free constant.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The entry power sum is bounded by the geometric interpolation of the
row-variance and row-maximum power sums, for every real exponent at least two. -/
theorem sum_entry_rpow_le_row_profiles
    (b : Matrix m n ℝ) (hb : ∀ i j, 0 ≤ b i j) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, ∑ j, b i j ^ p) ≤
      (∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ (2 / p) *
        (∑ i, ‖b i‖ ^ p) ^ (1 - 2 / p) := by
  classical
  by_cases hp2 : p = 2
  · subst p
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), sub_self, Real.rpow_one,
      Real.rpow_zero, mul_one, Real.rpow_two]
    exact le_rfl
  have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
  have hp0 : 0 < p := lt_trans (by norm_num) hpgt
  have hpm : 0 < p - 2 := sub_pos.mpr hpgt
  have hdeg (i : m) : 0 ≤ ∑ j, b i j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hentry (i : m) (j : n) : b i j ^ p ≤ b i j ^ 2 * ‖b i‖ ^ (p - 2) := by
    have hcap : b i j ≤ ‖b i‖ := by
      simpa only [Real.norm_of_nonneg (hb i j)] using norm_le_pi_norm (b i) j
    have hpow : b i j ^ p = b i j ^ 2 * b i j ^ (p - 2) := by
      have hx := Real.rpow_add_of_nonneg (hb i j) (by norm_num : (0 : ℝ) ≤ 2) hpm.le
      have he : (2 : ℝ) + (p - 2) = p := by ring
      simpa only [he, Real.rpow_two] using hx
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hb i j) hcap hpm.le) (sq_nonneg _)
  have hfirst : (∑ i, ∑ j, b i j ^ p) ≤
      ∑ i, (∑ j, b i j ^ 2) * ‖b i‖ ^ (p - 2) := by
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hentry i j
  have hh : Real.HolderConjugate (p / 2) (p / (p - 2)) :=
    Real.holderConjugate_iff.mpr ⟨by linarith, by field_simp; ring⟩
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset m)
    (f := fun i => ∑ j, b i j ^ 2) (g := fun i => ‖b i‖ ^ (p - 2)) hh
    (fun i _ => hdeg i) (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hterm (i : m) : (‖b i‖ ^ (p - 2)) ^ (p / (p - 2)) = ‖b i‖ ^ p := by
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  simp_rw [hterm] at hholder
  have he₁ : 1 / (p / 2) = 2 / p := by field_simp
  have he₂ : 1 / (p / (p - 2)) = 1 - 2 / p := by field_simp
  rw [he₁, he₂] at hholder
  exact hfirst.trans hholder

/-- The rooted entry profile is bounded by the geometric interpolation of
the rooted row-variance and row-maximum profiles. -/
theorem sum_entry_rpow_root_le_row_profiles
    (b : Matrix m n ℝ) (hb : ∀ i j, 0 ≤ b i j) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, ∑ j, b i j ^ p) ^ p⁻¹ ≤
      ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹) ^ (2 / p) *
        ((∑ i, ‖b i‖ ^ p) ^ p⁻¹) ^ (1 - 2 / p) := by
  have hD : 0 ≤ ∑ i, (∑ j, b i j ^ 2) ^ (p / 2) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _
  have hS : 0 ≤ ∑ i, ‖b i‖ ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hb i j) _)
    (sum_entry_rpow_le_row_profiles b hb hp) (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ p))
  rw [Real.mul_rpow (Real.rpow_nonneg hD _) (Real.rpow_nonneg hS _),
    ← Real.rpow_mul hD, ← Real.rpow_mul hS] at h
  simpa only [← Real.rpow_mul hD, ← Real.rpow_mul hS, mul_comm p⁻¹] using h

/-- Uniform conversion of the entry profile into the exact two profiles in
the Gaussian Schatten theorem. The constant is independent of the exponent
and of both matrix dimensions. -/
theorem sqrt_mul_sum_entry_rpow_root_le_two_row_profiles
    (b : Matrix m n ℝ) (hb : ∀ i j, 0 ≤ b i j) {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt p * (∑ i, ∑ j, b i j ^ p) ^ p⁻¹ ≤
      2 * ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
        Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹) := by
  let A := (∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹
  let B := (∑ i, ‖b i‖ ^ p) ^ p⁻¹
  have hA : 0 ≤ A := Real.rpow_nonneg
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _) _
  have hB : 0 ≤ B := Real.rpow_nonneg
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hp0 : 0 < p := by linarith
  have hw : 0 ≤ 1 - 2 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp)
  have hagm := Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by norm_num) hp0.le) hw
    hA hB (by ring : 2 / p + (1 - 2 / p) = 1)
  have h := (sum_entry_rpow_root_le_row_profiles b hb hp).trans hagm
  have hrootp : 1 ≤ Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ p)
  have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp0.le
  have hcoef : Real.sqrt p * (2 / p) ≤ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hp0]
    nlinarith
  have hbcoef : Real.sqrt p * (1 - 2 / p) ≤ Real.sqrt p := by
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0.le, Real.sqrt_nonneg p]
  have hh := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg p)
  change Real.sqrt p * _ ≤ 2 * (A + Real.sqrt p * B)
  calc
    _ ≤ Real.sqrt p * ((2 / p) * A + (1 - 2 / p) * B) := hh
    _ ≤ 2 * A + Real.sqrt p * B := by
      calc
        _ = (Real.sqrt p * (2 / p)) * A + (Real.sqrt p * (1 - 2 / p)) * B := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoef hA) (mul_le_mul_of_nonneg_right hbcoef hB)
    _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg p) hB]

end NLAlib
