import NLAlib.Polynomial.FunctionApproximation.BernsteinEllipse
import NLAlib.ForMathlib.Algebra.Reciprocal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Geometric bounds for Bernstein ellipses

Complete the canonical Joukowski definitions with their focal-distance
characterisation and scalar bounds. Realises `bernstein-ellipse-def`.
-/

noncomputable section

open Complex Set Polynomial Polynomial.Chebyshev
open scoped Topology

namespace NLAlib

/-- The focal-distance sum of a Joukowski image is the radius plus its reciprocal.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
Helper for `bernstein-ellipse-def`. -/
theorem norm_joukowski_sub_one_add_norm_joukowski_add_one {w : ℂ} (hw : w ≠ 0) :
    ‖joukowski w - 1‖ + ‖joukowski w + 1‖ = ‖w‖ + ‖w‖⁻¹ := by
  have hm : joukowski w - 1 = (w - 1) ^ 2 / (2 * w) := by
    dsimp [joukowski]
    field_simp
    ring
  have hp : joukowski w + 1 = (w + 1) ^ 2 / (2 * w) := by
    dsimp [joukowski]
    field_simp
    ring
  have hsum : ‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2 = 2 * (‖w‖ ^ 2 + 1) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_add,
      Complex.normSq_one]
    ring
  rw [hm, hp, norm_div, norm_div, norm_pow, norm_pow, norm_mul]
  norm_num
  rw [← add_div, hsum]
  field_simp

/-- Every complex point is a Joukowski image with radius at least one.
Source: the quadratic equation `w²-2zw+1=0`; operator derivations §4.
Helper for `bernstein-ellipse-def`. -/
theorem exists_one_le_norm_joukowski_eq (z : ℂ) :
    ∃ w : ℂ, 1 ≤ ‖w‖ ∧ joukowski w = z := by
  let p : ℂ[X] := X ^ 2 - C (2 * z) * X + 1
  have hdeg : p.degree = 2 := by dsimp [p]; compute_degree <;> norm_num
  obtain ⟨w, hw⟩ := Complex.exists_root (show 0 < p.degree by rw [hdeg]; norm_num)
  have heq : w ^ 2 - 2 * z * w + 1 = 0 := by simpa [p, Polynomial.IsRoot] using hw
  have hw0 : w ≠ 0 := by intro h; simp [h] at heq
  have hJ : joukowski w = z := by
    dsimp [joukowski]
    field_simp
    linear_combination heq
  by_cases hnorm : 1 ≤ ‖w‖
  · exact ⟨w, hnorm, hJ⟩
  · refine ⟨w⁻¹, ?_, (joukowski_inv w).trans hJ⟩
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hw0)).mpr (le_of_not_ge hnorm)

/-- The canonical open ellipse consists exactly of Joukowski images with radius
in `[1,ρ)`. Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
Helper for `bernstein-ellipse-def`. -/
theorem openBernsteinEllipse_eq_image_one_le_norm {ρ : ℝ} (hρ : 1 < ρ) :
    openBernsteinEllipse ρ = joukowski '' {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ < ρ} := by
  apply Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    by_cases hnorm : 1 ≤ ‖w‖
    · exact ⟨w, ⟨hnorm, hw.2⟩, rfl⟩
    · have hwpos : 0 < ‖w‖ := lt_trans (inv_pos.mpr (zero_lt_one.trans hρ)) hw.1
      refine ⟨w⁻¹, ⟨?_, ?_⟩, joukowski_inv w⟩
      · rw [norm_inv]
        exact (one_le_inv₀ hwpos).mpr (le_of_not_ge hnorm)
      · rw [norm_inv]
        exact (inv_lt_comm₀ hwpos (zero_lt_one.trans hρ)).mpr hw.1
  · rintro z ⟨w, hw, rfl⟩
    refine ⟨w, ⟨?_, hw.2⟩, rfl⟩
    exact ((inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ).trans_le hw.1

/-- The open Bernstein ellipse has the usual focal-distance description.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem mem_openBernsteinEllipse_iff {ρ : ℝ} (hρ : 1 < ρ) (z : ℂ) :
    z ∈ openBernsteinEllipse ρ ↔ ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹ := by
  obtain ⟨w, hw, rfl⟩ := exists_one_le_norm_joukowski_eq z
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  rw [norm_joukowski_sub_one_add_norm_joukowski_add_one hw0]
  constructor
  · intro hz
    rw [openBernsteinEllipse_eq_image_one_le_norm hρ] at hz
    obtain ⟨v, hv, hJ⟩ := hz
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by linarith [hv.1])
    have hnorm : ‖v‖ + ‖v‖⁻¹ = ‖w‖ + ‖w‖⁻¹ := by
      rw [← norm_joukowski_sub_one_add_norm_joukowski_add_one hv0, hJ,
        norm_joukowski_sub_one_add_norm_joukowski_add_one hw0]
    rw [← hnorm]
    exact strictMonoOn_add_inv_Ici_one hv.1 hρ.le hv.2
  · intro hdist
    have hrad : ‖w‖ < ρ := by
      by_contra h
      have hle := strictMonoOn_add_inv_Ici_one.monotoneOn hρ.le hw (le_of_not_gt h)
      linarith
    rw [openBernsteinEllipse_eq_image_one_le_norm hρ]
    exact ⟨w, ⟨hw, hrad⟩, rfl⟩

/-- Bernstein ellipse interiors are open in the complex plane.
Source: Trefethen, ATAP, Ch. 8; focal-distance characterisation.
atlas: bernstein-ellipse-def -/
theorem isOpen_openBernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ) :
    IsOpen (openBernsteinEllipse ρ) := by
  have heq : openBernsteinEllipse ρ = {z : ℂ | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹} := by
    ext z
    exact mem_openBernsteinEllipse_iff hρ z
  rw [heq]
  exact isOpen_lt (by fun_prop) continuous_const

/-- Bernstein ellipse interiors increase with their radius.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem openBernsteinEllipse_mono {r ρ : ℝ} (hr : 1 < r) (hrρ : r ≤ ρ) :
    openBernsteinEllipse r ⊆ openBernsteinEllipse ρ := by
  intro z hz
  rw [mem_openBernsteinEllipse_iff hr z] at hz
  rw [mem_openBernsteinEllipse_iff (hr.trans_le hrρ) z]
  exact hz.trans_le (strictMonoOn_add_inv_Ici_one.monotoneOn hr.le (hr.le.trans hrρ) hrρ)

/-- Every open Bernstein ellipse of radius greater than one contains the real unit interval.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem ofReal_mem_openBernsteinEllipse {ρ x : ℝ} (hρ : 1 < ρ)
    (hx : x ∈ Icc (-1 : ℝ) 1) : (x : ℂ) ∈ openBernsteinEllipse ρ :=
  filledBernsteinEllipse_subset_openBernsteinEllipse hρ hρ
    (ofReal_mem_filledBernsteinEllipse (ρ := 1) le_rfl hx)

/-- The filled Bernstein ellipse has the closed focal-distance description.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
Helper for `bernstein-ellipse-def`. -/
theorem mem_filledBernsteinEllipse_iff {ρ : ℝ} (hρ : 1 ≤ ρ) (z : ℂ) :
    z ∈ filledBernsteinEllipse ρ ↔ ‖z - 1‖ + ‖z + 1‖ ≤ ρ + ρ⁻¹ := by
  obtain ⟨w, hw, rfl⟩ := exists_one_le_norm_joukowski_eq z
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  rw [norm_joukowski_sub_one_add_norm_joukowski_add_one hw0]
  constructor
  · rintro ⟨v, hv, hJ⟩
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by linarith [hv.1])
    have hnorm : ‖v‖ + ‖v‖⁻¹ = ‖w‖ + ‖w‖⁻¹ := by
      rw [← norm_joukowski_sub_one_add_norm_joukowski_add_one hv0, hJ,
        norm_joukowski_sub_one_add_norm_joukowski_add_one hw0]
    rw [← hnorm]
    exact strictMonoOn_add_inv_Ici_one.monotoneOn hv.1 hρ hv.2
  · intro hdist
    have hrad : ‖w‖ ≤ ρ := by
      by_contra h
      have hlt := strictMonoOn_add_inv_Ici_one hρ hw (lt_of_not_ge h)
      linarith
    exact ⟨w, ⟨hw, hrad⟩, rfl⟩

/-- The complex Chebyshev polynomial has the exact Laurent form after Joukowski substitution.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
Helper for `bernstein-ellipse-def` and `bernstein-walsh-ellipse`. -/
theorem eval_T_complex_joukowski {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (T ℂ (n : ℤ)).eval (joukowski w) = (w ^ n + (w⁻¹) ^ n) / 2 := by
  have hJ : joukowski w = Complex.cosh (Complex.log w) := by
    simp [joukowski, Complex.cosh, Complex.exp_neg, Complex.exp_log hw]
  rw [hJ, T_complex_cosh]
  simp [Complex.cosh, Int.cast_natCast, Complex.exp_neg, Complex.exp_nat_mul,
    Complex.exp_log hw, inv_pow]

/-- Every point in the filled Bernstein ellipse has modulus at most its major semiaxis.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem norm_le_of_mem_filledBernsteinEllipse {ρ : ℝ} (hρ : 1 ≤ ρ) {z : ℂ}
    (hz : z ∈ filledBernsteinEllipse ρ) : ‖z‖ ≤ (ρ + ρ⁻¹) / 2 := by
  obtain ⟨w, hw, rfl⟩ := hz
  calc ‖joukowski w‖ = ‖w + w⁻¹‖ / 2 := by simp [joukowski]
    _ ≤ (‖w‖ + ‖w⁻¹‖) / 2 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (‖w‖ + ‖w‖⁻¹) / 2 := by rw [norm_inv]
    _ ≤ (ρ + ρ⁻¹) / 2 := div_le_div_of_nonneg_right
      (strictMonoOn_add_inv_Ici_one.monotoneOn hw.1 hρ hw.2) (by norm_num)

/-- The real part in a filled Bernstein ellipse is bounded below by minus the major semiaxis.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem neg_semiaxis_le_re_of_mem_filledBernsteinEllipse {ρ : ℝ} (hρ : 1 ≤ ρ) {z : ℂ}
    (hz : z ∈ filledBernsteinEllipse ρ) : -(ρ + ρ⁻¹) / 2 ≤ z.re := by
  have hn := norm_le_of_mem_filledBernsteinEllipse hρ hz
  have hre := (abs_le.mp (Complex.abs_re_le_norm z)).1
  linarith

/-- Complex Chebyshev polynomials have their sharp radius bound on the filled ellipse.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem norm_eval_T_complex_le_of_mem_filledBernsteinEllipse {ρ : ℝ}
    (hρ : 1 ≤ ρ) {z : ℂ} (hz : z ∈ filledBernsteinEllipse ρ) (n : ℕ) :
    ‖(T ℂ (n : ℤ)).eval z‖ ≤ (ρ ^ n + (ρ⁻¹) ^ n) / 2 := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith [hw.1])
  rw [eval_T_complex_joukowski hw0, norm_div]
  norm_num
  have hadd : ‖w ^ n + w⁻¹ ^ n‖ ≤ ‖w‖ ^ n + (‖w‖⁻¹) ^ n := by
    simpa only [norm_pow, norm_inv] using norm_add_le (w ^ n) (w⁻¹ ^ n)
  have hrad : ‖w‖ ^ n + (‖w‖⁻¹) ^ n ≤ ρ ^ n + (ρ⁻¹) ^ n := by
    simp only [inv_pow]
    exact strictMonoOn_add_inv_Ici_one.monotoneOn
      (one_le_pow₀ hw.1) (one_le_pow₀ hρ) (pow_le_pow_left₀ (by positivity) hw.2 n)
  simpa only [inv_pow] using div_le_div_of_nonneg_right (hadd.trans hrad)
    (by norm_num : (0 : ℝ) ≤ 2)

/-- The filled ellipse is the topological closure of the open ellipse.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem closure_openBernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ) :
    closure (openBernsteinEllipse ρ) = filledBernsteinEllipse ρ := by
  have hclosed : IsClosed (filledBernsteinEllipse ρ) := by
    have heq : filledBernsteinEllipse ρ = {z : ℂ | ‖z - 1‖ + ‖z + 1‖ ≤ ρ + ρ⁻¹} := by
      ext z
      exact mem_filledBernsteinEllipse_iff hρ.le z
    rw [heq]
    exact isClosed_le (by fun_prop) continuous_const
  apply Subset.antisymm
  · apply closure_minimal _ hclosed
    intro z hz
    exact (mem_filledBernsteinEllipse_iff hρ.le z).mpr
      ((mem_openBernsteinEllipse_iff hρ z).mp hz).le
  · intro z hz
    have hdist := (mem_filledBernsteinEllipse_iff hρ.le z).mp hz
    have hc : 2 < ρ + ρ⁻¹ := by
      have hh := strictMonoOn_add_inv_Ici_one (𝕜 := ℝ) (by simp : (1 : ℝ) ∈ Ici 1)
        hρ.le hρ
      norm_num at hh
      exact hh
    have hscale : ∀ t ∈ Ico (0 : ℝ) 1, (t : ℂ) * z ∈ openBernsteinEllipse ρ := by
      intro t ht
      have hsub : ‖(t : ℂ) * z - 1‖ ≤ t * ‖z - 1‖ + (1 - t) := by
        calc ‖(t : ℂ) * z - 1‖ =
            ‖(t : ℂ) * (z - 1) + ((1 - t : ℝ) : ℂ) * (-1)‖ := by
              congr 1
              push_cast
              ring
          _ ≤ ‖(t : ℂ) * (z - 1)‖ + ‖((1 - t : ℝ) : ℂ) * (-1)‖ := norm_add_le _ _
          _ = t * ‖z - 1‖ + (1 - t) := by
            rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one, Complex.norm_real,
              Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg ht.1, abs_of_nonneg (sub_pos.mpr ht.2).le]
      have hadd : ‖(t : ℂ) * z + 1‖ ≤ t * ‖z + 1‖ + (1 - t) := by
        calc ‖(t : ℂ) * z + 1‖ =
            ‖(t : ℂ) * (z + 1) + ((1 - t : ℝ) : ℂ)‖ := by
              congr 1
              push_cast
              ring
          _ ≤ ‖(t : ℂ) * (z + 1)‖ + ‖((1 - t : ℝ) : ℂ)‖ := norm_add_le _ _
          _ = t * ‖z + 1‖ + (1 - t) := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg ht.1, abs_of_nonneg (sub_pos.mpr ht.2).le]
      rw [mem_openBernsteinEllipse_iff hρ]
      nlinarith [mul_le_mul_of_nonneg_left hdist ht.1,
        mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hc)]
    have hcontinuous : Continuous (fun t : ℝ => (t : ℂ) * z) := by fun_prop
    have h1 : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by
      rw [closure_Ico zero_ne_one]
      exact ⟨zero_le_one, le_rfl⟩
    have hzin : z ∈ closure ((fun t : ℝ => (t : ℂ) * z) '' Ico (0 : ℝ) 1) := by
      apply image_closure_subset_closure_image hcontinuous
      exact ⟨1, h1, by simp⟩
    exact closure_mono (by rintro w ⟨t, ht, rfl⟩; exact hscale t ht) hzin

/-- The affine image of a filled ellipse has the explicit right-half-plane enclosure.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem re_affine_ge_of_mem_filledBernsteinEllipse {a b ρ : ℝ} (hab : a ≤ b)
    (hρ : 1 ≤ ρ) {z : ℂ} (hz : z ∈ filledBernsteinEllipse ρ) :
    (b + a - (b - a) * ((ρ + ρ⁻¹) / 2)) / 2 ≤
      (((b - a : ℝ) : ℂ) * z + (b + a : ℝ)).re / 2 := by
  have hre := neg_semiaxis_le_re_of_mem_filledBernsteinEllipse hρ hz
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_left hre (sub_nonneg.mpr hab)]

/-- The affine image of a filled ellipse has the explicit modulus enclosure.
Source: Trefethen, ATAP, Ch. 8; operator derivations §4.
atlas: bernstein-ellipse-def -/
theorem norm_affine_le_of_mem_filledBernsteinEllipse {a b ρ : ℝ} (hab : a ≤ b)
    (hρ : 1 ≤ ρ) {z : ℂ} (hz : z ∈ filledBernsteinEllipse ρ) :
    ‖(((b - a : ℝ) : ℂ) * z + (b + a : ℝ)) / 2‖ ≤
      (|b + a| + (b - a) * ((ρ + ρ⁻¹) / 2)) / 2 := by
  have hn := norm_le_of_mem_filledBernsteinEllipse hρ hz
  rw [norm_div]
  rw [norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc ‖((b - a : ℝ) : ℂ) * z + (b + a : ℝ)‖ ≤
      ‖((b - a : ℝ) : ℂ) * z‖ + ‖((b + a : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = (b - a) * ‖z‖ + |b + a| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    _ ≤ |b + a| + (b - a) * ((ρ + ρ⁻¹) / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hab)]

end NLAlib
