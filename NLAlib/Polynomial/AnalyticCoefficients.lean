import NLAlib.Polynomial.BernsteinEllipse

/-!
# Chebyshev coefficient decay from a holomorphic Bernstein ellipse

Cauchy–Goursat moves the Joukowski coefficient contour from the unit circle to the outer
ellipse parameter circle. The circle-integral norm estimate gives the sharp geometric
coefficient bound. Every analyticity assumption refers to the original function on the
filled Bernstein ellipse; coefficient decay is derived rather than assumed.
-/

noncomputable section

open Complex Set Metric Filter
open scoped Topology

namespace NLAlib

/-- Complex Chebyshev coefficients in their Joukowski contour form. The zeroth coefficient
has normalization `1/(2πi)`; positive coefficients have normalization `1/(πi)`.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1 (`chebyshev-coeff-analytic-decay`). -/
def chebyshevComplexCoeff (F : ℂ → ℂ) (k : ℕ) : ℂ :=
  (if k = 0 then (1 : ℂ) else 2) * ((2 * Real.pi * I : ℂ)⁻¹ *
    (∮ w in C(0, 1), F (joukowski w) / w ^ (k + 1)))

/-- The real Chebyshev coefficients are the real parts of the standard contour coefficients.
For a function real on `[-1,1]` these are the usual real Chebyshev expansion coefficients.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1 (`chebyshev-coeff-analytic-decay`). -/
def chebyshevAnalyticCoeff (F : ℂ → ℂ) (k : ℕ) : ℝ := (chebyshevComplexCoeff F k).re

/-- A genuine open-ellipse bound is necessarily nonnegative, since the ellipse contains zero.
Source: Trefethen, ATAP, Chapter 8; helper for analytic coefficient and SLQ rates. -/
theorem nonneg_of_norm_le_on_open_bernsteinEllipse {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) : 0 ≤ M := by
  have hz : (0 : ℂ) ∈ openBernsteinEllipse ρ :=
    filledBernsteinEllipse_subset_openBernsteinEllipse (r := 1) hρ hρ
      (ofReal_mem_filledBernsteinEllipse (ρ := 1) le_rfl (by norm_num : (0 : ℝ) ∈ Icc (-1) 1))
  exact (norm_nonneg _).trans (hM 0 hz)

/-- Cauchy–Goursat moves a Chebyshev coefficient contour to the Bernstein parameter radius.
Source: Trefethen, ATAP, Chapter 8, proof of Theorem 8.1.
Atlas `chebyshev-coeff-analytic-decay` (helper). -/
theorem circleIntegral_chebyshevCoeff_eq_radius {F : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hFc : ContinuousOn F (filledBernsteinEllipse ρ))
    (hFd : DifferentiableOn ℂ F (interior (filledBernsteinEllipse ρ))) (k : ℕ) :
    (∮ w in C(0, 1), F (joukowski w) / w ^ (k + 1)) =
      ∮ w in C(0, ρ), F (joukowski w) / w ^ (k + 1) := by
  have hnonzero : ∀ w ∈ closedBall (0 : ℂ) ρ \ ball 0 1, w ≠ 0 := by
    intro w hw hzero
    have h := hw.2
    norm_num [hzero] at h
  have hc : ContinuousOn (fun w : ℂ => F (joukowski w) / w ^ (k + 1))
      (closedBall (0 : ℂ) ρ \ ball 0 1) :=
    (continuousOn_comp_joukowski_closed_annulus hFc).div
      (continuousOn_id.pow _) (fun w hw => pow_ne_zero _ (hnonzero w hw))
  have hd : ∀ w ∈ (ball (0 : ℂ) ρ \ closedBall 0 1) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => F (joukowski w) / w ^ (k + 1)) w := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro hzero
      have h := hw.1.2
      norm_num [hzero] at h
    exact (differentiableAt_comp_joukowski_open_annulus hFd hw.1).div
      (differentiableAt_id.pow _) (pow_ne_zero _ hw0)
  exact (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (by norm_num : (0 : ℝ) < 1) hρ.le countable_empty hc hd).symm

/-- The normalized nonnegative Laurent coefficient is at most `M/ρ^k` on a holomorphic
Bernstein ellipse of parameter `ρ>1`.
Source: Trefethen, ATAP, Chapter 8, proof of Theorem 8.1.
Atlas `chebyshev-coeff-analytic-decay` (helper). -/
theorem norm_normalized_circleIntegral_chebyshevCoeff_le {F : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hFc : ContinuousOn F (filledBernsteinEllipse ρ))
    (hFd : DifferentiableOn ℂ F (interior (filledBernsteinEllipse ρ)))
    (hM : ∀ z ∈ filledBernsteinEllipse ρ, ‖F z‖ ≤ M) (k : ℕ) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
      (∮ w in C(0, 1), F (joukowski w) / w ^ (k + 1))‖ ≤ M / ρ ^ k := by
  rw [circleIntegral_chebyshevCoeff_eq_radius hρ hFc hFd]
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hbound : ∀ w ∈ sphere (0 : ℂ) ρ,
      ‖F (joukowski w) / w ^ (k + 1)‖ ≤ M / ρ ^ (k + 1) := by
    intro w hw
    have hnorm : ‖w‖ = ρ := by simpa [mem_sphere_iff_norm] using hw
    rw [norm_div, norm_pow, hnorm]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hρ0.le _)
    exact hM _ (joukowski_mem_filledBernsteinEllipse (by rw [hnorm]; exact ⟨hρ.le, le_rfl⟩))
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ0.le hbound
  change ‖(2 * Real.pi * I : ℂ)⁻¹ * _‖ ≤ _ at h
  refine h.trans_eq ?_
  rw [pow_succ]
  field_simp

/-- Positive Chebyshev coefficients of a function holomorphic in the filled Bernstein
ellipse interior and continuous on its closure decay as `2M/ρ^k`.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1; operator rederivations
`rt:analytic-approx`. The contour coefficients are explicitly defined and no decay bound
or polynomial-approximation property is assumed.
atlas: chebyshev-coeff-analytic-decay (partial) -/
theorem norm_chebyshevComplexCoeff_le {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFc : ContinuousOn F (filledBernsteinEllipse ρ))
    (hFd : DifferentiableOn ℂ F (interior (filledBernsteinEllipse ρ)))
    (hM : ∀ z ∈ filledBernsteinEllipse ρ, ‖F z‖ ≤ M) {k : ℕ} (hk : 0 < k) :
    ‖chebyshevComplexCoeff F k‖ ≤ 2 * M / ρ ^ k := by
  rw [chebyshevComplexCoeff, if_neg (Nat.ne_of_gt hk), norm_mul]
  norm_num only [norm_ofNat]
  have h := norm_normalized_circleIntegral_chebyshevCoeff_le hρ hFc hFd hM k
  have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← mul_div_assoc] at hh
  exact hh

/-- The zeroth Chebyshev coefficient has norm at most the function bound `M`.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1.
Atlas `chebyshev-coeff-analytic-decay` (zeroth-coefficient endpoint). -/
theorem norm_chebyshevComplexCoeff_zero_le {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFc : ContinuousOn F (filledBernsteinEllipse ρ))
    (hFd : DifferentiableOn ℂ F (interior (filledBernsteinEllipse ρ)))
    (hM : ∀ z ∈ filledBernsteinEllipse ρ, ‖F z‖ ≤ M) :
    ‖chebyshevComplexCoeff F 0‖ ≤ M := by
  simpa [chebyshevComplexCoeff] using
    norm_normalized_circleIntegral_chebyshevCoeff_le hρ hFc hFd hM 0

/-- Real Chebyshev coefficients obey the exact Bernstein ellipse decay constant.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1; operator rederivations
`rt:analytic-approx`. This real-part version also applies to complex-valued extensions.
atlas: chebyshev-coeff-analytic-decay (partial) -/
theorem abs_chebyshevAnalyticCoeff_le {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFc : ContinuousOn F (filledBernsteinEllipse ρ))
    (hFd : DifferentiableOn ℂ F (interior (filledBernsteinEllipse ρ)))
    (hM : ∀ z ∈ filledBernsteinEllipse ρ, ‖F z‖ ≤ M) {k : ℕ} (hk : 0 < k) :
    |chebyshevAnalyticCoeff F k| ≤ 2 * M / ρ ^ k :=
  (Complex.abs_re_le_norm _).trans (norm_chebyshevComplexCoeff_le hρ hFc hFd hM hk)

/-- Under the original holomorphy and boundedness assumptions on the open Bernstein ellipse,
positive coefficients obey the exact bound `2M/ρ^k`. No continuous extension to the outer
boundary is assumed: apply the closed-radius estimate at every `1<r<ρ` and take `r↑ρ`.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1.
atlas: chebyshev-coeff-analytic-decay (partial) -/
theorem norm_chebyshevComplexCoeff_le_of_open_ellipse {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) {k : ℕ} (hk : 0 < k) :
    ‖chebyshevComplexCoeff F k‖ ≤ 2 * M / ρ ^ k := by
  have hb : ∀ r ∈ Ioo (1 : ℝ) ρ, ‖chebyshevComplexCoeff F k‖ ≤ 2 * M / r ^ k := by
    intro r hr
    have hsub := filledBernsteinEllipse_subset_openBernsteinEllipse hρ hr.2
    exact norm_chebyshevComplexCoeff_le hr.1 (hFd.continuousOn.mono hsub)
      (hFd.mono (interior_subset.trans hsub)) (fun z hz => hM z (hsub hz)) hk
  have hc : ContinuousAt (fun r : ℝ => 2 * M / r ^ k) ρ := by
    apply ContinuousAt.div continuousAt_const (continuousAt_id.pow _)
    exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hρ))
  have : NeBot (𝓝[Ioo (1 : ℝ) ρ] ρ) := right_nhdsWithin_Ioo_neBot hρ
  exact ge_of_tendsto (hc.continuousWithinAt.tendsto)
    (Filter.mem_of_superset self_mem_nhdsWithin (fun r hr => hb r hr))

/-- The original open-ellipse assumption gives the exact real Chebyshev coefficient bound,
without continuity on the ellipse boundary.
Source: Trefethen, ATAP, Chapter 8, Theorem 8.1.
atlas: chebyshev-coeff-analytic-decay (partial) -/
theorem abs_chebyshevAnalyticCoeff_le_of_open_ellipse {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) {k : ℕ} (hk : 0 < k) :
    |chebyshevAnalyticCoeff F k| ≤ 2 * M / ρ ^ k :=
  (Complex.abs_re_le_norm _).trans (norm_chebyshevComplexCoeff_le_of_open_ellipse hρ hFd hM hk)

end NLAlib
