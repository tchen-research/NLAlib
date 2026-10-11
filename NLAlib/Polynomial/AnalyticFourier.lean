import NLAlib.Polynomial.AnalyticCoefficients
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Measure.Haar.Unique
import NLAlib.Polynomial.Basic

/-!
# Fourier reconstruction of analytic Chebyshev series

This module identifies the Joukowski contour coefficients with the Fourier coefficients of
the continuous circle pullback. It connects the proved analytic decay to Mathlib's genuine
uniform Fourier reconstruction theorem, rather than assuming a Chebyshev expansion.
-/

noncomputable section

open Complex Set Metric Filter Polynomial Polynomial.Chebyshev
open scoped Topology ComplexConjugate Real

namespace NLAlib

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Pull back a complex function on the Bernstein ellipse to the additive circle.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
def chebyshevCircleFunction (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) : ℂ :=
  F (joukowski (fourier 1 θ))

/-- The pullback of a function continuous on the filled Bernstein ellipse is continuous.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem continuous_chebyshevCircleFunction {F : ℂ → ℂ} {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hFc : ContinuousOn F (filledBernsteinEllipse ρ)) : Continuous (chebyshevCircleFunction F) := by
  have hnorm : ∀ θ : AddCircle (2 * Real.pi), ‖fourier 1 θ‖ = 1 :=
    fun θ => Circle.norm_coe _
  have hne : ∀ θ : AddCircle (2 * Real.pi), fourier 1 θ ≠ 0 := by
    intro θ
    exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  have hJ : Continuous (fun θ : AddCircle (2 * Real.pi) => joukowski (fourier 1 θ)) := by
    unfold joukowski
    exact ((fourier 1).continuous.add ((fourier 1).continuous.inv₀ hne)).div_const 2
  exact hFc.comp_continuous hJ (fun θ =>
    joukowski_mem_filledBernsteinEllipse (by rw [hnorm]; exact ⟨le_rfl, hρ⟩))

/-- Fourier monomials of period `2π` equal the unit-circle parametrization at frequency one.
Source: Mathlib additive-circle Fourier definition; helper for `chebyshev-approx-analytic`. -/
theorem fourier_one_eq_circleMap (θ : ℝ) :
    fourier 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_apply]
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
  congr 1
  push_cast
  field_simp

/-- The circle pullback evaluated at a real angle is exactly `F(cos θ)`.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem chebyshevCircleFunction_coe_eq_cos (F : ℂ → ℂ) (θ : ℝ) :
    chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi)) = F (Real.cos θ) := by
  rw [chebyshevCircleFunction, fourier_one_eq_circleMap]
  have hn : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by simp
  rw [joukowski_eq_re_of_norm_eq_one hn]
  congr 1
  simp [circleMap, Complex.exp_mul_I]

/-- Natural Fourier frequencies are powers of the first unit-circle monomial.
Source: Mathlib additive-circle Fourier multiplication; helper for `chebyshev-approx-analytic`. -/
theorem fourier_nat_eq_pow (k : ℕ) (θ : AddCircle (2 * Real.pi)) :
    fourier (k : ℤ) θ = fourier 1 θ ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

/-- The nonnegative Fourier coefficient of the circle pullback equals its normalized
Joukowski contour coefficient, with the zeroth Chebyshev normalization not yet doubled.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem fourierCoeff_chebyshevCircleFunction_eq_circleIntegral (F : ℂ → ℂ) (k : ℕ) :
    fourierCoeff (chebyshevCircleFunction F) (k : ℤ) =
      (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ w in C(0, 1), F (joukowski w) / w ^ (k + 1)) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, circleIntegral]
  have heq : ∀ θ : ℝ,
      deriv (circleMap (0 : ℂ) 1) θ •
        (F (joukowski (circleMap 0 1 θ)) / circleMap 0 1 θ ^ (k + 1)) =
        I * (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) •
          chebyshevCircleFunction F θ) := by
    intro θ
    rw [deriv_circleMap, ← fourier_one_eq_circleMap, fourier_neg,
      fourier_nat_eq_pow]
    have hn : ‖fourier 1 (θ : AddCircle (2 * Real.pi))‖ = 1 := Circle.norm_coe _
    have hz : fourier 1 (θ : AddCircle (2 * Real.pi)) ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    rw [map_pow, ← Complex.inv_eq_conj hn, inv_pow, pow_succ]
    simp only [smul_eq_mul, chebyshevCircleFunction]
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp

/-- The contour definition agrees exactly with the standard Fourier definition of the
Chebyshev coefficients, including the distinct zeroth normalization.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-coeff-analytic-decay`, helper). -/
theorem chebyshevComplexCoeff_eq_fourierCoeff (F : ℂ → ℂ) (k : ℕ) :
    chebyshevComplexCoeff F k = (if k = 0 then (1 : ℂ) else 2) *
      fourierCoeff (chebyshevCircleFunction F) (k : ℤ) := by
  rw [chebyshevComplexCoeff, fourierCoeff_chebyshevCircleFunction_eq_circleIntegral]

/-- The standard positive Chebyshev coefficient `2 Re FourierCoeff(F(cos ·),k)` has the
sharp decay constant under the original bounded holomorphic open-ellipse hypothesis.
The circle/contour bridge and the radius-limit theorem discharge both identification and
boundary issues.
Source: Trefethen, ATAP, Theorem 8.1.
atlas: chebyshev-coeff-analytic-decay -/
theorem abs_two_mul_re_fourierCoeff_chebyshevCircleFunction_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) {k : ℕ} (hk : 0 < k) :
    |2 * (fourierCoeff (chebyshevCircleFunction F) (k : ℤ)).re| ≤ 2 * M / ρ ^ k := by
  have h := abs_chebyshevAnalyticCoeff_le_of_open_ellipse hρ hFd hM hk
  simpa [chebyshevAnalyticCoeff, chebyshevComplexCoeff_eq_fourierCoeff,
    Nat.ne_of_gt hk, Complex.mul_re] using h

/-- The circle pullback is even, by the inversion symmetry of the Joukowski transform.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem chebyshevCircleFunction_neg (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    chebyshevCircleFunction F (-θ) = chebyshevCircleFunction F θ := by
  simp only [chebyshevCircleFunction, fourier_one, AddCircle.toCircle_neg, Circle.coe_inv,
    joukowski_inv]

/-- Reflecting a Fourier monomial in the circle reverses its frequency.
Source: Mathlib additive-circle Fourier definition; helper for `chebyshev-approx-analytic`. -/
theorem fourier_apply_neg (k : ℤ) (θ : AddCircle (2 * Real.pi)) :
    fourier k (-θ) = fourier (-k) θ := by
  simp only [fourier_apply, smul_neg, neg_smul]

/-- The Fourier coefficients of the even Joukowski pullback are even.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem fourierCoeff_chebyshevCircleFunction_neg (F : ℂ → ℂ) (k : ℤ) :
    fourierCoeff (chebyshevCircleFunction F) (-k) =
      fourierCoeff (chebyshevCircleFunction F) k := by
  rw [fourierCoeff, fourierCoeff]
  have h := MeasureTheory.integral_neg_eq_self
    (fun θ : AddCircle (2 * Real.pi) => fourier (-k) θ • chebyshevCircleFunction F θ)
    AddCircle.haarAddCircle
  simp only [fourier_apply_neg, neg_neg, chebyshevCircleFunction_neg] at h ⊢
  exact h

/-- The nonnegative Fourier coefficients decay as `M/ρ^k`, including the zeroth coefficient.
Source: Trefethen, ATAP, Theorem 8.1 (`chebyshev-approx-analytic`, helper). -/
theorem norm_fourierCoeff_chebyshevCircleFunction_nat_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) (k : ℕ) :
    ‖fourierCoeff (chebyshevCircleFunction F) (k : ℤ)‖ ≤ M / ρ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · let r := (1 + ρ) / 2
    have hr : 1 < r ∧ r < ρ := by dsimp [r]; constructor <;> linarith
    have hsub := filledBernsteinEllipse_subset_openBernsteinEllipse hρ hr.2
    have h := norm_chebyshevComplexCoeff_zero_le hr.1 (hFd.continuousOn.mono hsub)
      (hFd.mono (interior_subset.trans hsub)) (fun z hz => hM z (hsub hz))
    simpa [chebyshevComplexCoeff_eq_fourierCoeff] using h
  · have h := norm_chebyshevComplexCoeff_le_of_open_ellipse hρ hFd hM hk
    rw [chebyshevComplexCoeff_eq_fourierCoeff, if_neg (Nat.ne_of_gt hk), norm_mul] at h
    norm_num only [norm_ofNat] at h
    rw [mul_div_assoc] at h
    linarith

/-- The actual zeroth Chebyshev coefficient has the sharp norm bound on the original
open Bernstein ellipse, without any outer-boundary continuity premise.
Source: Trefethen, ATAP, Theorem 8.1; operator rederivations `rt:analytic-approx`.
atlas: chebyshev-coeff-analytic-decay (partial) -/
theorem norm_chebyshevComplexCoeff_zero_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) :
    ‖chebyshevComplexCoeff F 0‖ ≤ M := by
  simpa [chebyshevComplexCoeff_eq_fourierCoeff] using
    norm_fourierCoeff_chebyshevCircleFunction_nat_le_of_open_ellipse hρ hFd hM 0

/-- The real zeroth Chebyshev coefficient has absolute value at most the actual
open-ellipse function bound.
Source: Trefethen, ATAP, Theorem 8.1; operator rederivations `rt:analytic-approx`.
atlas: chebyshev-coeff-analytic-decay (partial) -/
theorem abs_chebyshevAnalyticCoeff_zero_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) :
    |chebyshevAnalyticCoeff F 0| ≤ M :=
  (Complex.abs_re_le_norm _).trans
    (norm_chebyshevComplexCoeff_zero_le_of_open_ellipse hρ hFd hM)

/-- Genuine analytic decay makes the full two-sided Fourier coefficient sequence summable.
Source: Trefethen, ATAP, Theorems 8.1 and 3.1(a); helper for `chebyshev-approx-analytic`. -/
theorem summable_fourierCoeff_chebyshevCircleFunction_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) :
    Summable (fourierCoeff (chebyshevCircleFunction F)) := by
  have hgeom : Summable (fun k : ℕ => (ρ⁻¹) ^ k) :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_of_pos (by positivity : 0 < ρ⁻¹)]
      exact (inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ)
  have hs_norm : Summable (fun k : ℕ =>
      ‖fourierCoeff (chebyshevCircleFunction F) (k : ℤ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hgeom.mul_left M)
    intro k
    simpa only [div_eq_mul_inv, inv_pow] using
      norm_fourierCoeff_chebyshevCircleFunction_nat_le_of_open_ellipse hρ hFd hM k
  have hs_nat := hs_norm.of_norm
  have hs_neg : Summable (fun k : ℕ =>
      fourierCoeff (chebyshevCircleFunction F) (-((k : ℤ) + 1))) := by
    simp_rw [fourierCoeff_chebyshevCircleFunction_neg]
    exact_mod_cast (summable_nat_add_iff 1).mpr hs_nat
  exact Summable.of_nat_of_neg_add_one hs_nat hs_neg

/-- The Fourier series of the circle pullback reconstructs the original function pointwise,
under the genuine open-ellipse analytic assumptions.
Source: Trefethen, ATAP, Theorems 8.1 and 3.1(a); Mathlib's uniform Fourier reconstruction.
Atlas `chebyshev-approx-analytic` (helper). -/
theorem hasSum_fourier_chebyshevCircleFunction_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) (θ : AddCircle (2 * Real.pi)) :
    HasSum (fun k : ℤ => fourierCoeff (chebyshevCircleFunction F) k • fourier k θ)
      (chebyshevCircleFunction F θ) := by
  have hsub := filledBernsteinEllipse_subset_openBernsteinEllipse (r := 1) hρ hρ
  let g : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨chebyshevCircleFunction F, continuous_chebyshevCircleFunction (ρ := 1) le_rfl
      (hFd.continuousOn.mono hsub)⟩
  exact has_pointwise_sum_fourier_series_of_summable
    (f := g) (summable_fourierCoeff_chebyshevCircleFunction_of_open_ellipse hρ hFd hM) θ

end NLAlib
