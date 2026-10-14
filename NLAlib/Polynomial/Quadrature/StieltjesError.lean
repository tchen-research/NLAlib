import NLAlib.Polynomial.OrthogonalPolynomials.StieltjesTransform
import NLAlib.ForMathlib.Algebra.PolynomialGeometricResolvent

/-! # Quantitative complex Gauss and Stieltjes error

Positive Gauss weights and polynomial exactness give a uniform-error transfer.
A finite geometric polynomial then yields the explicit Markov estimate at
infinity. Source: Gautschi (2004), Chapter 1; operator derivations AQ20.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Finset
namespace NLAlib

/-- Any uniform complex polynomial approximation bounds the actual canonical
Gauss error by twice the original mass times its error. -/
theorem norm_integral_sub_sum_gaussWeights_le_of_polynomial_approx
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) {p : ℂ[X]} (hp : p.degree < (2*n : ℕ))
    {ε : ℝ} (happrox : ∀ x ∈ Icc a b, ‖f x - p.eval (x : ℂ)‖ ≤ ε) :
    ‖(∫ x, f x ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      f (gaussNodes μ hμ n i)‖ ≤ 2 * μ.real univ * ε := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  have hint : Integrable f μ := by
    refine (hf.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [hs] with x hx hnot
    exact (hnot hx).elim
  have hexact := integral_complex_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn hp
  have heq : (∫ x, f x ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      f (gaussNodes μ hμ n i) =
      (∫ x, f x - p.eval (x : ℂ) ∂μ) -
        ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
          (f (gaussNodes μ hμ n i) - p.eval (gaussNodes μ hμ n i : ℂ)) := by
    rw [integral_sub hint (hμ.integrable_complex_eval p)]
    simp only [mul_sub, sum_sub_distrib]
    rw [hexact]
    ring
  have hb1 : ‖∫ x, f x - p.eval (x : ℂ) ∂μ‖ ≤ ε * μ.real univ :=
    norm_integral_le_of_norm_le_const (by filter_upwards [hs] with x hx; exact happrox x hx)
  have hb2 : ‖∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      (f (gaussNodes μ hμ n i) - p.eval (gaussNodes μ hμ n i : ℂ))‖ ≤ μ.real univ * ε := by
    calc
      _ ≤ ∑ i : Fin n, ‖(gaussWeights μ hμ n i : ℂ) *
          (f (gaussNodes μ hμ n i) - p.eval (gaussNodes μ hμ n i : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, gaussWeights μ hμ n i * ε := by
        apply sum_le_sum
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (gaussWeights_pos hμ hn i)]
        exact mul_le_mul_of_nonneg_left (happrox _ (gaussNodes_mem_Icc hμ hs hn i))
          (gaussWeights_pos hμ hn i).le
      _ = μ.real univ * ε := by rw [← sum_mul, sum_gaussWeights_eq_measure_univ hμ hn0 hn]; rfl
  rw [heq]
  exact (norm_sub_le _ _).trans (by nlinarith [hb1, hb2])

/-- Outside a radius enclosing the real interval, the native Stieltjes
transform differs from its actual second-kind ratio by the explicit finite
moment-matching bound. Source: Gautschi (2004), Markov theorem, AQ20.
atlas: jacobi-fraction-second-kind (partial) -/
theorem norm_stieltjesTransform_sub_secondKind_div_le_geometric
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {R : ℝ} (hR : 0 ≤ R)
    (hRI : ∀ x ∈ Icc a b, |x| ≤ R) {z : ℂ} (hz : R < ‖z‖) :
    ‖stieltjesTransform μ z -
      ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z‖ ≤
      2 * μ.real univ * R^(2*n) / (‖z‖^(2*n) * (‖z‖-R)) := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans_lt hz)
  have hzI : ∀ x ∈ Icc a b, z ≠ (x : ℂ) := by
    intro x hx heq
    have hnz : ‖z‖ = |x| := by rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact (not_lt_of_ge (hRI x hx)) (hnz ▸ hz)
  have happrox (x : ℝ) (hx : x ∈ Icc a b) :
      ‖(z-(x:ℂ))⁻¹ - (geometricResolventPolynomial z (2*n)).eval (x : ℂ)‖ ≤
        R^(2*n)/(‖z‖^(2*n)*(‖z‖-R)) := by
    rw [inv_sub_eval_geometricResolventPolynomial_eq hz0 (hzI x hx), norm_div, norm_mul, norm_pow,
      norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hden : ‖z‖-R ≤ ‖z-(x:ℂ)‖ := by
      have h := norm_sub_norm_le z (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      linarith [hRI x hx]
    calc
      _ ≤ R^(2*n)/(‖z‖^(2*n)*‖z-(x:ℂ)‖) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hRI x hx) _)
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
      _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hR _)
        (mul_pos (pow_pos (hR.trans_lt hz) _) (sub_pos.mpr hz))
        (mul_le_mul_of_nonneg_left hden (pow_nonneg (norm_nonneg _) _))
  rw [eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div hμ hs hn0 hn hzI]
  have he := norm_integral_sub_sum_gaussWeights_le_of_polynomial_approx hμ hs hn0 hn
    ((continuous_const.sub Complex.continuous_ofReal).continuousOn.inv₀
      (fun x hx => sub_ne_zero.mpr (hzI x hx)))
    (degree_geometricResolventPolynomial_lt z (2*n)) happrox
  simpa only [stieltjesTransform, div_eq_mul_inv, mul_div_assoc, mul_assoc,
    Pi.inv_apply, Pi.sub_apply] using he

end NLAlib
