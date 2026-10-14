import NLAlib.Polynomial.Quadrature.RationalMeasure
import NLAlib.Polynomial.Quadrature.GaussMeasure
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiLocation
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationMeasure

/-! # Actual positive rational Gauss rules

The compact-support, positive-denominator hypotheses construct the divided
measure's polynomial moments. Its actual canonical Gauss nodes and weights
then give the rational rule and the converse uniqueness statement.
Source: Gautschi (2004), rational Gauss rules; operator derivations AQ36.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Finset
namespace NLAlib

/-- Strictly positive denominator density preserves the topological support. -/
theorem support_dividedPolynomialMeasure_eq {μ : Measure ℝ} {ω : ℝ[X]}
    (hω : ∀ᵐ x ∂μ, 0 < ω.eval x) : (dividedPolynomialMeasure μ ω).support = μ.support := by
  apply Set.Subset.antisymm
  · exact (withDensity_absolutelyContinuous μ _).support_mono
  · apply (withDensity_absolutelyContinuous' (by fun_prop) ?_).support_mono
    filter_upwards [hω] with x hx
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hx)).ne'

/-- A positive denominator on the compact support enclosure gives all actual
polynomial moments of the reciprocal-density measure. -/
theorem hasPolynomialMoments_dividedPolynomialMeasure_of_ae_mem_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {ω : ℝ[X]}
    (hω : ∀ x ∈ Icc a b, 0 < ω.eval x) :
    HasPolynomialMoments (dividedPolynomialMeasure μ ω) := by
  have hdiv := hasDividedPolynomialMoments_of_ae_mem_Icc hs (fun x hx => (hω x hx).ne')
  intro p
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)).mpr
  apply (hdiv p).congr
  filter_upwards [hs] with x hx
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (hω x hx).le), smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

/-- The actual Gauss rule of the positive divided measure supplies a rational
rule for the original measure, with real nodes in its support enclosure and
strictly positive multiplied weights. No polynomial-exact rule is assumed.
Source: Gautschi (2004), rational Gauss construction AQ36.
atlas: rational-gauss-quadrature (partial) -/
theorem rational_gauss_rule_of_positive_denominator
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {ω : ℝ[X]}
    (hω : ∀ x ∈ Icc a b, 0 < ω.eval x) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) :
    let ν := dividedPolynomialMeasure μ ω
    let hν := hasPolynomialMoments_dividedPolynomialMeasure_of_ae_mem_Icc hs hω
    (∀ i : Fin n, gaussNodes ν hν n i ∈ Icc a b ∧
      0 < gaussWeights ν hν n i * ω.eval (gaussNodes ν hν n i)) ∧
    (∀ p : ℝ[X], p.degree < (2*n : ℕ) → (∫ x, p.eval x/ω.eval x ∂μ) =
      ∑ i : Fin n, (gaussWeights ν hν n i * ω.eval (gaussNodes ν hν n i)) *
        (p.eval (gaussNodes ν hν n i)/ω.eval (gaussNodes ν hν n i))) := by
  dsimp only
  let ν := dividedPolynomialMeasure μ ω
  let hν := hasPolynomialMoments_dividedPolynomialMeasure_of_ae_mem_Icc hs hω
  have hωae : ∀ᵐ x ∂μ, 0 < ω.eval x := by filter_upwards [hs] with x hx; exact hω x hx
  have hsν : ∀ᵐ x ∂ν, x ∈ Icc a b := (withDensity_absolutelyContinuous μ _).ae_le hs
  have hnν : (n : ℕ∞) ≤ ν.support.encard := by rw [support_dividedPolynomialMeasure_eq hωae]; exact hn
  have hnodes (i : Fin n) : gaussNodes ν hν n i ∈ Icc a b := gaussNodes_mem_Icc hν hsν hnν i
  refine ⟨fun i => ⟨hnodes i, mul_pos (gaussWeights_pos hν hnν i) (hω _ (hnodes i))⟩, ?_⟩
  intro p hp
  rw [← integral_dividedPolynomialMeasure μ ω hωae, integral_eval_eq_sum_gaussWeights_mul_eval hν hn0 hnν hp]
  apply sum_congr rfl
  intro i _
  change gaussWeights ν hν n i * p.eval (gaussNodes ν hν n i) =
    (gaussWeights ν hν n i * ω.eval (gaussNodes ν hν n i)) *
      (p.eval (gaussNodes ν hν n i)/ω.eval (gaussNodes ν hν n i))
  field_simp [(hω _ (hnodes i)).ne']

/-- Any distinct-node rational rule of the full numerator degree range is the
actual Gauss rule of the reciprocal-density measure after dividing its weights.
Source: Gautschi (2004), rational Gauss converse AQ36.
atlas: rational-gauss-quadrature (partial) -/
theorem rational_rule_eq_divided_measure_gauss_of_exactness
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {ω : ℝ[X]}
    (hω : ∀ x ∈ Icc a b, 0 < ω.eval x) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) (v w : Fin n → ℝ)
    (hv : Function.Injective v)
    (hexact : ∀ p : ℝ[X], p.degree < (2*n : ℕ) → (∫ x, p.eval x/ω.eval x ∂μ) =
      ∑ i, w i * (p.eval (v i)/ω.eval (v i))) :
    let ν := dividedPolynomialMeasure μ ω
    let hν := hasPolynomialMoments_dividedPolynomialMeasure_of_ae_mem_Icc hs hω
    ∃ e : Equiv.Perm (Fin n), (∀ i, v (e i) = gaussNodes ν hν n i) ∧
      (∀ i, w (e i)/ω.eval (v (e i)) = gaussWeights ν hν n i) := by
  dsimp only
  let hν := hasPolynomialMoments_dividedPolynomialMeasure_of_ae_mem_Icc hs hω
  have hωae : ∀ᵐ x ∂μ, 0 < ω.eval x := by filter_upwards [hs] with x hx; exact hω x hx
  apply rule_eq_gaussNodes_gaussWeights_of_moments hν hn0
    (by rw [support_dividedPolynomialMeasure_eq hωae]; exact hn) v (fun i => w i/ω.eval (v i)) hv
  intro k hk
  rw [integral_dividedPolynomialMeasure μ ω hωae]
  have h := hexact (X^k) (by rw [degree_X_pow]; exact_mod_cast hk)
  simp only [eval_pow, eval_X] at h
  rw [h]
  apply sum_congr rfl
  intro i _
  ring

end NLAlib
