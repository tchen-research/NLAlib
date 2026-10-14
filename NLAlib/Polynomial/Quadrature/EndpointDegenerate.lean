import NLAlib.Polynomial.Quadrature.GeneralMeasure
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Zero-order and degenerate endpoint rules

The two-endpoint linear rule needs no inverse moment matrix or strict Schur shift.
Its weights are nonnegative even when the measure is supported at just one endpoint,
and they vanish for the zero measure. A coincident-endpoint interval has the exact
one-node rule instead. These are the boundary cases of gauss-radau-lobatto.
-/

noncomputable section
open Polynomial MeasureTheory Set

namespace NLAlib

/-- The weights of the zero-order two-endpoint rule are the integrated affine
cardinals. At coincident endpoints this total definition gives zero weights; the
one-point rule is the appropriate exact rule in that case. -/
def endpointLinearWeights (μ : Measure ℝ) (a c : ℝ) : Fin 2 → ℝ :=
  ![∫ x, (c - x) / (c - a) ∂μ, ∫ x, (x - a) / (c - a) ∂μ]

/-- The two-endpoint linear weights are nonnegative on the supporting interval;
no moment nondegeneracy is needed, so either weight may vanish.
Source: focused mathematical reroutes, Section 3, zero-order Lobatto branch.
atlas: gauss-radau-lobatto (partial) -/
theorem endpointLinearWeights_nonneg {μ : Measure ℝ} {a c : ℝ} (hac : a < c)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a c) (i : Fin 2) : 0 ≤ endpointLinearWeights μ a c i := by
  fin_cases i
  · apply integral_nonneg_of_ae
    filter_upwards [hμ] with x hx
    exact div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hac.le)
  · apply integral_nonneg_of_ae
    filter_upwards [hμ] with x hx
    exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hac.le)

private theorem integrable_endpointCardinals {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a c : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a c) :
    Integrable (fun x => (c - x) / (c - a)) μ ∧
      Integrable (fun x => (x - a) / (c - a)) μ := by
  constructor
  · convert integrable_eval_of_ae_mem_Icc hμ (C ((c - a)⁻¹) * (C c - X)) using 1
    funext x
    simp only [eval_mul, eval_C, eval_sub, eval_X, div_eq_mul_inv]
    ring
  · convert integrable_eval_of_ae_mem_Icc hμ (C ((c - a)⁻¹) * (X - C a)) using 1
    funext x
    simp only [eval_mul, eval_C, eval_sub, eval_X, div_eq_mul_inv]
    ring

/-- The actual zero-order Lobatto rule integrates every affine polynomial, including
one-point measures and the zero measure. Source: focused mathematical reroutes,
Section 3, zero-order Lobatto branch.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_endpointLinearWeights_mul_eval {μ : Measure ℝ}
    [IsFiniteMeasure μ] {a c : ℝ} (hac : a < c)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a c) {p : ℝ[X]} (hp : p.degree ≤ 1) :
    (∫ x, p.eval x ∂μ) = endpointLinearWeights μ a c 0 * p.eval a +
      endpointLinearWeights μ a c 1 * p.eval c := by
  have he (x : ℝ) : p.eval x = (c - x) / (c - a) * p.eval a +
      (x - a) / (c - a) * p.eval c := by
    rw [eq_X_add_C_of_degree_le_one hp]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    field_simp [ne_of_gt (sub_pos.mpr hac)]
    ring
  obtain ⟨ha, hc⟩ := integrable_endpointCardinals hμ
  conv_lhs => rw [show p.eval = (fun x => (c - x) / (c - a) * p.eval a +
    (x - a) / (c - a) * p.eval c) from funext he]
  rw [integral_add (ha.mul_const _) (hc.mul_const _), integral_mul_const, integral_mul_const]
  rfl

/-- The zero-order two-endpoint weights sum to the original mass, including a
vanishing endpoint weight and the zero measure. Source: focused reroutes, Section 3.
atlas: gauss-radau-lobatto (partial) -/
theorem sum_endpointLinearWeights {μ : Measure ℝ} [IsFiniteMeasure μ] {a c : ℝ}
    (hac : a < c) (hμ : ∀ᵐ x ∂μ, x ∈ Icc a c) :
    (∑ i, endpointLinearWeights μ a c i) = ∫ _ : ℝ, (1 : ℝ) ∂μ := by
  have h := integral_eval_eq_endpointLinearWeights_mul_eval hac hμ
    (p := 1) (by simp : (1 : ℝ[X]).degree ≤ 1)
  simpa only [eval_one, mul_one, Fin.sum_univ_two] using h.symm

/-- Both explicit zero-order endpoint weights vanish for the zero measure.
Source: focused mathematical reroutes, Section 3, zero-measure branch.
atlas: gauss-radau-lobatto (partial) -/
theorem endpointLinearWeights_zero (a c : ℝ) : endpointLinearWeights 0 a c = 0 := by
  ext i
  fin_cases i <;> simp [endpointLinearWeights]

/-- A measure concentrated on a coincident-endpoint interval is integrated by its
one-point mass rule for every function; no two-distinct-endpoint rule is asserted.
Source: focused mathematical reroutes, Section 3, coincident-endpoint branch.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eq_mass_mul_of_ae_mem_singleton_interval {μ : Measure ℝ}
    [IsFiniteMeasure μ] {a : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a a) (f : ℝ → ℝ) :
    (∫ x, f x ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) * f a := by
  have he : f =ᵐ[μ] fun _ => f a := by
    filter_upwards [hμ] with x hx
    rw [le_antisymm hx.2 hx.1]
  rw [integral_congr_ae he]
  simp only [integral_const, smul_eq_mul, mul_one]

end NLAlib
