import NLAlib.Polynomial.Quadrature.HermiteRemainder
import NLAlib.Polynomial.Quadrature.GeneralMeasure
import NLAlib.ForMathlib.MeasureTheory.IntegralMeanValue

/-! # Integral derivative remainders for Gauss-degree rules

Polynomial exactness integrates the actual Hermite interpolant. The connected-image
mean-value argument turns the pointwise intermediate derivative values into one interior
value, without a measurable selection. Zero nodal norm gives exactness separately.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A rule exact below degree `2n` equals the integral of the actual finite Hermite
interpolant of the sampled values and first derivatives.
Source: Gautschi (2004), Theorem 1.48; operator derivations, (AQ3).
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem integral_hermiteInterpolate_eq_quadrature {μ : Measure ℝ} {n : ℕ} (hn : 0 < n)
    (v w : Fin n → ℝ) (hv : Function.Injective v)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i)) (f : ℝ → ℝ) :
    (∫ x, (Lagrange.hermiteInterpolate univ v (f ∘ v) (deriv f ∘ v)).eval x ∂μ) =
      ∑ i, w i * f (v i) := by
  have hdeg : (Lagrange.hermiteInterpolate univ v (f ∘ v) (deriv f ∘ v)).degree <
      (2 * n : ℕ) := by
    simpa only [card_univ, Fintype.card_fin] using
      Lagrange.degree_hermiteInterpolate_lt
        (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, mem_univ _⟩) hv.injOn _ _
  rw [hexact _ hdeg]
  exact sum_congr rfl fun i _ => by
    rw [Lagrange.eval_hermiteInterpolate_at_node hv.injOn _ _ (mem_univ i)]
    rfl

/-- A finite compactly supported measure and a rule of Gauss exactness with distinct
interior nodes have the classical integral derivative remainder with an interior point.
The nodal squared norm may be zero. Source: Gautschi (2004), Theorem 1.48;
operator derivations, (AQ3)–(AQ6).
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem exists_integral_sub_quadrature_eq_iteratedDeriv_mul_nodal_sq
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : 0 < n)
    (v w : Fin n → ℝ) (hv : Function.Injective v) (hva : ∀ i, v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * n, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * n) f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b, (∫ x, f x ∂μ) - ∑ i, w i * f (v i) =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial *
        ∫ x, (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
  let H := Lagrange.hermiteInterpolate univ v (f ∘ v) (deriv f ∘ v)
  have hHdeg : H.degree < (2 * n : ℕ) := by
    simpa [H] using Lagrange.degree_hermiteInterpolate_lt
      (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, mem_univ _⟩) hv.injOn _ _
  have hHnode (i : Fin n) : H.eval (v i) = f (v i) :=
    Lagrange.eval_hermiteInterpolate_at_node hv.injOn _ _ (mem_univ i)
  have hHintegral : (∫ x, H.eval x ∂μ) = ∑ i, w i * f (v i) := by
    rw [hexact H hHdeg]
    simp only [hHnode]
  have hfi : Integrable f μ := by
    refine (hf.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [hμ] with x hx hnot
    exact (hnot hx).elim
  have hHi := integrable_eval_of_ae_mem_Icc hμ H
  have hWi : Integrable (fun x => (Lagrange.nodal univ v).eval x ^ 2) μ := by
    have hp : (Lagrange.nodal univ v ^ 2).eval =
        fun x => (Lagrange.nodal univ v).eval x ^ 2 := by funext x; exact eval_pow 2
    rw [← hp]
    exact integrable_eval_of_ae_mem_Icc hμ _
  obtain ⟨ξ, hξ, hmean⟩ := exists_integral_eq_mul_integral_of_pointwise
    (s := Set.Ioo a b) (D := fun ξ => iteratedDeriv (2 * n) f ξ / (2 * n).factorial)
    (hfi.sub hHi) hWi (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (Set.nonempty_Ioo.mpr hab) isPreconnected_Ioo (hD.div_const (2 * n).factorial)
    (by
      filter_upwards [hμ] with x hx
      exact exists_sub_eval_hermiteInterpolate_eq hn hab hv hva hx hf hf')
  refine ⟨ξ, hξ, ?_⟩
  simpa only [Pi.sub_apply, integral_sub hfi hHi, hHintegral] using hmean

/-- When the squared nodal integral is zero, any rule of Gauss polynomial exactness
integrates every function exactly. This handles finite-support termination without
asserting interior locations for the terminal nodes.
Source: operator derivations, the zero-norm branch of (AQ6).
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem integral_eq_quadrature_of_integral_nodal_sq_eq_zero
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : 0 < n)
    (v w : Fin n → ℝ) (hv : Function.Injective v)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    (hz : (∫ x, (Lagrange.nodal univ v).eval x ^ 2 ∂μ) = 0) (f : ℝ → ℝ) :
    (∫ x, f x ∂μ) = ∑ i, w i * f (v i) := by
  classical
  let H := Lagrange.hermiteInterpolate univ v (f ∘ v) (fun _ => 0)
  have hHdeg : H.degree < (2 * n : ℕ) := by
    simpa [H] using Lagrange.degree_hermiteInterpolate_lt
      (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, mem_univ _⟩) hv.injOn _ _
  have hHnode (i : Fin n) : H.eval (v i) = f (v i) :=
    Lagrange.eval_hermiteInterpolate_at_node hv.injOn _ _ (mem_univ i)
  have hWi : Integrable (fun x => (Lagrange.nodal univ v).eval x ^ 2) μ := by
    have hp : (Lagrange.nodal univ v ^ 2).eval =
        fun x => (Lagrange.nodal univ v).eval x ^ 2 := by funext x; exact eval_pow 2
    rw [← hp]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hzero := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hWi).mp hz
  have hfeq : f =ᵐ[μ] H.eval := by
    filter_upwards [hzero] with x hx
    have hxzero : (Lagrange.nodal univ v).eval x = 0 := by
      simpa only [Pi.zero_apply, sq_eq_zero_iff] using hx
    rw [Lagrange.eval_nodal, prod_eq_zero_iff] at hxzero
    obtain ⟨i, _, hi⟩ := hxzero
    have hxi : x = v i := sub_eq_zero.mp hi
    rw [hxi, hHnode]
  rw [integral_congr_ae hfeq, hexact H hHdeg]
  simp only [hHnode]

end NLAlib
