import NLAlib.Polynomial.OrthogonalPolynomials.MomentCoordinates
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional

/-!
# Polynomial data from finitely many measure moments

Absolute moments below degree `d` suffice to integrate every polynomial below
degree `d`. Extending that finite moment vector by zero gives a total linear
functional with exactly those integrals. No higher moment or positivity of the
extension at higher orders is asserted.
Source: Gautschi (2004), Chapters 1--2, finite moment construction.
-/

noncomputable section
open Polynomial MeasureTheory Finset
namespace NLAlib

/-- A finite list of absolute moments gives the corresponding ordinary moments. -/
theorem integrable_pow_of_integrable_abs_pow {μ : Measure ℝ} {d : ℕ}
    (hμ : ∀ j < d, Integrable (fun x : ℝ => |x| ^ j) μ) {j : ℕ} (hj : j < d) :
    Integrable (fun x : ℝ => x ^ j) μ := by
  apply (integrable_norm_iff (f := fun x : ℝ => x ^ j) (by fun_prop)).mp
  simpa only [Real.norm_eq_abs, abs_pow] using hμ j hj

/-- Finite absolute moments imply integrability throughout the finite polynomial
degree space, without assuming any higher moment. -/
theorem integrable_eval_of_degree_lt_of_abs_moments {μ : Measure ℝ} {d : ℕ}
    (hμ : ∀ j < d, Integrable (fun x : ℝ => |x| ^ j) μ)
    {p : ℝ[X]} (hp : p.degree < d) : Integrable p.eval μ := by
  have he : p.eval = fun x => ∑ i : Fin d, p.coeff i.val * x ^ i.val := by
    funext x
    nth_rw 1 [eq_sum_monomial_fin_of_degree_lt hp]
    simp only [eval_finsetSum, eval_monomial]
  rw [he]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_pow_of_integrable_abs_pow hμ i.isLt).const_mul _

/-- The zero extension of a finite measure moment vector agrees with integration
on its entire degree range. This explicitly pays every integrability obligation. -/
theorem finiteMomentFunctional_integral_apply {μ : Measure ℝ} {d : ℕ}
    (hμ : ∀ j < d, Integrable (fun x : ℝ => |x| ^ j) μ)
    {p : ℝ[X]} (hp : p.degree < d) :
    finiteMomentFunctional (fun i : Fin d => ∫ x, x ^ i.val ∂μ) p = ∫ x, p.eval x ∂μ := by
  rw [finiteMomentFunctional_apply]
  have he : p.eval = fun x => ∑ i : Fin d, p.coeff i.val * x ^ i.val := by
    funext x
    nth_rw 1 [eq_sum_monomial_fin_of_degree_lt hp]
    simp only [eval_finsetSum, eval_monomial]
  rw [he, integral_finsetSum _ (fun i _ =>
    (integrable_pow_of_integrable_abs_pow hμ i.isLt).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, mul_comm]

/-- The first `2n` ordinary measure moments, extended by zero. This convention
does not require higher moments to exist. -/
def finiteMeasureMomentFunctional (μ : Measure ℝ) (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  finiteMomentFunctional (fun i : Fin (2 * n) => ∫ x, x ^ i.val ∂μ)

/-- The finite measure moment functional evaluates every required polynomial by
its actual integral. -/
theorem finiteMeasureMomentFunctional_apply {μ : Measure ℝ} {n : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ)
    {p : ℝ[X]} (hp : p.degree < 2 * n) :
    finiteMeasureMomentFunctional μ n p = ∫ x, p.eval x ∂μ :=
  finiteMomentFunctional_integral_apply hμ hp

/-- The actual finite measure/support hypotheses imply positive definiteness of
the finite Hankel system. Only moments through degree `2n-1` are assumed; the
empty `n=0` system is also covered.
atlas: modified-chebyshev-algorithm (partial) -/
theorem posDef_hankelMomentMatrix_finiteMeasureMomentFunctional {μ : Measure ℝ} {n : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ)
    (hs : (n : ℕ∞) ≤ μ.support.encard) :
    (hankelMomentMatrix (finiteMeasureMomentFunctional μ n) n).PosDef := by
  rw [posDef_hankelMomentMatrix_iff_functional_sq_pos]
  intro p hp hp0
  have hpdeg := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have hsquare : (p ^ 2).degree < (2 * n : ℕ) := by
    rw [degree_pow, degree_eq_natDegree hp0, nsmul_eq_mul]
    exact_mod_cast (show 2 * p.natDegree < 2 * n by omega)
  rw [finiteMeasureMomentFunctional_apply hμ hsquare]
  simp only [eval_pow]
  apply integral_sq_eval_pos_of_le_support_encard hs hp0 hp
  simpa only [eval_pow] using integrable_eval_of_degree_lt_of_abs_moments hμ hsquare

/-- Canonical polynomials from the finite moment vector satisfy actual measure
orthogonality at every included order, including the terminal order `n`.
atlas: modified-chebyshev-algorithm (partial) -/
theorem integral_monicOrthogonalPolynomial_finiteMeasure_mul_eq_zero
    {μ : Measure ℝ} {n k : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ)
    (hs : (n : ℕ∞) ≤ μ.support.encard) (hk : k ≤ n)
    {q : ℝ[X]} (hq : q.degree < k) :
    ∫ x, (monicOrthogonalPolynomial (finiteMeasureMomentFunctional μ n) k).eval x *
      q.eval x ∂μ = 0 := by
  let L := finiteMeasureMomentFunctional μ n
  have hpos := posDef_hankelMomentMatrix_finiteMeasureMomentFunctional hμ hs
  have horth := (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos hk)).orthogonal q hq
  by_cases hq0 : q = 0
  · simp [hq0]
  have hqd := (natDegree_lt_iff_degree_lt hq0).mpr hq
  have hprod : (monicOrthogonalPolynomial L k * q).degree < (2 * n : ℕ) := by
    rw [degree_mul, degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
      natDegree_monicOrthogonalPolynomial, degree_eq_natDegree hq0]
    exact_mod_cast (show k + q.natDegree < 2 * n by omega)
  rw [finiteMeasureMomentFunctional_apply hμ hprod] at horth
  simpa only [eval_mul] using horth

end NLAlib
