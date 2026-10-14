import NLAlib.Polynomial.OrthogonalPolynomials.Symmetry
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Squaring a polynomial-moment measure

The native square-map pushforward and its square-density variant have every
polynomial moment. Their polynomial integrals are the even and odd squared
variable forms, and support nondegeneracy descends to both finite Hankel systems.
Source: Gautschi (2004), Theorem 1.18; operator derivations OP17–OP19.
-/

noncomputable section

open Polynomial MeasureTheory

namespace NLAlib

/-- Squaring the variable preserves every finite polynomial moment. -/
theorem hasPolynomialMoments_map_sq {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) :
    HasPolynomialMoments (Measure.map (fun x : ℝ => x ^ 2) μ) := by
  intro p
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  convert hμ (p.comp (X ^ 2)) using 1
  ext x
  simp

/-- Multiplying a measure by the nonnegative square density preserves finite
polynomial moments. -/
theorem hasPolynomialMoments_withDensity_sq {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) :
    HasPolynomialMoments (μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))) := by
  intro p
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  convert hμ (X ^ 2 * p) using 1
  ext x
  simp

/-- A polynomial integral against the squared-variable pushforward is its
composition with `X²` integrated against the original measure. -/
theorem polynomialIntegral_map_sq (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) (p : ℝ[X]) :
    polynomialIntegral (Measure.map (fun x : ℝ => x ^ 2) μ) (hasPolynomialMoments_map_sq hμ) p =
      polynomialIntegral μ hμ (p.comp (X ^ 2)) := by
  rw [polynomialIntegral_apply,
    integral_map_of_stronglyMeasurable (by fun_prop) p.continuous.stronglyMeasurable]
  simp only [polynomialIntegral_apply, eval_comp, eval_pow, eval_X]

/-- A square-density polynomial integral is the polynomial product with `X²`
integrated against the original measure. -/
theorem polynomialIntegral_withDensity_sq (μ : Measure ℝ) (hμ : HasPolynomialMoments μ)
    (p : ℝ[X]) :
    polynomialIntegral (μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2)))
      (hasPolynomialMoments_withDensity_sq hμ) p = polynomialIntegral μ hμ (X ^ 2 * p) := by
  rw [polynomialIntegral_apply, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, polynomialIntegral_apply,
    eval_mul, eval_pow, eval_X]

/-- Squaring the variable preserves the order-`k` Hankel nondegeneracy whenever
the original measure has at least `2k` support points. Symmetry is not needed. -/
theorem hankelMomentDet_map_sq_ne_zero {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {k : ℕ} (hk : (2 * k : ℕ∞) ≤ μ.support.encard) :
    hankelMomentDet
      (polynomialIntegral (Measure.map (fun x : ℝ => x ^ 2) μ) (hasPolynomialMoments_map_sq hμ)) k ≠ 0 := by
  let ν := Measure.map (fun x : ℝ => x ^ 2) μ
  let hν := hasPolynomialMoments_map_sq hμ
  have hpos : (hankelMomentMatrix (polynomialIntegral ν hν) k).PosDef := by
    apply (posDef_hankelMomentMatrix_iff_integral_sq_eval_pos ν hν k).mpr
    intro p hp hp0
    let r := p.comp (X ^ 2)
    have hr0 : r ≠ 0 := (expand_ne_zero (by decide : 0 < 2)).mpr hp0
    have hrd : r.degree < (2 * k : ℕ) := by
      rw [degree_eq_natDegree hr0]
      have hnat : r.natDegree = p.natDegree * 2 := natDegree_expand 2 p
      rw [hnat]
      have hp' := (natDegree_lt_iff_degree_lt hp0).mpr hp
      exact_mod_cast (show p.natDegree * 2 < 2 * k by omega)
    have h := integral_sq_eval_pos_of_le_support_encard hk hr0 hrd (hμ.integrable_sq r)
    dsimp only [ν]
    have hsm : StronglyMeasurable (fun x : ℝ => p.eval x ^ 2) :=
      (p.continuous.pow 2).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable (φ := fun x : ℝ => x ^ 2)
      (f := fun x : ℝ => p.eval x ^ 2) (by fun_prop) hsm]
    simpa only [r, eval_comp, eval_pow, eval_X] using h
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det _ |>.mp hpos.isUnit)

/-- The odd squared-variable moment system is nonsingular whenever the original
measure has at least `2k+1` support points. This also covers mass at zero. -/
theorem hankelMomentDet_map_sq_withDensity_sq_ne_zero {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {k : ℕ} (hk : (2 * k + 1 : ℕ∞) ≤ μ.support.encard) :
    hankelMomentDet
      (polynomialIntegral
        (Measure.map (fun x : ℝ => x ^ 2) (μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))))
        (hasPolynomialMoments_map_sq (hasPolynomialMoments_withDensity_sq hμ))) k ≠ 0 := by
  let ν := Measure.map (fun x : ℝ => x ^ 2) (μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2)))
  let hν := hasPolynomialMoments_map_sq (hasPolynomialMoments_withDensity_sq hμ)
  have hpos : (hankelMomentMatrix (polynomialIntegral ν hν) k).PosDef := by
    apply (posDef_hankelMomentMatrix_iff_integral_sq_eval_pos ν hν k).mpr
    intro p hp hp0
    let r := X * p.comp (X ^ 2)
    have hpcomp0 : p.comp (X ^ 2) ≠ 0 := (expand_ne_zero (by decide : 0 < 2)).mpr hp0
    have hr0 : r ≠ 0 := mul_ne_zero X_ne_zero hpcomp0
    have hrd : r.degree < (2 * k + 1 : ℕ) := by
      rw [degree_eq_natDegree hr0]
      have hnat : r.natDegree = p.natDegree * 2 + 1 := by
        rw [natDegree_X_mul hpcomp0]
        exact congrArg (fun i : ℕ => i + 1) (natDegree_expand 2 p)
      rw [hnat]
      have hp' := (natDegree_lt_iff_degree_lt hp0).mpr hp
      exact_mod_cast (show p.natDegree * 2 + 1 < 2 * k + 1 by omega)
    have h := integral_sq_eval_pos_of_le_support_encard hk hr0 hrd (hμ.integrable_sq r)
    dsimp only [ν]
    have hsm : StronglyMeasurable (fun x : ℝ => p.eval x ^ 2) :=
      (p.continuous.pow 2).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable (φ := fun x : ℝ => x ^ 2)
      (f := fun x : ℝ => p.eval x ^ 2) (by fun_prop) hsm,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
    simpa only [r, eval_mul, eval_comp, eval_pow, eval_X, mul_pow] using h
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det _ |>.mp hpos.isUnit)

end NLAlib
