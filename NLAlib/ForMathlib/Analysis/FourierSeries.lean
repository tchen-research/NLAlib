import NLAlib.ForMathlib.Analysis.FourierCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier coefficients of uniformly absolutely convergent series

Dominated convergence lets actual Fourier coefficients pass through a function series
with a scalar summable bound; character multiplication shifts the frequency.
-/

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate Real

namespace NLAlib

open scoped NLAlib.TwoPi

/-- Fourier coefficients commute with a uniformly dominated absolute function series.
Source: dominated convergence for Bochner integrals; helper for `chebyshev-series-exp-bessel`. -/
theorem hasSum_fourierCoeff_of_summable_bound {ι : Type*} [Countable ι]
    {F : ι → AddCircle (2 * Real.pi) → ℂ} {f : AddCircle (2 * Real.pi) → ℂ}
    {b : ι → ℝ} (hF : ∀ i, Continuous (F i)) (hb : Summable b)
    (hbound : ∀ i t, ‖F i t‖ ≤ b i) (hseries : ∀ t, HasSum (fun i => F i t) (f t))
    (k : ℤ) : HasSum (fun i => fourierCoeff (F i) k) (fourierCoeff f k) := by
  simp only [fourierCoeff]
  apply hasSum_integral_of_dominated_convergence (fun i _ => b i)
  · intro i
    exact ((fourier (-k)).continuous.smul (hF i)).aestronglyMeasurable
  · intro i
    apply Filter.Eventually.of_forall
    intro t
    rw [norm_smul, show ‖fourier (-k) t‖ = (1 : ℝ) from Circle.norm_coe _, one_mul]
    exact hbound i t
  · exact Filter.Eventually.of_forall (fun _ => hb)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun t => (hseries t).const_smul _)

/-- Multiplication by a Fourier character shifts the coefficient frequency.
Source: the character multiplication identity; helper for `chebyshev-series-exp-bessel`. -/
theorem fourierCoeff_fourier_mul (g : AddCircle (2 * Real.pi) → ℂ) (m k : ℤ) :
    fourierCoeff (fun t => fourier m t * g t) k = fourierCoeff g (k - m) := by
  unfold fourierCoeff
  congr 1
  funext t
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add]
  rw [show -k + m = -(k - m) by ring]

end NLAlib
