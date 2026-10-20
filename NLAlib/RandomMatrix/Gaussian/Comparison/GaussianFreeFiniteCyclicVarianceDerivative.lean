import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteVarianceDerivative
import NLAlib.Matrix.Functions.MixedResolventInsertionHessian

/-! # Genuine cyclic finite-N Gaussian comparison derivative

The exact covariance interpolation is combined with the actual cyclic
Hessian identity. This retains two positive inverse arcs in every term,
which is the form needed for the source covariance cancellation argument.
Source: arXiv:2108.06312v2, Lemma 6.2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

open scoped Matrix.Norms.L2Operator in
/-- The actual finite-N expected mixed trace has the exact cyclic
diagonal-minus-GUE derivative. Both the source variance interpolation and
the cyclic regrouping are proved for this genuine coordinate model.
Source: arXiv:2108.06312v2, Lemma 6.2.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem hasDerivAt_integral_normalizedTrace_gaussianFreeFinite_mixed_resolvent_cyclic
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt
      (fun t : ℝ => ∫ x : E, normalizedTrace
        (resolvent (gaussianFreeFiniteInterpolation A₀ A t x) ζ ^ p *
          resolvent (gaussianFreeFiniteInterpolation A₀ A t x) (star ζ) ^ p)
        ∂gaussianVector K)
      ((1 / 2 : ℝ) •
        ((∑ i, ∑ r : n, ∫ x : E, cyclicMixedResolventHessian
          (gaussianFreeFiniteInterpolation A₀ A q x) ζ p
          (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)) ∂gaussianVector K) -
         (∑ i, ∑ k : GUECoordinate Unit n, ∫ x : E, cyclicMixedResolventHessian
          (gaussianFreeFiniteInterpolation A₀ A q x) ζ p
          (A i ⊗ₖ gueCoefficientMatrix k) ∂gaussianVector K))) q := by
  have hd := hasDerivAt_integral_normalizedTrace_gaussianFreeFinite_mixed_resolvent
    (n := n) A₀ hA₀ A hA ζ hζ p hq hq1
  dsimp only at hd
  have he (C : M) (hC : C.IsHermitian) (x : E) :
      (∑ j : Fin (p + p), ∑ k : Fin (p + p + 1), normalizedTrace
        (gaussianFreeFiniteBlockWord A₀ A q
          (resolventWordInsert (resolventWordInsert (mixedResolventWord ζ p) j C) k C) x)) =
        cyclicMixedResolventHessian (gaussianFreeFiniteInterpolation A₀ A q x) ζ p C := by
    simpa only [gaussianFreeFiniteBlockWord] using
      sum_twice_inserted_mixed_resolvent_trace_eq_cyclicHessian
        (gaussianFreeFiniteInterpolation A₀ A q x)
        (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x) C hC ζ hζ p
  have hl (i : ι) (r : n) (x : E) := he
    (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)) (by
      simpa only [gaussianFreeFiniteCoefficient, Real.sqrt_one, one_smul] using
        gaussianFreeFiniteCoefficient_isHermitian A hA 1 (.inl (i, r))) x
  have hr (i : ι) (k : GUECoordinate Unit n) (x : E) := he
    (A i ⊗ₖ gueCoefficientMatrix k) (by
      simpa only [gaussianFreeFiniteCoefficient, sub_zero, Real.sqrt_one, one_smul] using
        gaussianFreeFiniteCoefficient_isHermitian A hA 0 (.inr (i, k))) x
  simpa only [hl, hr] using hd

end NLAlib
