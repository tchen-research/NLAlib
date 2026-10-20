import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteCyclicVarianceDerivative
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteCovarianceMomentBound
import NLAlib.Matrix.Functions.MixedResolventInsertionArcSplit

/-! # Exact covariance form of the native cyclic Gaussian derivative

The genuine source variance derivative is regrouped using finite positive
arcs and actual integrability, preserving the diagonal-minus-GUE covariance
and every dimension normalization.
Source: arXiv:2108.06312v2, Lemmas 6.2--6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem integrable_nativeMixedArc_bilin
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ)
    (B : M →L[ℝ] M →L[ℝ] ℂ) :
    Integrable (fun x : E => B
      (gaussianFreeFiniteMixedArc A₀ A q ζ a b x)
      (gaussianFreeFiniteMixedArc A₀ A q ζ c e x)) (gaussianVector K) := by
  have hfc := (contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ a b (r := ⊤)).continuous
  have hgc := (contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ c e (r := ⊤)).continuous
  obtain ⟨Cf, _, hCf, _, hfb, _⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ a b
  obtain ⟨Cg, _, hCg, _, hgb, _⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ c e
  apply Integrable.of_bound ((B.continuous.comp hfc).clm_apply hgc).aestronglyMeasurable
    (‖B‖ * Cf * Cg)
  filter_upwards [] with x
  refine (B.le_opNorm₂ _ _).trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (by simpa only [specNorm_eq_norm] using hfb x) (norm_nonneg B))
    (by simpa only [specNorm_eq_norm] using hgb x) (norm_nonneg _) (by positivity)

open scoped Matrix.Norms.L2Operator in
/-- The genuine mean covariance difference of the actual positive arcs in
one cyclic derivative insertion. This is a definition of finite actual
Gaussian expectations, with no sign or comparison property built in. -/
def gaussianFreeFiniteCovarianceInsertionMean
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (q : ℝ) (ζ : ℂ) (a b : ℕ) : ℂ :=
  ∑ j : Fin (a + b), ∫ x : E, gaussianFreeCovarianceDifferenceBilinear (n := n) A
    (gaussianFreeFiniteMixedArc A₀ A q ζ
      (mixedResolventSplitLeft a b j).1 (mixedResolventSplitLeft a b j).2 x)
    (gaussianFreeFiniteMixedArc A₀ A q ζ
      (mixedResolventSplitRight a b j).1 (mixedResolventSplitRight a b j).2 x)
    ∂gaussianVector K

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The literal diagonal-minus-GUE expectation of the actual cyclic trace
insertion equals its positive-arc covariance mean. Every interchange is a
finite sum of actual integrable Gaussian functions. -/
theorem sum_integral_nativeMixedResolventTraceInsertion_sub_eq_covarianceMean
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) :
    (∑ i, ∑ r : n, ∫ x : E, mixedResolventTraceInsertion
      (gaussianFreeFiniteInterpolation A₀ A q x)
      (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ))
      (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)) ζ (star ζ) a b ∂gaussianVector K) -
    (∑ i, ∑ k : GUECoordinate Unit n, ∫ x : E, mixedResolventTraceInsertion
      (gaussianFreeFiniteInterpolation A₀ A q x)
      (A i ⊗ₖ gueCoefficientMatrix k) (A i ⊗ₖ gueCoefficientMatrix k) ζ (star ζ) a b
      ∂gaussianVector K) =
      gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ a b := by
  let μ := gaussianVector K
  let f (j : Fin (a + b)) := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ
    (mixedResolventSplitLeft a b j).1 (mixedResolventSplitLeft a b j).2
  let g (j : Fin (a + b)) := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ
    (mixedResolventSplitRight a b j).1 (mixedResolventSplitRight a b j).2
  let D (i : ι) (r : n) : M := A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)
  let G (i : ι) (k : GUECoordinate Unit n) : M := A i ⊗ₖ gueCoefficientMatrix k
  let I (B : M →L[ℝ] M →L[ℝ] ℂ) (j : Fin (a + b)) :=
    ∫ x : E, B (f j x) (g j x) ∂μ
  have hi (B : M →L[ℝ] M →L[ℝ] ℂ) (j : Fin (a + b)) :
      Integrable (fun x : E => B (f j x) (g j x)) μ :=
    integrable_nativeMixedArc_bilin A₀ hA₀ A hA q ζ hζ _ _ _ _ B
  have hsplit (C : M) : (∫ x : E, mixedResolventTraceInsertion
      (gaussianFreeFiniteInterpolation A₀ A q x) C C ζ (star ζ) a b ∂μ) =
      ∑ j : Fin (a + b), I (normalizedSandwichTraceBilinear C) j := by
    simp_rw [mixedResolventTraceInsertion_eq_sum_split]
    change (∫ x : E, ∑ j : Fin (a + b), normalizedSandwichTraceBilinear C (f j x) (g j x) ∂μ) = _
    exact integral_finsetSum _ fun j _ => hi _ j
  have hdiff (j : Fin (a + b)) :
      I (gaussianFreeCovarianceDifferenceBilinear (n := n) A) j =
      (∑ i, ∑ r : n, I (normalizedSandwichTraceBilinear (D i r)) j) -
        ∑ i, ∑ k : GUECoordinate Unit n, I (normalizedSandwichTraceBilinear (G i k)) j := by
    dsimp only [I]
    simp only [gaussianFreeCovarianceDifferenceBilinear, sub_apply, sum_apply]
    rw [integral_sub
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun r _ => hi _ j)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hi _ j)]
    simp only [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun r _ => hi _ j,
      integral_finsetSum _ fun r _ => hi _ j]
    rfl
  let J (C : M) := ∫ x : E, mixedResolventTraceInsertion
    (gaussianFreeFiniteInterpolation A₀ A q x) C C ζ (star ζ) a b ∂μ
  have hJ : J = fun C : M => ∑ j : Fin (a + b), I (normalizedSandwichTraceBilinear C) j :=
    funext hsplit
  change (∑ i, ∑ r : n, J (D i r)) - (∑ i, ∑ k : GUECoordinate Unit n, J (G i k)) = _
  rw [hJ]
  change (∑ i, ∑ r : n, ∑ j : Fin (a + b), I (normalizedSandwichTraceBilinear (D i r)) j) -
    (∑ i, ∑ k : GUECoordinate Unit n, ∑ j : Fin (a + b), I (normalizedSandwichTraceBilinear (G i k)) j) =
      ∑ j : Fin (a + b), I (gaussianFreeCovarianceDifferenceBilinear (n := n) A) j
  simp_rw [hdiff, Finset.sum_sub_distrib]
  congr 1
  · calc
      _ = ∑ i, ∑ j : Fin (a + b), ∑ r : n, I (normalizedSandwichTraceBilinear (D i r)) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  · calc
      _ = ∑ i, ∑ j : Fin (a + b), ∑ k : GUECoordinate Unit n,
          I (normalizedSandwichTraceBilinear (G i k)) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem integrable_nativeMixedResolventTraceInsertion
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) (C : M) :
    Integrable (fun x : E => mixedResolventTraceInsertion
      (gaussianFreeFiniteInterpolation A₀ A q x) C C ζ (star ζ) a b) (gaussianVector K) := by
  have hi (j : Fin (a + b)) : Integrable (fun x : E => normalizedSandwichTraceBilinear C
      (gaussianFreeFiniteMixedArc A₀ A q ζ
        (mixedResolventSplitLeft a b j).1 (mixedResolventSplitLeft a b j).2 x)
      (gaussianFreeFiniteMixedArc A₀ A q ζ
        (mixedResolventSplitRight a b j).1 (mixedResolventSplitRight a b j).2 x))
      (gaussianVector K) := integrable_nativeMixedArc_bilin A₀ hA₀ A hA q ζ hζ _ _ _ _ _
  apply (integrable_finsetSum _ fun j _ => hi j).congr
  filter_upwards [] with x
  exact (mixedResolventTraceInsertion_eq_sum_split
    (gaussianFreeFiniteInterpolation A₀ A q x) C ζ a b).symm

open scoped Matrix.Norms.L2Operator in
/-- The actual native moment derivative is its literal sum of true
positive-arc covariance means. The cyclic Hessian, finite integral
interchanges, and coefficient covariance cancellation are all proved.
Source: arXiv:2108.06312v2, Lemmas 6.2--6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem hasDerivAt_integral_normalizedTrace_gaussianFreeFinite_mixed_resolvent_covariance
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt
      (fun t : ℝ => ∫ x : E, normalizedTrace
        (resolvent (gaussianFreeFiniteInterpolation A₀ A t x) ζ ^ p *
          resolvent (gaussianFreeFiniteInterpolation A₀ A t x) (star ζ) ^ p)
        ∂gaussianVector K)
      ((1 / 2 : ℝ) • ((p : ℝ) •
        gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ (p + 1) p +
          (p : ℝ) • gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ p (p + 1))) q := by
  let μ := gaussianVector K
  let D (i : ι) (r : n) : M := A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)
  let G (i : ι) (k : GUECoordinate Unit n) : M := A i ⊗ₖ gueCoefficientMatrix k
  let I (a b : ℕ) (C : M) := ∫ x : E,
    mixedResolventTraceInsertion (gaussianFreeFiniteInterpolation A₀ A q x) C C ζ (star ζ) a b ∂μ
  have hcyclic (C : M) : (∫ x : E, cyclicMixedResolventHessian
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p C ∂μ) =
      (p : ℝ) • I (p + 1) p C + (p : ℝ) • I p (p + 1) C := by
    simp only [cyclicMixedResolventHessian]
    have hi₁ : Integrable (fun x : E => (p : ℝ) • mixedResolventTraceInsertion
        (gaussianFreeFiniteInterpolation A₀ A q x) C C ζ (star ζ) (p + 1) p) μ := by
      simpa only [Pi.smul_apply] using! Integrable.smul (p : ℝ)
        (integrable_nativeMixedResolventTraceInsertion A₀ hA₀ A hA q ζ hζ (p + 1) p C)
    have hi₂ : Integrable (fun x : E => (p : ℝ) • mixedResolventTraceInsertion
        (gaussianFreeFiniteInterpolation A₀ A q x) C C ζ (star ζ) p (p + 1)) μ := by
      simpa only [Pi.smul_apply] using! Integrable.smul (p : ℝ)
        (integrable_nativeMixedResolventTraceInsertion A₀ hA₀ A hA q ζ hζ p (p + 1) C)
    rw [integral_add hi₁ hi₂, integral_smul, integral_smul]
  have he (a b : ℕ) : (∑ i, ∑ r : n, I a b (D i r)) -
      (∑ i, ∑ k : GUECoordinate Unit n, I a b (G i k)) =
      gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ a b :=
    sum_integral_nativeMixedResolventTraceInsertion_sub_eq_covarianceMean A₀ hA₀ A hA q ζ hζ a b
  have hd := hasDerivAt_integral_normalizedTrace_gaussianFreeFinite_mixed_resolvent_cyclic
    (n := n) A₀ hA₀ A hA ζ hζ p hq hq1
  let J (C : M) := ∫ x : E, cyclicMixedResolventHessian
    (gaussianFreeFiniteInterpolation A₀ A q x) ζ p C ∂μ
  have hJ : J = fun C : M => (p : ℝ) • I (p + 1) p C + (p : ℝ) • I p (p + 1) C :=
    funext hcyclic
  change HasDerivAt _ ((1 / 2 : ℝ) •
    ((∑ i, ∑ r : n, J (D i r)) - (∑ i, ∑ k : GUECoordinate Unit n, J (G i k)))) q at hd
  rw [hJ] at hd
  have hderiv : ((∑ i, ∑ r : n, ((p : ℝ) • I (p + 1) p (D i r) +
      (p : ℝ) • I p (p + 1) (D i r))) -
      (∑ i, ∑ k : GUECoordinate Unit n, ((p : ℝ) • I (p + 1) p (G i k) +
        (p : ℝ) • I p (p + 1) (G i k)))) =
      (p : ℝ) • gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ (p + 1) p +
      (p : ℝ) • gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ p (p + 1) := by
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← he (p + 1) p, ← he p (p + 1)]
    simp only [smul_sub]
    abel
  exact hd.congr_deriv (congrArg (fun z : ℂ => (1 / 2 : ℝ) • z) hderiv)

end NLAlib
