import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteMixedArcs
import NLAlib.Probability.Gaussian.Calculus.StandardCovarianceIntegral
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteExpectedWords
import NLAlib.Matrix.Norms.TraceSpectral
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Native finite-N arc covariance, with every analytic premise derived

The covariance formula is applied to literal mixed inverse powers of the
actual interpolating Hermitian matrix. It uses their genuine derivatives,
the actual Gaussian law, and the literal correlated-coordinate path.
Source: arXiv:2108.06312v2, Corollary 4.12 and Lemma 6.3.
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
/-- The true covariance of two native mixed resolvent arcs is the exact
single-coordinate derivative contraction under the actual product Gaussian
law. Smoothness, boundedness, and derivative domination are all derived;
no supplied covariance identity or comparison premise is required.
Source: arXiv:2108.06312v2, Corollary 4.12 and Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem integral_bilin_gaussianFreeFiniteMixedArc_covariance
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ)
    (B : M →L[ℝ] M →L[ℝ] ℂ) :
    let f := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b
    let g := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ c e
    let μ := gaussianVector K
    (∫ y : E, B (f y) (g y) ∂μ) - B (∫ y : E, f y ∂μ) (∫ y : E, g y ∂μ) =
      ∫ t : ℝ in (0 : ℝ)..1, ∑ k,
        ∫ w : E × E, B (fderiv ℝ f w.1 (Pi.single k 1))
          (fderiv ℝ g (t • w.1 + Real.sqrt (1 - t ^ 2) • w.2) (Pi.single k 1))
            ∂μ.prod μ := by
  dsimp only
  let f := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b
  let g := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ c e
  have hfc : ContDiff ℝ ⊤ f := contDiff_gaussianFreeFiniteMixedArc A₀ hA₀ A hA q ζ hζ a b
  have hgc : ContDiff ℝ ⊤ g := contDiff_gaussianFreeFiniteMixedArc A₀ hA₀ A hA q ζ hζ c e
  obtain ⟨Cf, Cd, _, _, hfb, hdfb⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ a b
  obtain ⟨Cg, Ce, _, _, hgb, hdgb⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ c e
  exact integral_bilin_sub_bilin_integrals_eq_standard_gaussian_gradient_integral
    f (fderiv ℝ f) g (fderiv ℝ g)
    (fun x => (hfc.differentiable (by simp) x).hasFDerivAt)
    (hfc.fderiv_right (m := ⊤) (by simp)).continuous
    (fun x => (hgc.differentiable (by simp) x).hasFDerivAt)
    (hgc.fderiv_right (m := ⊤) (by simp)).continuous
    Cf Cd Cg Ce hfb hdfb hgb hdgb B

open scoped Matrix.Norms.L2Operator in
/-- The literal normalized two-arc trace bilinear form with a fixed pair of
coefficient insertions. This preserves the matrix multiplication order. -/
def normalizedSandwichTraceBilinear (C : M) : M →L[ℝ] M →L[ℝ] ℂ :=
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  (ContinuousLinearMap.compL ℝ M M ℂ T).comp
    ((ContinuousLinearMap.mul ℝ M).comp (ContinuousLinearMap.mulLeftRight ℝ M C C))

open scoped Matrix.Norms.L2Operator in
/-- Evaluation of the actual normalized trace bilinear form. -/
@[simp] theorem normalizedSandwichTraceBilinear_apply (C U V : M) :
    normalizedSandwichTraceBilinear C U V = normalizedTrace (C * U * C * V) := by
  simp [normalizedSandwichTraceBilinear]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem mixedArc_eq_word (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (q : ℝ) (ζ : ℂ) (a b : ℕ) :
    gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b =
      gaussianFreeFiniteResolventWord A₀ A q
        (Fin.append (fun _ : Fin a => ζ) (fun _ : Fin b => star ζ)) := by
  funext x
  have ht : (fun j : Fin (a + b) => resolvent (gaussianFreeFiniteInterpolation A₀ A q x)
      (Fin.append (fun _ : Fin a => ζ) (fun _ : Fin b => star ζ) j)) =
      Fin.append (fun _ : Fin a => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ)
        (fun _ : Fin b => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (star ζ)) := by
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp only [Fin.append_left, Fin.append_right]
  simp only [gaussianFreeFiniteMixedArc, gaussianFreeFiniteResolventWord, ht,
    List.ofFn_fin_append, List.prod_append, List.ofFn_const, List.prod_replicate]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual expectation of a native mixed arc has exactly the tensor
symmetry needed for diagonal/GUE covariance cancellation. -/
theorem sum_diagonal_sub_gue_covariance_sandwich_integral_mixedArc
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) :
    let W := ∫ x : E, gaussianFreeFiniteMixedArc A₀ A q ζ a b x ∂gaussianVector K
    (∑ i, ∑ r : n, (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)) * W *
      (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ))) -
      (∑ i, ∑ k : GUECoordinate Unit n, (A i ⊗ₖ gueCoefficientMatrix k) * W *
        (A i ⊗ₖ gueCoefficientMatrix k)) = 0 := by
  dsimp only
  rw [mixedArc_eq_word]
  apply sum_diagonal_sub_gue_covariance_sandwich_integral_resolvent_word A₀ hA₀ A hA q
  intro j
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
  · simpa only [Fin.append_left] using hζ
  · simpa only [Fin.append_right, Complex.star_def, Complex.conj_im] using neg_ne_zero.mpr hζ

open scoped Matrix.Norms.L2Operator in
/-- The genuine difference of the two finite-N covariance trace forms. Its
coefficient families are the actual diagonal units and normalized GUE basis. -/
def gaussianFreeCovarianceDifferenceBilinear (A : ι → Matrix d d ℂ) :
    M →L[ℝ] M →L[ℝ] ℂ :=
  (∑ i, ∑ r : n, normalizedSandwichTraceBilinear
    (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ))) -
      ∑ i, ∑ k : GUECoordinate Unit n, normalizedSandwichTraceBilinear
        (A i ⊗ₖ gueCoefficientMatrix k)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem covarianceDifferenceBilinear_apply (A : ι → Matrix d d ℂ) (U V : M) :
    gaussianFreeCovarianceDifferenceBilinear A U V = normalizedTrace
      (((∑ i, ∑ r : n, (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ)) * U *
        (A i ⊗ₖ (Matrix.single r r 1 : Matrix n n ℂ))) -
          ∑ i, ∑ k : GUECoordinate Unit n, (A i ⊗ₖ gueCoefficientMatrix k) * U *
            (A i ⊗ₖ gueCoefficientMatrix k)) * V) := by
  simp only [gaussianFreeCovarianceDifferenceBilinear, sub_apply,
    sum_apply, normalizedSandwichTraceBilinear_apply,
    Matrix.sub_mul, Finset.sum_mul, normalizedTrace_sub]
  simp only [normalizedTrace, Matrix.trace_sum, Finset.mul_sum]

open scoped Matrix.Norms.L2Operator in
/-- The actual diagonal-minus-GUE two-arc expectation is a genuine Gaussian
gradient covariance. The product of the actual means cancels by proved
ensemble symmetry and the genuine coefficient covariance identity; no
cancellation or distribution premise is assumed.
Source: arXiv:2108.06312v2, Lemmas 6.2--6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem integral_covarianceDifference_gaussianFreeFiniteMixedArc_eq_gradient_integral
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ) :
    let f := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b
    let g := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ c e
    let B := gaussianFreeCovarianceDifferenceBilinear (n := n) A
    let μ := gaussianVector K
    (∫ y : E, B (f y) (g y) ∂μ) =
      ∫ t : ℝ in (0 : ℝ)..1, ∑ k,
        ∫ w : E × E, B (fderiv ℝ f w.1 (Pi.single k 1))
          (fderiv ℝ g (t • w.1 + Real.sqrt (1 - t ^ 2) • w.2) (Pi.single k 1))
            ∂μ.prod μ := by
  dsimp only
  have h := integral_bilin_gaussianFreeFiniteMixedArc_covariance A₀ hA₀ A hA q ζ hζ
    a b c e (gaussianFreeCovarianceDifferenceBilinear (n := n) A)
  dsimp only at h
  rw [covarianceDifferenceBilinear_apply,
    sum_diagonal_sub_gue_covariance_sandwich_integral_mixedArc A₀ hA₀ A hA q ζ hζ a b,
    Matrix.zero_mul, normalizedTrace_zero, sub_zero] at h
  exact h

end NLAlib
