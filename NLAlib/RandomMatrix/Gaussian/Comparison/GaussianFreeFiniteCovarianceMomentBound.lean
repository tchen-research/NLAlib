import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteGradientMomentBound

/-! # Genuine native two-arc covariance moment bound

The actual Gaussian covariance integral is estimated using the actual
coefficient crossing calculation. Both diagonal and GUE coefficient budgets
are derived from their native matrices.
Source: arXiv:2108.06312v2, Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Kronecker ComplexOrder MatrixOrder
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

open scoped Matrix.Norms.L2Operator in
private theorem integrable_nativeMixedArc_gradient_bilin
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ)
    (B : M →L[ℝ] M →L[ℝ] ℂ) (Y Z : E × E → E)
    (hY : Continuous Y) (hZ : Continuous Z) (k : K) :
    Integrable (fun w : E × E => B
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) (Y w) (Pi.single k 1))
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ c e) (Z w) (Pi.single k 1)))
        ((gaussianVector K).prod (gaussianVector K)) := by
  let f := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b
  let g := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ c e
  let u : E := Pi.single k 1
  have hfc₀ := contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ a b (r := ⊤)
  have hgc₀ := contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ c e (r := ⊤)
  have hdfc : Continuous (fderiv ℝ f) := (hfc₀.fderiv_right (m := ⊤) (by simp)).continuous
  have hdgc : Continuous (fderiv ℝ g) := (hgc₀.fderiv_right (m := ⊤) (by simp)).continuous
  obtain ⟨Cf, Cd, _, hCd, _, hdfb⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ a b
  obtain ⟨Cg, Ce, _, hCe, _, hdgb⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ c e
  have hfc : Continuous (fun w => fderiv ℝ f (Y w) u) :=
    (hdfc.comp hY).clm_apply continuous_const
  have hgc : Continuous (fun w => fderiv ℝ g (Z w) u) :=
    (hdgc.comp hZ).clm_apply continuous_const
  apply Integrable.of_bound ((B.continuous.comp hfc).clm_apply hgc).aestronglyMeasurable
    (‖B‖ * (Cd * ‖u‖) * (Ce * ‖u‖))
  filter_upwards [] with w
  apply (B.le_opNorm₂ _ _).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hdfb _) (norm_nonneg u))) (norm_nonneg B)
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hdgb _) (norm_nonneg u))
  · positivity
  · positivity

open scoped Matrix.Norms.L2Operator in
/-- The exact native covariance-gradient integrand is bounded uniformly
along the actual correlation path by the original covariance budgets and
the true expected higher Gram moment. -/
theorem norm_sum_integral_nativeMixedArc_covarianceDifference_gradient_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ) {m : ℕ} (hm : 0 < m)
    (hL : a + b + c + e + 2 = 2 * m) {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    ‖∑ k : K, ∫ w : E × E, gaussianFreeCovarianceDifferenceBilinear (n := n) A
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) w.1 (Pi.single k 1))
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ c e)
        (t • w.1 + Real.sqrt (1 - t ^ 2) • w.2) (Pi.single k 1))
        ∂(gaussianVector K).prod (gaussianVector K)‖ ≤
      2 * ((a + b : ℕ) : ℝ) * ((c + e : ℕ) : ℝ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        ∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ m
          ∂gaussianVector K := by
  let μ := gaussianVector K
  let D : ι × n → M := fun ir => A ir.1 ⊗ₖ (Matrix.single ir.2 ir.2 1 : Matrix n n ℂ)
  let G : ι × GUECoordinate Unit n → M := fun ik => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2
  let Y : E × E → E := Prod.fst
  let Z : E × E → E := fun w => t • w.1 + Real.sqrt (1 - t ^ 2) • w.2
  let f := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b
  let g := gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ c e
  let FD : E × E → ℂ := fun w => ∑ k : K, ∑ ir : ι × n,
    normalizedSandwichTraceBilinear (D ir) (fderiv ℝ f (Y w) (Pi.single k 1))
      (fderiv ℝ g (Z w) (Pi.single k 1))
  let FG : E × E → ℂ := fun w => ∑ k : K, ∑ ik : ι × GUECoordinate Unit n,
    normalizedSandwichTraceBilinear (G ik) (fderiv ℝ f (Y w) (Pi.single k 1))
      (fderiv ℝ g (Z w) (Pi.single k 1))
  have hYc : Continuous Y := continuous_fst
  have hZc : Continuous Z := by
    have hy : Continuous (Prod.fst : E × E → E) := continuous_fst
    have hz : Continuous (Prod.snd : E × E → E) := continuous_snd
    simpa +instances only [Z, Pi.add_def, Pi.smul_def] using!
      (hy.const_smul t).add (hz.const_smul (Real.sqrt (1 - t ^ 2)))
  have hiB (B : M →L[ℝ] M →L[ℝ] ℂ) (k : K) :
      Integrable (fun w : E × E => B (fderiv ℝ f (Y w) (Pi.single k 1))
        (fderiv ℝ g (Z w) (Pi.single k 1))) (μ.prod μ) :=
    integrable_nativeMixedArc_gradient_bilin A₀ hA₀ A hA q ζ hζ a b c e B Y Z hYc hZc k
  have hiD : Integrable FD (μ.prod μ) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun ir _ => hiB _ k
  have hiG : Integrable FG (μ.prod μ) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun ik _ => hiB _ k
  have hDe (ir : ι × n) : (D ir).IsHermitian := by
    simpa only [D, gaussianFreeFiniteCoefficient, Real.sqrt_one, one_smul] using
      gaussianFreeFiniteCoefficient_isHermitian A hA 1 (.inl ir)
  have hGe (ik : ι × GUECoordinate Unit n) : (G ik).IsHermitian := by
    simpa only [G, gaussianFreeFiniteCoefficient, sub_zero, Real.sqrt_one, one_smul] using
      gaussianFreeFiniteCoefficient_isHermitian A hA 0 (.inr ik)
  have hGW : specNorm (coefficientCovariance G) ≤ specNorm (coefficientCovariance A) := by
    rw [specNorm_coefficientCovariance_kronecker_gueCoefficientMatrix]
    by_cases hn : Fintype.card n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact specNorm_nonneg _
    · exact div_le_self (specNorm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hYp : MeasurePreserving Y (μ.prod μ) μ := measurePreserving_fst
  have hZp : MeasurePreserving Z (μ.prod μ) μ :=
    measurePreserving_standardGaussianCorrelation (κ := K) t ht ht1
  have hD := norm_integral_nativeMixedArc_gradient_sandwich_le D hDe A₀ hA₀ A hA hq hq1
    (specNorm_coefficientVariance_kronecker_diagonal_single_le A)
    (specNorm_coefficientCovariance_kronecker_diagonal_single_le A)
    ζ hζ a b c e hm hL Y Z hYp hZp
  have hG := norm_integral_nativeMixedArc_gradient_sandwich_le G hGe A₀ hA₀ A hA hq hq1
    (specNorm_coefficientVariance_kronecker_gueCoefficientMatrix_le A) hGW
    ζ hζ a b c e hm hL Y Z hYp hZp
  have heq (w : E × E) : (∑ k : K, gaussianFreeCovarianceDifferenceBilinear (n := n) A
      (fderiv ℝ f (Y w) (Pi.single k 1)) (fderiv ℝ g (Z w) (Pi.single k 1))) = FD w - FG w := by
    simp only [FD, FG, gaussianFreeCovarianceDifferenceBilinear, sub_apply, sum_apply,
      Finset.sum_sub_distrib, Fintype.sum_prod_type, D, G]
  calc
    _ = ‖∫ w : E × E, FD w - FG w ∂μ.prod μ‖ := by
      rw [← integral_finsetSum _ fun k _ => hiB _ k]
      simp only [heq]
    _ ≤ ‖∫ w, FD w ∂μ.prod μ‖ + ‖∫ w, FG w ∂μ.prod μ‖ := by
      rw [integral_sub hiD hiG]
      exact norm_sub_le _ _
    _ ≤ _ := by
      have h := add_le_add hD hG
      simpa only [FD, FG, f, g, two_mul, add_mul, mul_assoc] using h

open scoped Matrix.Norms.L2Operator in
/-- The actual native two-arc covariance is bounded by the original
variance/covariance product and the expected native higher Gram moment.
All Gaussian identities, parameter bounds, and marginal laws are derived.
Source: arXiv:2108.06312v2, Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem norm_integral_nativeMixedArc_covarianceDifference_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ) {m : ℕ} (hm : 0 < m)
    (hL : a + b + c + e + 2 = 2 * m) :
    ‖∫ x : E, gaussianFreeCovarianceDifferenceBilinear (n := n) A
      (gaussianFreeFiniteMixedArc A₀ A q ζ a b x)
      (gaussianFreeFiniteMixedArc A₀ A q ζ c e x) ∂gaussianVector K‖ ≤
      2 * ((a + b : ℕ) : ℝ) * ((c + e : ℕ) : ℝ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        ∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ m
          ∂gaussianVector K := by
  rw [integral_covarianceDifference_gaussianFreeFiniteMixedArc_eq_gradient_integral
    A₀ hA₀ A hA q ζ hζ a b c e]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (fun t ht => by
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      exact norm_sum_integral_nativeMixedArc_covarianceDifference_gradient_le
        (n := n) A₀ hA₀ A hA hq hq1 ζ hζ a b c e hm hL (t := t)
        (by linarith [ht'.1]) ht'.2)
  simpa only [sub_zero, abs_one, mul_one] using h

end NLAlib
