import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteCyclicCovariance

/-! # Actual finite-N Gaussian/free moment differential comparison

The native variance derivative and genuine Gaussian crossing covariance
estimate give the source fractional-moment differential inequality with an
explicit universal polynomial in the moment order.
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

open scoped Matrix.Norms.L2Operator in
/-- The actual mean insertion covariance has the true finite number of
positive arc splits and no dimension loss in its moment bound. -/
theorem norm_gaussianFreeFiniteCovarianceInsertionMean_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
    (a b : ℕ) (hab : a + b = 2 * p + 1) :
    ‖gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ a b‖ ≤
      (2 * p + 1 : ℕ) * (2 * (2 * p + 2 : ℕ) ^ 2 : ℝ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        ∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ (p + 2)
          ∂gaussianVector K := by
  let V : ℝ := specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)
  let M : ℝ := ∫ x : E,
    resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ (p + 2) ∂gaussianVector K
  have hV : 0 ≤ V := mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hM : 0 ≤ M := integral_nonneg fun x => resolventEvenMoment_nonneg _ _ (by omega)
  unfold gaussianFreeFiniteCovarianceInsertionMean
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin (a + b), (2 * (2 * p + 2 : ℕ) ^ 2 : ℝ) * V * M := by
      apply Finset.sum_le_sum
      intro j _
      let l := mixedResolventSplitLeft a b j
      let r := mixedResolventSplitRight a b j
      have hs := mixedResolventSplit_lengths a b j
      have hl : l.1 + l.2 ≤ 2 * p + 2 := by dsimp only [l]; omega
      have hr : r.1 + r.2 ≤ 2 * p + 2 := by dsimp only [r]; omega
      have hmul : ((l.1 + l.2 : ℕ) : ℝ) * ((r.1 + r.2 : ℕ) : ℝ) ≤ (2 * p + 2 : ℕ) ^ (2 : ℕ) := by
        have hl' : ((l.1 + l.2 : ℕ) : ℝ) ≤ (2 * p + 2 : ℕ) := by exact_mod_cast hl
        have hr' : ((r.1 + r.2 : ℕ) : ℝ) ≤ (2 * p + 2 : ℕ) := by exact_mod_cast hr
        simpa only [pow_two] using mul_le_mul hl' hr'
          (Nat.cast_nonneg (r.1 + r.2)) (by positivity : (0 : ℝ) ≤ (2 * p + 2 : ℕ))
      have h := norm_integral_nativeMixedArc_covarianceDifference_le (n := n) A₀ hA₀ A hA hq hq1
        ζ hζ l.1 l.2 r.1 r.2 (m := p + 2) (by omega) (by dsimp only [l, r]; omega)
      refine h.trans ?_
      change 2 * ((l.1 + l.2 : ℕ) : ℝ) * ((r.1 + r.2 : ℕ) : ℝ) * V * M ≤ _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by nlinarith [hmul]) hV) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hab, nsmul_eq_mul]; ring

open scoped Matrix.Norms.L2Operator in
/-- The genuine finite-N moment derivative has the source fractional
moment bound with its actual original variance and unnormalized entry
covariance. There is no assumed Gaussian/free comparison or limiting law.
Source: arXiv:2108.06312v2, Lemmas 6.2--6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem exists_hasDerivAt_integral_gaussianFreeFinite_mixed_resolvent_norm_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ D : ℂ,
      HasDerivAt (fun t : ℝ => ∫ x : E, normalizedTrace
        (resolvent (gaussianFreeFiniteInterpolation A₀ A t x) ζ ^ p *
          resolvent (gaussianFreeFiniteInterpolation A₀ A t x) (star ζ) ^ p)
        ∂gaussianVector K) D q ∧
      ‖D‖ ≤ (2 * p * (2 * p + 1) * (2 * p + 2) ^ 2 : ℕ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        (|ζ.im|⁻¹) ^ 5 *
        (∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ p
          ∂gaussianVector K) ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  let I₁ := gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ (p + 1) p
  let I₂ := gaussianFreeFiniteCovarianceInsertionMean (n := n) A₀ A q ζ p (p + 1)
  let V : ℝ := specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)
  let M : ℝ := ∫ x : E,
    resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ (p + 2) ∂gaussianVector K
  have h₁ := norm_gaussianFreeFiniteCovarianceInsertionMean_le (n := n) A₀ hA₀ A hA hq.le hq1.le
    ζ hζ hp (p + 1) p (by omega)
  have h₂ := norm_gaussianFreeFiniteCovarianceInsertionMean_le (n := n) A₀ hA₀ A hA hq.le hq1.le
    ζ hζ hp p (p + 1) (by omega)
  have hV : 0 ≤ V := mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  refine ⟨(1 / 2 : ℝ) • ((p : ℝ) • I₁ + (p : ℝ) • I₂),
    hasDerivAt_integral_normalizedTrace_gaussianFreeFinite_mixed_resolvent_covariance
      A₀ hA₀ A hA ζ hζ p hq hq1, ?_⟩
  calc
    _ ≤ (1 / 2 : ℝ) * ((p : ℝ) * ‖I₁‖ + (p : ℝ) * ‖I₂‖) := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [norm_smul, Real.norm_natCast] using norm_add_le ((p : ℝ) • I₁) ((p : ℝ) • I₂)
    _ ≤ (2 * p * (2 * p + 1) * (2 * p + 2) ^ 2 : ℕ) * V * M := by
      dsimp only [I₁, I₂] at *
      have h := add_le_add (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg p))
        (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg p))
      have h := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
      dsimp only [V, M]
      push_cast at h ⊢
      nlinarith only [h]
    _ ≤ _ := by
      have h := integral_gaussianFreeFinite_resolventEvenMoment_add_two_le (n := n) A₀ hA₀ A hA q ζ hζ hp
      have h := mul_le_mul_of_nonneg_left h
        (mul_nonneg (Nat.cast_nonneg (2 * p * (2 * p + 1) * (2 * p + 2) ^ 2)) hV)
      simpa only [M, V, mul_assoc] using h

end NLAlib
