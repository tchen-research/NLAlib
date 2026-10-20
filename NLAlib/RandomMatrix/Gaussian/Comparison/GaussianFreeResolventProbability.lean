import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeRootMomentComparison
import NLAlib.Probability.Free.WordNativeUniformResolventMoments
import NLAlib.ForMathlib.Analysis.CStarAlgebra.PositiveGramNorm
import NLAlib.Probability.Transforms.ResolventNormMoments
import NLAlib.ForMathlib.MeasureTheory.LpMarkov
import NLAlib.Probability.Concentration.Matrix.GaussianResolventSeries
import NLAlib.Probability.SubGaussian.LpMoments
import NLAlib.Matrix.Norms.BilinearSphereParameters

/-! # Actual two-sided Gaussian/free resolvent probability comparison

The actual interpolation moment bound, native free resolvent moments,
Markov inequality and Gaussian concentration supply both probability bounds.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d]
  [DecidableEq ι] [DecidableEq d] [Nonempty d]

open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian resolvent exceeds the actual native free resolvent
plus the interpolation error with an explicit even-moment Markov tail.
Source: arXiv:2108.06312v2, Theorem 6.2, and arXiv:2406.11453v2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_specNorm_gaussian_resolvent_gt_free_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    let B : ℝ := ((2*p+1)*(2*p+2)^2 : ℕ) *
      (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) * (|ζ.im|⁻¹)^5
    (gaussianVector ι).real {x : ι → ℝ |
      Real.exp 1 * (Fintype.card d : ℝ) ^ (1 / ((2*p : ℕ) : ℝ)) *
        (‖resolvent (wordNativeMatrixLinearCombination A₀ A) ζ‖ + B) <
          specNorm (resolvent (A₀ + ∑ i, x i • A i) ζ)} ≤ Real.exp (-((2*p : ℕ) : ℝ)) := by
  classical
  dsimp only
  let X : (ι → ℝ) → Matrix d d ℂ := fun x => A₀ + ∑ i, x i • A i
  have hXm : Measurable X := by unfold X; fun_prop
  have hX (x : ι → ℝ) : (X x).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  let B : ℝ := ((2*p+1)*(2*p+2)^2 : ℕ) *
    (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) * (|ζ.im|⁻¹)^5
  let L : ℝ := lpNorm (fun x => specNorm (resolvent (X x) ζ)) (2*(p : ℝ≥0∞)) (gaussianVector ι)
  have hroot : ((wordMatrixVacuumExpectation
      ((star (resolvent (wordNativeMatrixLinearCombination A₀ A) ζ) *
        resolvent (wordNativeMatrixLinearCombination A₀ A) ζ)^p)).re) ^
          (1 / ((2*p : ℕ) : ℝ)) ≤ ‖resolvent (wordNativeMatrixLinearCombination A₀ A) ζ‖ := by
    exact (wordMatrixVacuumPositiveMap (D := d) (ι := ι)).gramMoment_rpow_le_norm
      wordMatrixVacuumExpectation_one _ hp
  have hcomp := (abs_sub_le_iff.mp
    (abs_gaussian_wordNative_resolventEvenMoment_rpow_sub_le A₀ hA₀ A hA ζ hζ hp)).1
  have hL : L ≤ (Fintype.card d : ℝ) ^ (1 / ((2*p : ℕ) : ℝ)) *
      (‖resolvent (wordNativeMatrixLinearCombination A₀ A) ζ‖ + B) := by
    refine (lpNorm_specNorm_resolvent_le_card_rpow_mul_integral_resolventEvenMoment_rpow_inv
      (gaussianVector ι) X hXm.aemeasurable (Filter.Eventually.of_forall hX) hζ hp).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    dsimp only [X] at *
    linarith
  have hm0 := measureReal_lt_exp_mul_lpNorm_le_exp_neg (by omega : 0 < 2*p)
    (memLp_specNorm_resolvent (gaussianVector ι) X hXm.aemeasurable
      (Filter.Eventually.of_forall hX) hζ ((2*p : ℕ) : ℝ≥0∞))
  have hm : (gaussianVector ι).real {x | Real.exp 1 * L <
      ‖specNorm (resolvent (X x) ζ)‖} ≤ Real.exp (-((2*p : ℕ) : ℝ)) := by
    simpa only [L, Nat.cast_mul, Nat.cast_ofNat] using hm0
  refine le_trans ?_ hm
  apply measureReal_mono _ (by finiteness)
  intro x hx
  change Real.exp 1 * L < ‖specNorm (resolvent (X x) ζ)‖
  rw [Real.norm_of_nonneg (specNorm_nonneg _)]
  exact lt_of_le_of_lt (by simpa only [B, mul_assoc] using
    mul_le_mul_of_nonneg_left hL (Real.exp_pos 1).le) hx

omit [DecidableEq ι] [Nonempty d] in
open scoped Matrix.Norms.L2Operator in
/-- At a point above the actual free spectrum, the actual free resolvent
is controlled by the actual Gaussian resolvent with the source logarithmic
moment loss and its genuine sigma-star Gaussian fluctuation.
Source: arXiv:2406.11453v2, Corollary 4.4 and Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_free_resolvent_gt_gaussian_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℕ} (hq : 0 < q) (hlog : Real.log (Fintype.card d : ℝ) ≤ q)
    {ζ : ℂ} (hζ : 0 < ζ.im)
    (hspec : ζ.re ∈ spectrum ℝ (wordNativeMatrixLinearCombination A₀ A))
    {t : ℝ} (ht : 0 ≤ t) :
    let c : ℝ := bilinearSquareMass A Finset.univ * (|ζ.im|⁻¹)^4
    let B : ℝ := ((2*(2*q)+1)*(2*(2*q)+2)^2 : ℕ) *
      (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) * (|ζ.im|⁻¹)^5
    let E : ℝ := Real.sqrt (specNorm (∑ k, A k^2)) / ((Fintype.card d : ℝ)^2 * ζ.im^2)
    (gaussianVector ι).real {x : ι → ℝ |
      (438*Real.exp 5) * (specNorm (resolvent (A₀ + ∑ i, x i • A i) ζ) +
        Real.sqrt (4*c*(2*q)) + t + B + E) <
          ‖resolvent (wordNativeMatrixLinearCombination A₀ A) ζ‖} ≤
        2 * Real.exp (-t^2/(2*c)) := by
  classical
  dsimp only
  let X : (ι → ℝ) → Matrix d d ℂ := fun x => A₀ + ∑ i, x i • A i
  have hXm : Measurable X := by unfold X; fun_prop
  have hX (x : ι → ℝ) : (X x).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  let c : ℝ := bilinearSquareMass A Finset.univ * (|ζ.im|⁻¹)^4
  have hc : 0 ≤ c := mul_nonneg (bilinearSquareMass_nonneg _ _) (by positivity)
  let C : ℝ := 438*Real.exp 5
  have hC : 0 < C := by dsimp only [C]; positivity
  let B : ℝ := ((2*(2*q)+1)*(2*(2*q)+2)^2 : ℕ) *
    (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) * (|ζ.im|⁻¹)^5
  let E : ℝ := Real.sqrt (specNorm (∑ k, A k^2)) / ((Fintype.card d : ℝ)^2 * ζ.im^2)
  let L : ℝ := lpNorm (fun x => specNorm (resolvent (X x) ζ))
    (2*((2*q : ℕ) : ℝ≥0∞)) (gaussianVector ι)
  have hcomp := (abs_sub_le_iff.mp
    (abs_gaussian_wordNative_resolventEvenMoment_rpow_sub_le A₀ hA₀ A hA ζ hζ.ne'
      (by omega : 0 < 2*q))).2
  have hroot := integral_resolventEvenMoment_rpow_inv_le_lpNorm_specNorm
    (gaussianVector ι) X hXm.aemeasurable (Filter.Eventually.of_forall hX) hζ.ne'
      (by omega : 0 < 2*q)
  have hfree := norm_resolvent_wordNativeMatrixLinearCombination_le_evenMoment_log_order
    q hq hlog hA₀ A hA hζ hspec
  have hexp : 1 / (((2*(2*q) : ℕ)) : ℝ) = 1 / (4*q : ℝ) := by push_cast; ring
  rw [hexp] at hcomp hroot
  have hbound : ‖resolvent (wordNativeMatrixLinearCombination A₀ A) ζ‖ ≤ C*(L+B+E) := by
    refine hfree.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    dsimp only [X, L, B, E] at *
    linarith
  have henergy (u : d → ℂ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ (Real.sqrt (bilinearSquareMass A Finset.univ))^2 := by
    rw [Real.sq_sqrt (bilinearSquareMass_nonneg _ _)]
    exact sum_re_quadForm_sq_le_bilinearSquareMass A u hu
  have hmgf0 := hasSubgaussianMGF_specNorm_resolvent_affineSeries_of_quadratic_energy
    A₀ hA₀ A hA (Real.sqrt_nonneg (bilinearSquareMass A Finset.univ)) henergy ζ hζ.ne'
  have hmgf : HasSubgaussianMGF
      (fun x => specNorm (resolvent (X x) ζ) -
        ∫ y, specNorm (resolvent (X y) ζ) ∂gaussianVector ι)
      ⟨c, hc⟩ (gaussianVector ι) := by
    simpa only [Real.sq_sqrt (bilinearSquareMass_nonneg _ _), X, c] using hmgf0
  have hm := measureReal_lt_lpNorm_sub_le_of_centered_hasSubgaussianMGF
    (fun x : ι → ℝ => specNorm_nonneg (resolvent (X x) ζ)) hmgf
      (by omega : 0 < 2*q) ht
  refine le_trans ?_ hm
  apply measureReal_mono _ (by finiteness)
  intro x hx
  change specNorm (resolvent (X x) ζ) + Real.sqrt (4*c*(((2*q : ℕ) : ℝ))) + t < L
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  change C*(specNorm (resolvent (X x) ζ) + Real.sqrt (4*c*(2*q)) + t + B + E) < _ at hx
  by_contra hnot
  have hp := mul_nonneg hC.le (sub_nonneg.mpr (le_of_not_gt hnot))
  nlinarith only [hp, hx, hbound]

end NLAlib
