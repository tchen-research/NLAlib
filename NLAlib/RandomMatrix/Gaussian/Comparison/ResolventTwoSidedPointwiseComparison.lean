import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventNormMomentUniversality
import NLAlib.Probability.Concentration.Matrix.IndependentResolventMoments
import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventPointwiseComparison
import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventReversePointwiseComparison
import NLAlib.ForMathlib.Analysis.ResolventMomentScale
import NLAlib.ForMathlib.Analysis.LogarithmicMomentFactor
import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventError

/-!
# Two-sided actual resolvent comparisons at a common error budget

Actual even-moment comparison, non-Gaussian concentration and Markov's
inequality control the realized Gaussian resolvent by the original sum.
Both random objects may have any coupling with the specified marginal laws.
Source: arXiv:2201.05142v3, Lemma 7.5.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- Both directions of the actual fixed-parameter resolvent comparison use
one deterministic error budget independent of the real spectral parameter.
The original independent sum and Gaussian proxy may have any coupling.
No moment, MGF or concentration conclusion is supplied as an assumption.
Source: arXiv:2201.05142v3, Lemmas 7.3 and 7.5, integer-moment version.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_two_sided_resolvent_comparison_failure_le
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
  (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
  {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
  (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
  (A₀ : M) (hA₀ : A₀.IsHermitian)
  (hmean : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
  (hcov : ∀ a b : J,
    cov[(fun A : M => matrixRealCoordinates A a),
      (fun A : M => matrixRealCoordinates A b); ρ] =
    cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
      (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
  (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
  (hlog : Real.log (Fintype.card n) ≤ (p : ℝ))
    {s : ℝ} (hs : 0 ≤ s)
    (hmeanν : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hbilinear : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ A : M, ‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ s^2)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ)
 :
    μ.real {ω |
      9*specNorm (resolvent (G ω) ζ)+independentSumResolventError ν R s |ζ.im| p <
        specNorm (resolvent (A₀+∑ i, S ω i) ζ) ∨
      9*specNorm (resolvent (A₀+∑ i, S ω i) ζ)+independentSumResolventError ν R s |ζ.im| p <
        specNorm (resolvent (G ω) ζ)} ≤
        6*Real.exp (-(p : ℝ)) := by
  have := hS.isProbabilityMeasure
  let F (x : ι → M) := specNorm (resolvent (A₀+∑ i, x i) ζ)
  let H (A : M) := specNorm (resolvent A ζ)
  let C := Real.exp 1*(Fintype.card n : ℝ)^(1/((2*p : ℕ) : ℝ))
  let B := (2/|ζ.im|^4)*(8*s^2+64*R*
    ∫ x : ι → M, specNorm (∑ i, x i) ∂Measure.pi ν) +
    (32*R^2/|ζ.im|^6)*((Real.exp 1-1)*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
      R^2*Real.log (Fintype.card n))
  let c := Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))
  let aX := 4*Real.sqrt (12*B*p)+8*c*p
  let bX := Real.sqrt (24*B*p)+c*p
  let U := s*Real.sqrt (p : ℝ)/|ζ.im|^2
  let V := 4096*((p : ℝ)^2*R*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
    (p : ℝ)^3*R^3)/|ζ.im|^4
  let a := Real.sqrt (4*(s^2*(|ζ.im|⁻¹)^4)*p)
  let b := Real.sqrt (s^2*(|ζ.im|⁻¹)^4)*Real.sqrt (2*(p : ℝ))
  let K := aX+bX+V+4*U
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hV : 0 ≤ V := by
    have hQ := specNorm_nonneg (∑ i, ∫ A : M, A^2 ∂ν i)
    dsimp [V]
    positivity
  have haX : 0 ≤ aX := by dsimp [aX,c]; positivity
  have hbX : 0 ≤ bX := by dsimp [bX,c]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hfl : a+b ≤ 4*U := by
    simpa only [a,b,U,mul_div_assoc,mul_assoc] using
      Real.gaussian_resolvent_moment_fluctuations_le hs hpR |ζ.im|
  have hC : C ≤ 9 := by
    dsimp [C]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    exact Real.exp_one_mul_rpow_inv_two_mul_le_nine_of_log_le
      (Nat.cast_nonneg _) (by exact_mod_cast hp) hlog
  have hbilinear' : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖=1 → ‖WithLp.toLp 2 w‖=1 →
      (∑ i, ∫ A : M, ‖star v ⬝ᵥ (A *ᵥ w)‖^2 ∂ν i) ≤ s^2 := by
    intro v w hv hw
    simpa only [WithLp.ofLp_toLp] using
      hbilinear (WithLp.toLp 2 v) (WithLp.toLp 2 w) hv.le hw.le
  have hforward := measureReal_specNorm_resolvent_sum_gt_gaussian_le_of_bilinear_moments
    ν hHerm hR hBound ρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog hs
      hmeanν hbilinear' μ S G hS hG (Real.sqrt_nonneg (2*(p : ℝ)))
  change μ.real {ω | C*(H (G ω)+a+b+V)<F (S ω)} ≤
    Real.exp (-((2*p : ℕ) : ℝ))+2*Real.exp (-(Real.sqrt (2*(p : ℝ)))^2/2) at hforward
  have hreverse := measureReal_specNorm_resolvent_gaussian_gt_sum_le_of_bilinear_moments
    ν hHerm hR hBound ρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog
      hmeanν hbilinear μ S G hS hG hpR
  change μ.real {ω | C*(F (S ω)+aX+bX+V)<H (G ω)} ≤
    Real.exp (-((2*p : ℕ) : ℝ))+2*Real.exp (-(p : ℝ)) at hreverse
  have hprob : Real.exp (-((2*p : ℕ) : ℝ))+2*Real.exp (-(p : ℝ)) ≤
      3*Real.exp (-(p : ℝ)) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    have hh := Real.exp_le_exp.mpr (show -(2*(p : ℝ)) ≤ -(p : ℝ) by linarith)
    linarith only [hh]
  have hprobF : Real.exp (-((2*p : ℕ) : ℝ))+2*Real.exp (-(Real.sqrt (2*(p : ℝ)))^2/2) ≤
      3*Real.exp (-(p : ℝ)) := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2*(p : ℝ))]
    simpa only [show -(2*(p : ℝ))/2 = -(p : ℝ) by ring] using hprob
  have hthresholdF (ω : Ω) : C*(H (G ω)+a+b+V) ≤ 9*H (G ω)+9*K := by
    have hH : 0 ≤ H (G ω) := specNorm_nonneg _
    have hi : 0 ≤ H (G ω)+a+b+V := by dsimp [a,b]; positivity
    have hh := mul_le_mul_of_nonneg_right hC hi
    dsimp only [K]
    linear_combination hh+9*hfl+9*haX+9*hbX
  have hthresholdR (ω : Ω) : C*(F (S ω)+aX+bX+V) ≤ 9*F (S ω)+9*K := by
    have hF : 0 ≤ F (S ω) := specNorm_nonneg _
    have hi : 0 ≤ F (S ω)+aX+bX+V := add_nonneg (add_nonneg (add_nonneg hF haX) hbX) hV
    have hh := mul_le_mul_of_nonneg_right hC hi
    dsimp only [K]
    linear_combination hh+36*hU
  have hsub : {ω | 9*H (G ω)+9*K<F (S ω) ∨ 9*F (S ω)+9*K<H (G ω)} ⊆
      {ω | C*(H (G ω)+a+b+V)<F (S ω)} ∪
        {ω | C*(F (S ω)+aX+bX+V)<H (G ω)} := by
    intro ω hω
    rcases hω with hω | hω
    · exact Or.inl (lt_of_le_of_lt (hthresholdF ω) hω)
    · exact Or.inr (lt_of_le_of_lt (hthresholdR ω) hω)
  have htotal := (measureReal_mono (μ := μ) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add (hforward.trans hprobF) (hreverse.trans hprob)))
  rw [show 3*Real.exp (-(p : ℝ))+3*Real.exp (-(p : ℝ)) =
    6*Real.exp (-(p : ℝ)) by ring] at htotal
  simpa only [independentSumResolventError,K,aX,bX,B,c,U,V,F,H,
    add_assoc,mul_div_assoc,mul_assoc] using htotal

end NLAlib
