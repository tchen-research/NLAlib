import NLAlib.RandomMatrix.Gaussian.Comparison.SpectralGridComparison
import NLAlib.RandomMatrix.Gaussian.Comparison.SpectralScale
import NLAlib.RandomMatrix.Gaussian.Comparison.SpectralDegenerate

/-!
# Actual independent-sum spectral universality at every real tail parameter

The bound uses the source square-root, mixed fractional-power and linear
scale. The original sum and Gaussian proxy may have any coupling; only
their actual means and full real/imaginary entry covariances are matched.
Source: arXiv:2201.05142v3, Theorem 2.6.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n)⊕(n×n)

open scoped Matrix.Norms.L2Operator in
/-- The genuine independent-sum Hausdorff spectral comparison at the source
scale, for every nonnegative real tail parameter. The variance parameters
are any upper budgets on the actual marginal square expectation and the
actual unit-ball bilinear second moments. Zero radius and singular Gaussian
covariance are included, and the mean and coupling are arbitrary.
Source: arXiv:2201.05142v3, Theorem 2.6, variance-budget version.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_hausdorffDist_spectra_gt_spectralScale_le
    (ν : ι → Measure M) [∀ i,IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i,∀ᵐ A ∂ν i,A.IsHermitian)
    {R s σ : ℝ} (hR : 0≤R) (hs : 0≤s) (hσ : 0≤σ)
    (hBound : ∀ i,∀ᵐ A ∂ν i,specNorm A≤R)
    (hmeanν : ∀ i,∫ A : M,A ∂ν i=0)
    (hvariance : specNorm (∑ i,∫ A : M,A^2 ∂ν i)≤σ^2)
    (hbilinear : ∀ a b : EuclideanSpace ℂ n,‖a‖≤1 → ‖b‖≤1 →
      (∑ i,∫ A : M,‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i)≤s^2)
    (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ,A.IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian)
    (hmean : (∫ A : M,A ∂ρ)=A₀+∫ x : ι → M,∑ i,x i ∂Measure.pi ν)
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b);ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i,x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i,x i) b);Measure.pi ν])
    (hd : 2≤Fintype.card n) {t : ℝ} (ht : 0≤t)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ) :
    μ.real {ω | 80000000*independentSumSpectralScale R s σ t <
      Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))} ≤
        (Fintype.card n : ℝ)*Real.exp (-t) := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have := hS.isProbabilityMeasure
  have hdR : (2 : ℝ)≤Fintype.card n := by exact_mod_cast hd
  have hdpos : (0 : ℝ)<Fintype.card n := by linarith only [hdR]
  by_cases hsmall : t<Real.log (Fintype.card n)
  · apply measureReal_le_one.trans
    calc
      (1 : ℝ)=Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (Real.log (Fintype.card n)-t) :=
        Real.exp_le_exp.mpr (by linarith only [hsmall])
      _ = _ := by rw [Real.exp_sub,Real.exp_log hdpos,Real.exp_neg]; rfl
  have hlogt : Real.log (Fintype.card n)≤t := le_of_not_gt hsmall
  have hD := independentSumSpectralScale_nonneg (σ:=σ) hR hs ht
  by_cases hzero : R=0
  · have hconst := ae_eq_constant_sum_and_gaussian_of_zero_radius
      ν (by simpa only [hzero] using hBound) ρ A₀ hmean hcov μ S G hS hG
    have hnull : ∀ᵐ ω ∂μ,¬(80000000*independentSumSpectralScale R s σ t <
        Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))) := by
      filter_upwards [hconst] with ω hω
      rw [hω.1,hω.2,Metric.hausdorffDist_self_zero]
      exact not_lt_of_ge (mul_nonneg (by norm_num) hD)
    have hm : μ {ω | 80000000*independentSumSpectralScale R s σ t <
        Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))}=0 := by
      simpa only [not_not] using (ae_iff.mp hnull)
    rw [(measureReal_eq_zero_iff).mpr hm]
    positivity
  have hscale : 0<R+s := add_pos_of_pos_of_nonneg (lt_of_le_of_ne hR (Ne.symm hzero)) hs
  have hl2 : Real.log 2≤t := (Real.log_le_log (by norm_num) hdR).trans hlogt
  have hhalf : (1/2 : ℝ)≤t := by linarith only [hl2,Real.log_two_gt_d9]
  let p : ℕ := ⌈20*t⌉₊
  have hp : 0<p := Nat.one_le_ceil_iff.mpr (by linarith only [hhalf])
  have htp : 20*t≤(p : ℝ) := Nat.le_ceil _
  have hple : (p : ℝ)≤22*t := by
    have hh : (p : ℝ)<20*t+1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [hh,hhalf]
  have hlog : Real.log (Fintype.card n)≤(p : ℝ) := by linarith only [hlogt,htp,ht]
  have hbudget := sqrt_add_linear_and_mixed_variance_le_twenty_two_spectralScale
    (σ:=σ) hR hs ht (Nat.cast_nonneg p) hple
  have hraw := measureReal_hausdorffDist_spectra_gt_le_of_source_scale ν hHerm hR hs hσ
    hscale hBound hmeanν hvariance hbilinear ρ hρHerm A₀ hA₀ hmean hcov hd hp hlog
      hbudget.1 hbudget.2 μ S G hS hG
  have hthreshold : 3600000*(22*independentSumSpectralScale R s σ t)≤
      80000000*independentSumSpectralScale R s σ t := by linarith only [hD]
  apply (measureReal_mono (μ:=μ) (show
    {ω | 80000000*independentSumSpectralScale R s σ t <
      Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))} ⊆
    {ω | 3600000*(22*independentSumSpectralScale R s σ t) <
      Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))}
      from fun _ hω => lt_of_le_of_lt hthreshold hω)).trans (hraw.trans ?_)
  exact Real.sixty_mul_sq_mul_exp_neg_le_of_log_le hdR hlogt htp

end NLAlib
