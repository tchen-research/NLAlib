import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventNormMomentUniversality
import NLAlib.Probability.Moments.BilinearSumCovariance

/-!
# Fixed-parameter resolvent comparison under any coupling

Actual marginal laws and Gaussian concentration yield a simultaneous
comparison without an independence assumption between the original sum and
its Gaussian proxy. Source: arXiv:2201.05142v3, Lemma 7.3.
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
/-- The actual resolvent of an independent matrix sum is bounded by the
realized full-covariance Gaussian resolvent outside an explicit probability
bound. The two random objects may have any coupling. Empty dimensions and
zero budgets are retained.
Source: arXiv:2201.05142v3, Lemma 7.3, with integer moment order and the
exact dimension factor displayed.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_resolvent_sum_gt_gaussian_le_of_hasLaw
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
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ ((Z - ∫ H, H ∂ρ) *ᵥ w)‖ ^ 2 ∂ρ) ≤ σ ^ 2)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω |
      Real.exp 1 * (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        (specNorm (resolvent (G ω) ζ) +
          Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) +
          Real.sqrt (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * t +
          4096 * ((p : ℝ) ^ 2 * R * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
            (p : ℝ) ^ 3 * R ^ 3) / |ζ.im| ^ 4) <
        specNorm (resolvent (A₀ + ∑ i, S ω i) ζ)} ≤
      Real.exp (-((2*p : ℕ) : ℝ)) + 2 * Real.exp (-t ^ 2 / 2) := by
  have := hS.isProbabilityMeasure
  let F (x : ι → M) := specNorm (resolvent (A₀ + ∑ i, x i) ζ)
  let H (A : M) := specNorm (resolvent A ζ)
  let C := Real.exp 1 * (Fintype.card n : ℝ) ^ (1 / ((2*p : ℕ) : ℝ))
  let m := ∫ A, H A ∂ρ
  let c := σ ^ 2 * (|ζ.im|⁻¹) ^ 4
  let a := Real.sqrt (4*c*p)
  let b := Real.sqrt c * t
  let e := 4096 * ((p : ℝ)^2*R*specNorm (∑ i, ∫ A : M, A^2 ∂ν i) +
    (p : ℝ)^3*R^3) / |ζ.im|^4
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have htailX : μ.real {ω | C*(m+a+e) < F (S ω)} ≤ Real.exp (-((2*p : ℕ) : ℝ)) := by
    rw [hS.measureReal_eq (p := fun x => C*(m+a+e) < F x)]
    · exact measureReal_specNorm_resolvent_pi_gt_gaussian_mean_le
        ν hHerm hR hBound ρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog hσ hbilinear
    · apply measurableSet_lt measurable_const
      change Measurable (fun x : ι → M => ‖resolvent (A₀ + ∑ i, x i) ζ‖)
      exact ((measurable_matrix_resolvent ζ).comp (by fun_prop)).norm
  have hsg : HasSubgaussianMGF (fun ω => H (G ω)-m) ⟨c, by positivity⟩ μ := by
    have hg : HasSubgaussianMGF (fun A => H A-m) ⟨c, by positivity⟩ (μ.map G) := by
      rw [hG.map_eq]
      exact hasSubgaussianMGF_specNorm_resolvent_gaussian_of_centered_bilinear_moment
        ρ hρHerm hσ hbilinear ζ hζ
    simpa only [Function.comp_def] using HasSubgaussianMGF.of_map hG.aemeasurable hg
  have htailG : μ.real {ω | b < |H (G ω)-m|} ≤ 2*Real.exp (-t^2/2) :=
    measureReal_sqrt_mul_lt_abs_le_of_hasSubgaussianMGF hsg ht
  have hs : {ω | C*(H (G ω)+a+b+e) < F (S ω)} ⊆
      {ω | C*(m+a+e) < F (S ω)} ∪ {ω | b < |H (G ω)-m|} := by
    intro ω hω
    by_cases hx : C*(m+a+e) < F (S ω)
    · exact Or.inl hx
    · right
      by_contra hg
      change ¬ b < |H (G ω)-m| at hg
      have hgm : m ≤ H (G ω)+b := by
        have hab := neg_le_abs (H (G ω)-m)
        have hh := le_of_not_gt hg
        linarith
      have hmul : C*(m+a+e) ≤ C*(H (G ω)+a+b+e) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      change C*(H (G ω)+a+b+e) < F (S ω) at hω
      exact (not_lt.mpr ((le_of_not_gt hx).trans hmul)) hω
  exact (measureReal_mono (μ := μ) hs).trans
    ((measureReal_union_le _ _).trans (add_le_add htailX htailG))


open scoped Matrix.Norms.L2Operator in
/-- The fixed-parameter comparison with an actual full-covariance Gaussian
proxy uses only the original independent increments' bilinear variance
budget. The proxy budget is derived, with arbitrary mean and coupling.
Source: arXiv:2201.05142v3, Lemma 7.3, integer moment form.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_resolvent_sum_gt_gaussian_le_of_bilinear_moments
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
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hmeanν : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∑ i, ∫ A : M, ‖star v ⬝ᵥ (A *ᵥ w)‖ ^ 2 ∂ν i) ≤ σ ^ 2)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω |
      Real.exp 1 * (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        (specNorm (resolvent (G ω) ζ) +
          Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) +
          Real.sqrt (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * t +
          4096 * ((p : ℝ) ^ 2 * R * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
            (p : ℝ) ^ 3 * R ^ 3) / |ζ.im| ^ 4) <
        specNorm (resolvent (A₀ + ∑ i, S ω i) ζ)} ≤
      Real.exp (-((2*p : ℕ) : ℝ)) + 2 * Real.exp (-t ^ 2 / 2) := by
  have hproxy : ∀ v w : n → ℂ,
      ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
        (∫ A : M, ‖star v ⬝ᵥ ((A-∫ B, B ∂ρ) *ᵥ w)‖ ^ 2 ∂ρ) ≤ σ ^ 2 := by
    intro v w hv hw
    have he := integral_norm_sq_centered_bilinear_eq_sum_of_covariance_eq
      ν (fun _ (A : M) => A) (fun _ => measurable_id) hBound hmeanν
      ρ IsGaussian.memLp_two_id hcov v w
    exact he.trans_le (hbilinear v w hv hw)
  exact measureReal_specNorm_resolvent_sum_gt_gaussian_le_of_hasLaw
    ν hHerm hR hBound ρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog hσ hproxy μ S G hS hG ht

end NLAlib
