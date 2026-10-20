import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventNormMomentUniversality
import NLAlib.Probability.Concentration.Matrix.IndependentResolventMoments
import NLAlib.Probability.Concentration.Matrix.IndependentResolventConcentration

/-!
# Reverse fixed-parameter resolvent comparison

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
/-- The realized Gaussian proxy resolvent is controlled by the original
independent sum outside an explicit probability bound. Its fluctuation budget
is derived from the original increments, with no supplied concentration or
moment estimate. Zero radius and empty matrix shapes are included.
Source: arXiv:2201.05142v3, the fixed-integer-moment step of Lemma 7.5.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_resolvent_gaussian_gt_sum_le_of_bilinear_moments
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
    {v : ℝ}
    (hmeanν : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hbilinear : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ A : M, ‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ)
    {t : ℝ} (ht : 0 ≤ t) :
    let B := (2/|ζ.im|^4)*(8*v+64*R*
      ∫ x : ι → M, specNorm (∑ i, x i) ∂Measure.pi ν) +
      (32*R^2/|ζ.im|^6)*((Real.exp 1-1)*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
        R^2*Real.log (Fintype.card n))
    let c := Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))
    μ.real {ω |
      Real.exp 1 * (Fintype.card n : ℝ) ^ (1 / ((2*p : ℕ) : ℝ)) *
        (specNorm (resolvent (A₀ + ∑ i, S ω i) ζ) +
          (4*Real.sqrt (12*B*p)+8*c*p) + (Real.sqrt (24*B*t)+c*t) +
          4096*((p : ℝ)^2*R*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
            (p : ℝ)^3*R^3)/|ζ.im|^4) < specNorm (resolvent (G ω) ζ)} ≤
      Real.exp (-((2*p : ℕ) : ℝ)) + 2*Real.exp (-t) := by
  have := hS.isProbabilityMeasure
  let F (x : ι → M) := specNorm (resolvent (A₀ + ∑ i, x i) ζ)
  let H (A : M) := specNorm (resolvent A ζ)
  let C := Real.exp 1 * (Fintype.card n : ℝ) ^ (1 / ((2*p : ℕ) : ℝ))
  let m := ∫ x, F x ∂Measure.pi ν
  let B := (2/|ζ.im|^4)*(8*v+64*R*
    ∫ x : ι → M, specNorm (∑ i, x i) ∂Measure.pi ν) +
    (32*R^2/|ζ.im|^6)*((Real.exp 1-1)*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
      R^2*Real.log (Fintype.card n))
  let c := Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))
  let a := 4*Real.sqrt (12*B*p)+8*c*p
  let b := Real.sqrt (24*B*t)+c*t
  let e := 4096*((p : ℝ)^2*R*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
    (p : ℝ)^3*R^3)/|ζ.im|^4
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hLp := lpNorm_specNorm_resolvent_gaussian_le_pi
    ν hHerm hR hBound ρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog
  have hXmom := lpNorm_specNorm_resolvent_pi_le_integral_add_of_bilinear_moments
    ν A₀ hA₀ (fun _ (A : M) => A) (fun _ => measurable_id) hR hHerm hBound
      hmeanν hbilinear ζ hζ hp
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hXmom
  have htailG : μ.real {ω | C*(m+a+e) < H (G ω)} ≤ Real.exp (-((2*p : ℕ) : ℝ)) := by
    rw [hG.measureReal_eq (p := fun A => C*(m+a+e) < H A)]
    · have hmem := memLp_specNorm_resolvent ρ id aemeasurable_id hρHerm hζ
        ((2*p : ℕ) : ℝ≥0∞)
      have hmarkov := measureReal_lt_exp_mul_lpNorm_le_exp_neg
        (Nat.mul_pos (by decide : 0 < 2) hp) hmem
      apply (measureReal_mono (μ := ρ) (fun A hA => ?_)).trans hmarkov
      change Real.exp 1 * lpNorm H ((2*p : ℕ) : ℝ≥0∞) ρ < ‖H A‖
      rw [Real.norm_of_nonneg (specNorm_nonneg _)]
      have htotal := hLp.trans (mul_le_mul_of_nonneg_left
        (add_le_add hXmom le_rfl) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have he := mul_le_mul_of_nonneg_left htotal (Real.exp_pos 1).le
      simp only [Nat.cast_mul, Nat.cast_ofNat] at *
      exact lt_of_le_of_lt (by simpa only [mul_assoc, add_assoc, F, H, C, m, a, B, c, e,
        Nat.cast_mul, Nat.cast_ofNat] using he) hA
    · apply measurableSet_lt measurable_const
      change Measurable (fun A : M => ‖resolvent A ζ‖)
      exact (measurable_matrix_resolvent ζ).norm
  have htailX : μ.real {ω | b < |F (S ω)-m|} ≤ 2*Real.exp (-t) := by
    rw [hS.measureReal_eq (p := fun x => b < |F x-m|)]
    · exact measureReal_gt_abs_centered_specNorm_resolvent_pi_le_of_bilinear_moments
        ν A₀ hA₀ (fun _ (A : M) => A) (fun _ => measurable_id) hR hHerm hBound
          hmeanν hbilinear ζ hζ ht
    · apply measurableSet_lt measurable_const
      apply Measurable.abs
      apply Measurable.sub _ measurable_const
      change Measurable (fun x : ι → M => ‖resolvent (A₀ + ∑ i, x i) ζ‖)
      exact ((measurable_matrix_resolvent ζ).comp (by fun_prop)).norm
  have hs : {ω | C*(F (S ω)+a+b+e) < H (G ω)} ⊆
      {ω | C*(m+a+e) < H (G ω)} ∪ {ω | b < |F (S ω)-m|} := by
    intro ω hω
    by_cases hg : C*(m+a+e) < H (G ω)
    · exact Or.inl hg
    · right
      by_contra hx
      change ¬ b < |F (S ω)-m| at hx
      have hxm : m ≤ F (S ω)+b := by
        have hab := neg_le_abs (F (S ω)-m)
        have hh := le_of_not_gt hx
        linarith
      have hmul : C*(m+a+e) ≤ C*(F (S ω)+a+b+e) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      change C*(F (S ω)+a+b+e) < H (G ω) at hω
      exact (not_lt.mpr ((le_of_not_gt hg).trans hmul)) hω
  exact (measureReal_mono (μ := μ) hs).trans
    ((measureReal_union_le _ _).trans (add_le_add htailG htailX))

end NLAlib
