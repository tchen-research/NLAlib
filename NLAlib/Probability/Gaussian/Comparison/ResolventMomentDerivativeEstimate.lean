import NLAlib.Probability.Gaussian.Comparison.ResolventMomentCubicInterpolation
import NLAlib.Probability.Gaussian.Comparison.ResolventMomentPath
import NLAlib.Probability.Moments.ExpectedResolventMomentTaylor
import NLAlib.Probability.Moments.ThirdCopySquareMass
import NLAlib.ForMathlib.MeasureTheory.FiniteUniformIntegral

/-!
# Actual sharp differential estimate for the resolvent Gram-moment path

The selected index is averaged inside the complex expectation before its
norm is taken. The common original resolvent base and full-array copy laws
then give the coefficient nine, with the actual original square-mass L(2p)
norm. Coordinate-null directions require only their original second moments.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.9.
Prerequisite for independent-sum-spectrum-universality.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)
local notation "C" => (ι × Fin 3) → E
local notation "Q" => (ι × C) × E

omit [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
open scoped Matrix.Norms.L2Operator in
private theorem memLp_original_square_mass
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    {R : ℝ} (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (q : ℝ≥0∞) :
    MemLp (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2)) q (Measure.pi ν) := by
  have hAll : ∀ᵐ x ∂Measure.pi ν, ∀ i, specNorm (L (x i)) ≤ R := by
    rw [ae_all_iff]
    intro i
    have hi := (measurePreserving_eval ν i).hasLaw
    apply ae_of_ae_map (p := fun x : E => specNorm (L x) ≤ R) hi.aemeasurable
    rw [hi.map_eq]
    exact hBound i
  have hc : Continuous (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2)) := by
    simp only [specNorm_eq_norm]
    fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable ((Fintype.card ι : ℝ) * R ^ 2)
  filter_upwards [hAll] with x hx
  simp only [specNorm_eq_norm, norm_norm] at hx ⊢
  calc
    _ ≤ ∑ i, ‖L (x i) ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, R ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖L (x i)‖ ^ 2 := by simpa only [pow_two] using norm_mul_le (L (x i)) (L (x i))
        _ ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
    _ = _ := by simp

open scoped Matrix.Norms.L2Operator in
/-- The genuine real Gram-moment interpolation is differentiable in the
interior, and its actual derivative obeys the sharp common-mass estimate.
The original square-mass L(2p) moment is derived from the actual matrix support
bound. There is no coordinate L3 or assumed derivative/remainder bound.
Zero radius and empty matrix dimensions are included. -/
theorem hasDerivAt_resamplingInterpolation_resolventEvenMoment_and_abs_deriv_le
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun q : ι × C => resamplingTripleOriginal q i),
          (fun q : ι × C => resamplingTripleOriginal q j); resamplingTripleMeasure ν])
    {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (hsmall : 16 * (p : ℝ) * R ≤ |ζ.im|)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let F := resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p)
    let B := lpNorm (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2))
      (2 * (p : ℝ≥0∞)) (Measure.pi ν)
    HasDerivAt F (deriv F t) t ∧
      |deriv F t| ≤ 9 * Real.sqrt t * ((2 * p : ℕ) : ℝ) *
        ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R * B *
          (|ζ.im|⁻¹) ^ 4 * F t ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  let := hγ.isProbabilityMeasure
  dsimp only
  let P₀ := Measure.pi fun k : ι × Fin 3 => ν k.1
  let P := P₀.prod γ
  let Qm := (resamplingTripleMeasure ν).prod γ
  let drop : Q → C × E := fun q => (q.1.2, q.2)
  let μ := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν
  let a := Real.sqrt t
  let b := Real.sqrt (1 - t)
  let x₀ : C × E → E := fun q => resamplingAffinePoint μ a b (∑ j, q.1 (j, 0)) q.2
  let z : Q → Fin 3 → ι → E := fun q s i => q.1.2 (i, s)
  let T : (C × E) → ι → ℂ := fun q i => resolventMomentTaylorKernel A ζ p a
    (x₀ q - a • (q.1 (i, 0) - q.1 (i, 1)))
    (q.1 (i, 0) - q.1 (i, 1)) (q.1 (i, 1) - q.1 (i, 2))
  let K : Q → ℂ := fun q => resolventMomentTaylorKernel A ζ p a
    (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2)
    (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
    (resamplingTripleFirst q.1 - resamplingTripleSecond q.1)
  let F := resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p)
  let B := lpNorm (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2))
    (2 * (p : ℝ≥0∞)) (Measure.pi ν)
  let c : ℝ := ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ)
  let α : ℝ := ((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)
  have ha : 0 ≤ a := Real.sqrt_nonneg t
  have ha1 : a ≤ 1 := by dsimp only [a]; exact Real.sqrt_le_one.mpr ht1.le
  have hdrop : MeasurePreserving drop Qm P := by
    exact (measurePreserving_snd (μ := (PMF.uniformOfFintype ι).toMeasure) (ν := P)).comp
      (measurePreserving_prodAssoc (PMF.uniformOfFintype ι).toMeasure P₀ γ)
  have hx₀m : Measurable x₀ := by
    unfold x₀ resamplingAffinePoint
    fun_prop
  have hzm : Measurable z := by unfold z; fun_prop
  have hAll : ∀ᵐ q ∂Qm, ∀ s i, specNorm (L (z q s i)) ≤ R := by
    rw [ae_all_iff]
    intro s
    have hs := hasLaw_resamplingTriple_prod_full_copy ν γ s
    apply ae_of_ae_map (p := fun x : ι → E => ∀ i, specNorm (L (x i)) ≤ R) hs.aemeasurable
    rw [hs.map_eq, ae_all_iff]
    intro i
    have hi := (measurePreserving_eval ν i).hasLaw
    apply ae_of_ae_map (p := fun x : E => specNorm (L x) ≤ R) hi.aemeasurable
    rw [hi.map_eq]
    exact hBound i
  have hOriginalMass := memLp_original_square_mass ν hBound (2 * (p : ℝ≥0∞))
  have hq : (1 : ℝ≥0∞) ≤ 2 * (p : ℝ≥0∞) := by
    have hp' : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast (Nat.succ_le_iff.mpr hp)
    calc
      1 ≤ (p : ℝ≥0∞) := hp'
      _ ≤ 2 * (p : ℝ≥0∞) := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hMass := memLp_and_lpNorm_two_mul_sum_resamplingTriple_prod_copy_sq_le
    ν γ L hq hOriginalMass
  have hExpected := integrable_and_norm_integral_sum_resolventMomentTaylorKernel_first_copy_le
    Qm A hA ζ hζ hp (x₀ ∘ drop) (hx₀m.comp hdrop.measurable).aemeasurable
    z hzm.aemeasurable hR hAll ha ha1 hsmall hMass.1
  have hK (q : Q) : K q = T (drop q) q.1.1 := by
    have hY : resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2 =
        x₀ (drop q) - a • (q.1.2 (q.1.1, 0) - q.1.2 (q.1.1, 1)) := by
      have hDiff := resamplingTriple_difference q.1
      dsimp only [x₀, drop, resamplingTripleOriginal, resamplingAffinePoint] at hDiff ⊢
      rw [← hDiff]
      simp only [smul_sub]
      abel
    simp only [K, T, hY, drop, resamplingTriple_difference, resamplingTriple_first_sub_second]
  obtain ⟨hKi, hd⟩ := hasDerivAt_resamplingInterpolation_normalizedTrace_mixed_eq_cubicKernel
    ν hν γ hγ hmean hcov hR hBound A hA ζ hζ p ht ht1
  change Integrable K Qm at hKi
  have hAverage : (Fintype.card ι : ℝ) • (∫ q, K q ∂Qm) =
      ∫ q : C × E, ∑ i, T q i ∂P := by
    have hEq : K = fun q => T (drop q) q.1.1 := funext hK
    rw [hEq] at hKi ⊢
    exact card_smul_integral_uniform_prod_prod P₀ γ (fun i x z => T (x, z) i) hKi
  have hDropIntegral : (∫ q : Q, ∑ i, T (drop q) i ∂Qm) =
      ∫ q : C × E, ∑ i, T q i ∂P := by
    calc
      _ = ∫ q : ι × (C × E), ∑ i, T q.2 i
          ∂(PMF.uniformOfFintype ι).toMeasure.prod P :=
        (measurePreserving_prodAssoc (PMF.uniformOfFintype ι).toMeasure P₀ γ).integral_comp'
          (fun q : ι × (C × E) => ∑ i, T q.2 i)
      _ = _ := by
        simpa only [probReal_univ, one_smul] using
          (integral_fun_snd (μ := (PMF.uniformOfFintype ι).toMeasure) (ν := P)
            (fun q : C × E => ∑ i, T q i))
  have hF : (∫ q : Q, resolventEvenMoment (A + L (x₀ (drop q))) ζ p ∂Qm) = F t := rfl
  have hFnn : 0 ≤ F t := by
    dsimp only [F, resamplingInterpolation]
    exact integral_nonneg fun q => resolventEvenMoment_nonneg _ ζ hp
  have hBudget : ‖∫ q : Q, ∑ i, T (drop q) i ∂Qm‖ ≤
      c * 3 * (2 * R) * (|ζ.im|⁻¹) ^ 4 * (6 * B) * F t ^ α := by
    have he := hExpected.2
    change ‖∫ q : Q, ∑ i, T (drop q) i ∂Qm‖ ≤
      c * 3 * (2 * R) * (|ζ.im|⁻¹) ^ 4 * _ *
        (∫ q : Q, resolventEvenMoment (A + L (x₀ (drop q))) ζ p ∂Qm) ^ α at he
    rw [hF] at he
    refine he.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMass.2 (by dsimp only [c]; positivity))
      (Real.rpow_nonneg hFnn α)
  let d : ℂ := (a / 4) • ∫ q : Q, ∑ i, T (drop q) i ∂Qm
  have hDerivative : HasDerivAt
      (resamplingInterpolation ν γ (fun x => normalizedTrace
        (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p))) d t := by
    apply hd.congr_deriv
    change ((Fintype.card ι : ℝ) * a / 4) • (∫ q, K q ∂Qm) = d
    dsimp only [d]
    have heq : (Fintype.card ι : ℝ) • (∫ q, K q ∂Qm) =
        ∫ q : Q, ∑ i, T (drop q) i ∂Qm := hAverage.trans hDropIntegral.symm
    calc
      _ = (a / 4) • ((Fintype.card ι : ℝ) • (∫ q, K q ∂Qm)) := by
        rw [smul_smul]
        congr 1
        ring
      _ = _ := by rw [heq]
  have hReal : HasDerivAt F d.re t := by
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hDerivative
    have hEq : F = fun s => (resamplingInterpolation ν γ (fun x => normalizedTrace
        (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) s).re := by
      funext s
      exact resamplingInterpolation_resolventEvenMoment_eq_re ν γ A hA hζ p s
    rw [hEq]
    exact hr
  refine ⟨hReal.congr_deriv hReal.deriv.symm, ?_⟩
  rw [hReal.deriv]
  calc
    |d.re| ≤ ‖d‖ := Complex.abs_re_le_norm d
    _ = (a / 4) * ‖∫ q : Q, ∑ i, T (drop q) i ∂Qm‖ := by
      dsimp only [d]
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (a / 4) * (c * 3 * (2 * R) * (|ζ.im|⁻¹) ^ 4 * (6 * B) * F t ^ α) :=
      mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = _ := by dsimp only [a, c, α]; ring

end NLAlib
