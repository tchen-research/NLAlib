import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFixedHeight
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeLogarithmicScale
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianSpectralDistance
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeZeroParameter

/-! # Actual Gaussian/free spectral distance at the source growth scale

The positive-variance theorem combines a derived fixed-confidence comparison
with actual Gaussian concentration. The weak and covariance parameters retain
the original coefficient normalization.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]

open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian series and native free affine model satisfy the
source Hausdorff tail and expectation estimates at the geometric
variance-covariance scale, for positive actual weak variance. The constant
is explicit and independent of mean, dimension and coefficient family.
Source: arXiv:2406.11453v2, Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem gaussian_free_hausdorffDist_le_with_probability_and_mean_of_pos
    (hd : 2 ≤ Fintype.card d) (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hmass : 0 < bilinearSquareMass A Finset.univ) :
    let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
    let s := Real.sqrt (bilinearSquareMass A Finset.univ)
    let E := ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
    let H := fun x : ι → ℝ => Metric.hausdorffDist
      (spectrum ℝ (A₀+∑ i,x i•A i)) (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A))
    (∫ x : ι → ℝ, H x ∂gaussianVector ι) ≤ (100000000000000000000 : ℝ)*E ∧
      ∀ t : ℝ, 0 ≤ t → (gaussianVector ι).real
        {x | (100000000000000000000 : ℝ)*E+100000000000000000000*s*t < H x} ≤ Real.exp (-t^2) := by
  classical
  dsimp only
  let q : ℕ := ⌈10*Real.log (Fintype.card d : ℝ)+100⌉₊
  obtain ⟨hq,hlog,hqupper,hfailure⟩ := gaussian_free_logarithmic_order_budgets hd
  change 0 < q at hq
  change Real.log (Fintype.card d : ℝ) ≤ q at hlog
  change (q : ℝ) ≤ 212*Real.log (Fintype.card d : ℝ) at hqupper
  change 1/(16*(q : ℝ))+27*(Fintype.card d : ℝ)^2*Real.exp (-(q : ℝ)) ≤ 1/2 at hfailure
  let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
  let s := Real.sqrt (bilinearSquareMass A Finset.univ)
  let Δ := ξ*(q : ℝ)^(3/4 : ℝ)
  let E := ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
  let S := spectrum ℝ (wordNativeMatrixLinearCombination A₀ A)
  let H := fun x : ι → ℝ => Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,x i•A i)) S
  have hξ : 0 ≤ ξ := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hspos : 0 < s := Real.sqrt_pos.mpr hmass
  have hweak0 := sqrt_bilinearSquareMass_le_sqrt_variance_covariance A hA
  have hvariance0 := sqrt_variance_div_card_le_sqrt_covariance A hA
  have hbudgets := gaussian_free_delta_budgets hq (Fintype.card_pos (α := d))
    (specNorm_nonneg (coefficientVariance A)) (specNorm_nonneg (coefficientCovariance A))
      hs hweak0 hvariance0
  dsimp only at hbudgets
  obtain ⟨hweak,hvariance,hbudget,hΔpos⟩ := hbudgets
  have hΔ : 0 < Δ := hΔpos hspos
  have hp := measureReal_hausdorffDist_gaussian_wordNative_gt_fixed_height A₀ hA₀ A hA
    hmass hq hlog hΔ hweak hvariance hbudget.le
  have hbad : (gaussianVector ι).real {x | (20000000000000000 : ℝ)*Δ < H x} ≤ 1/2 :=
    hp.trans hfailure
  have hXm : Measurable (fun x : ι → ℝ => A₀+∑ i,x i•A i) := by fun_prop
  have hHerm (x : ι → ℝ) : (A₀+∑ i,x i•A i).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hHm : AEMeasurable H (gaussianVector ι) :=
    aemeasurable_hausdorffDist_spectrum hXm.aemeasurable (Filter.Eventually.of_forall hHerm) S
  have hcompl := probReal_compl_eq_one_sub₀ (hHm.nullMeasurableSet_preimage (s := Set.Ioi (20000000000000000*Δ)) measurableSet_Ioi)
  have hhalf : (1/2 : ℝ) ≤ (gaussianVector ι).real {x | H x ≤ 20000000000000000*Δ} := by
    have he : (H ⁻¹' Set.Ioi (20000000000000000*Δ))ᶜ = {x | H x ≤ 20000000000000000*Δ} := by
      ext x
      simp only [Set.mem_compl_iff,Set.mem_preimage,Set.mem_Ioi,Set.mem_ofPred_eq,not_lt]
    rw [he] at hcompl
    change (gaussianVector ι).real {x | H x ≤ 20000000000000000*Δ} =
      1-(gaussianVector ι).real {x | 20000000000000000*Δ < H x} at hcompl
    linarith only [hcompl,hbad]
  have hmean := integral_hausdorffDist_spectrum_affineSeries_le_of_half_measure
    A₀ hA₀ A hA S hmass hhalf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp1 : 1 ≤ (q : ℝ)^(3/4 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hsΔ : s ≤ Δ := by
    have hx := mul_le_mul_of_nonneg_left hqp1 hξ
    dsimp only [Δ]
    nlinarith only [hweak0,hx]
  have hlogpos : 0 ≤ Real.log (Fintype.card d : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card d))
  have hpower : (q : ℝ)^(3/4 : ℝ) ≤ 212*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ) := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg q) hqupper (by norm_num : (0 : ℝ) ≤ 3/4)
    rw [Real.mul_rpow (by norm_num) hlogpos] at hh
    have h212 : (212 : ℝ)^(3/4 : ℝ) ≤ 212 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    exact hh.trans (mul_le_mul_of_nonneg_right h212 (Real.rpow_nonneg hlogpos _))
  have hΔE : Δ ≤ 212*E := by
    have hh := mul_le_mul_of_nonneg_left hpower hξ
    simpa only [Δ,E,mul_assoc,mul_left_comm] using hh
  have hwidth : (20000000000000000 : ℝ)*Δ+4*s ≤ 100000000000000000000*E := by
    have hE : 0 ≤ E := mul_nonneg hξ (Real.rpow_nonneg hlogpos _)
    nlinarith only [hΔE,hsΔ,hE]
  refine ⟨hmean.trans hwidth, ?_⟩
  intro t ht
  have htail := measureReal_hausdorffDist_spectrum_affineSeries_gt_of_half_measure
    A₀ hA₀ A hA S hmass hhalf ht
  refine le_trans ?_ htail
  apply measureReal_mono _ (by finiteness)
  intro x hx
  change 20000000000000000*Δ+4*s+2*s*t < H x
  have hst : 0 ≤ s*t := mul_nonneg hs ht
  change 100000000000000000000*E+100000000000000000000*s*t < H x at hx
  nlinarith only [hx,hwidth,hst]

open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian series and native free affine model satisfy the
source Hausdorff tail and expectation bounds for every coefficient family,
including zero variance. The universal constant is `10^20`.
Source: arXiv:2406.11453v2, Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem gaussian_free_hausdorffDist_le_with_probability_and_mean
    (hd : 2 ≤ Fintype.card d) (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
    let s := Real.sqrt (bilinearSquareMass A Finset.univ)
    let E := ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
    let H := fun x : ι → ℝ => Metric.hausdorffDist
      (spectrum ℝ (A₀+∑ i,x i•A i)) (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A))
    (∫ x : ι → ℝ, H x ∂gaussianVector ι) ≤ (100000000000000000000 : ℝ)*E ∧
      ∀ t : ℝ, 0 ≤ t → (gaussianVector ι).real
        {x | (100000000000000000000 : ℝ)*E+100000000000000000000*s*t < H x} ≤ Real.exp (-t^2) := by
  classical
  by_cases hmass : 0 < bilinearSquareMass A Finset.univ
  · exact gaussian_free_hausdorffDist_le_with_probability_and_mean_of_pos hd A₀ hA₀ A hA hmass
  have hz : bilinearSquareMass A Finset.univ=0 := le_antisymm (le_of_not_gt hmass)
    (bilinearSquareMass_nonneg _ _)
  have hH (x : ι → ℝ) := hausdorffDist_spectrum_gaussian_wordNative_eq_zero_of_zero_weak
    A₀ hA₀ A hz x
  dsimp only
  have hlog : 0 ≤ Real.log (Fintype.card d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card d))
  have hE : 0 ≤ Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*
      Real.sqrt (specNorm (coefficientCovariance A)))*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
  refine ⟨?_, ?_⟩
  · simp_rw [hH]
    rw [integral_zero]
    exact mul_nonneg (by norm_num) hE
  · intro t ht
    have he : {x : ι → ℝ |
        (100000000000000000000 : ℝ)*(Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*
          Real.sqrt (specNorm (coefficientCovariance A)))*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ))+
        100000000000000000000*Real.sqrt (bilinearSquareMass A Finset.univ)*t <
        Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,x i•A i))
          (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A))} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,hH]
      exact not_lt_of_ge (add_nonneg (mul_nonneg (by norm_num) hE)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) ht))
    rw [he,measureReal_empty]
    exact (Real.exp_pos _).le

end NLAlib
