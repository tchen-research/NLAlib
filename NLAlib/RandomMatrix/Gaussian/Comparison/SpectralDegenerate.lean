import NLAlib.RandomMatrix.Gaussian.Comparison.SpectralLocalization
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Zero-radius independent sums and their matching Gaussian matrices

The actual increment norm bound forces the sum to be deterministic. Full
entry covariance matching forces its Gaussian proxy to have the same
constant value, including singular covariance and empty dimensions.
Source: arXiv:2201.05142v3, Theorem 2.6, degenerate case.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n)⊕(n×n)

open scoped Matrix.Norms.L2Operator in
/-- A zero almost-sure increment radius makes the actual independent sum
and its full-covariance matching Gaussian proxy equal to their common mean
almost surely, for every coupling of their native laws. -/
theorem ae_eq_constant_sum_and_gaussian_of_zero_radius
    (ν : ι → Measure M) [∀ i,IsProbabilityMeasure (ν i)]
    (hBound : ∀ i,∀ᵐ A ∂ν i,specNorm A≤0)
    (ρ : Measure M) [IsGaussian ρ] (A₀ : M)
    (hmean : (∫ A : M,A ∂ρ)=A₀+∫ x : ι → M,∑ i,x i ∂Measure.pi ν)
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b);ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i,x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i,x i) b);Measure.pi ν])
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ) :
    ∀ᵐ ω ∂μ,(A₀+∑ i,S ω i)=A₀ ∧ G ω=A₀ := by
  have hνzero (i : ι) : ∀ᵐ A ∂ν i,A=0 := by
    filter_upwards [hBound i] with A hA
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [specNorm_eq_norm] using hA) (norm_nonneg _)
  have hmeanν (i : ι) : (∫ A : M,A ∂ν i)=0 := by
    simpa only [integral_zero] using integral_congr_ae (hνzero i)
  have hprod : ∀ᵐ x ∂Measure.pi ν,∀ i,x i=0 := ae_all_iff.mpr fun i =>
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hνzero i)
  have hsumMean : (∫ x : ι → M,∑ i,x i ∂Measure.pi ν)=0 := by
    calc
      _ = ∫ _x : ι → M,(0 : M) ∂Measure.pi ν := integral_congr_ae
        (hprod.mono fun x hx => by simp only [hx,Finset.sum_const_zero])
      _ = _ := integral_zero _ _
  have hmeanρ : (∫ A : M,A ∂ρ)=A₀ := by simpa only [hsumMean,add_zero] using hmean
  have hbudget (a b : EuclideanSpace ℂ n) (_ha : ‖a‖≤1) (_hb : ‖b‖≤1) :
      (∑ i,∫ A : M,‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i)≤(0 : ℝ)^2 := by
    have hi (i : ι) : (∫ A : M,‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i)=0 := by
      calc
        _ = ∫ _A : M,(0 : ℝ) ∂ν i := integral_congr_ae ((hνzero i).mono fun A hA => by simp [hA])
        _ = _ := integral_zero _ _
    simp only [hi,Finset.sum_const_zero,le_refl,zero_pow (by decide : (2 : ℕ)≠0)]
  have htail (p : ℝ) (hp : 0≤p) :
      ρ.real {A : M | 0<specNorm (A-A₀)}≤4*(Fintype.card n : ℝ)^2*Real.exp (-p) := by
    simpa only [zero_mul,mul_zero,hmeanρ] using
      measureReal_specNorm_gaussian_sub_mean_gt_bilinear_scale_le
        ν (le_refl (0 : ℝ)) hp hBound hmeanν hbudget ρ hcov
  have ht : Tendsto (fun p : ℝ => 4*(Fintype.card n : ℝ)^2*Real.exp (-p))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have hz : ρ.real {A : M | 0<specNorm (A-A₀)}=0 := le_antisymm
    (ge_of_tendsto ht (eventually_atTop.mpr ⟨0,fun p hp => htail p hp⟩)) measureReal_nonneg
  have hρzero : ∀ᵐ A ∂ρ,A=A₀ := by
    have hnorm : ∀ᵐ A ∂ρ,specNorm (A-A₀)≤0 := by
      rw [ae_iff]
      simpa only [not_le] using ((measureReal_eq_zero_iff).mp hz)
    filter_upwards [hnorm] with A hA
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [specNorm_eq_norm] using hA) (norm_nonneg _)
  have hGzero : ∀ᵐ ω ∂μ,G ω=A₀ := by
    apply ae_of_ae_map (p := fun A : M => A=A₀) hG.aemeasurable
    rwa [hG.map_eq]
  have hSzero : ∀ᵐ ω ∂μ,∀ i,S ω i=0 := by
    apply ae_of_ae_map (p := fun x : ι → M => ∀ i,x i=0) hS.aemeasurable
    rwa [hS.map_eq]
  filter_upwards [hGzero,hSzero] with ω hωG hωS
  exact ⟨by simp only [hωS,Finset.sum_const_zero,add_zero],hωG⟩

end NLAlib
