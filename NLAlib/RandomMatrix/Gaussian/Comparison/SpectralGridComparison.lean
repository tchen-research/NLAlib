import NLAlib.RandomMatrix.Gaussian.Comparison.SpectralLocalization
import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventTwoSidedPointwiseComparison
import NLAlib.Probability.Transforms.ResolventSpectralHausdorffGrid
import NLAlib.Matrix.Spectral.SpectralIntervalNet

/-!
# Native two-sided spectral comparison at the source moment scale

The actual localization tails and two-sided resolvent bounds are assembled
on one deterministic grid of at most `9*d²` points. All matrix means,
covariances and moments refer to the original laws.
Source: arXiv:2201.05142v3, Proposition 7.7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n)⊕(n×n)

open scoped Matrix.Norms.L2Operator in
/-- A common deterministic spectral grid gives the actual Hausdorff
comparison for every coupling of a bounded independent Hermitian sum and
its full-covariance matching Gaussian matrix. The error scale satisfies
the literal source square-root, linear and cubic inequalities; no spectral
comparison, concentration conclusion or grid certificate is assumed.
Source: arXiv:2201.05142v3, Proposition 7.7, integer-moment version.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_hausdorffDist_spectra_gt_le_of_source_scale
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    {R s σ δ : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) (hσ : 0 ≤ σ)
    (hscale : 0 < R+s)
    (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
    (hmeanν : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hvariance : specNorm (∑ i, ∫ A : M,A^2 ∂ν i) ≤ σ^2)
    (hbilinear : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ A : M, ‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i) ≤ s^2)
    (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ,A.IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian)
    (hmean : (∫ A : M,A ∂ρ) = A₀+∫ x : ι → M,∑ i,x i ∂Measure.pi ν)
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b);ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i,x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i,x i) b);Measure.pi ν])
    (hd : 2 ≤ Fintype.card n) {p : ℕ} (hp : 0 < p)
    (hlog : Real.log (Fintype.card n) ≤ (p : ℝ))
    (hmesh : s*Real.sqrt (p : ℝ)+R*p ≤ δ)
    (hcube : R*σ^2*(p : ℝ)^2 ≤ δ^3)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ) :
    μ.real {ω | 3600000*δ <
      Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))} ≤
        60*(Fintype.card n : ℝ)^2*Real.exp (-(p : ℝ)) := by
  classical
  have := hS.isProbabilityMeasure
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  let a := s*Real.sqrt (p : ℝ)+R*p
  have ha : 0<a := by
    have hpS : 0<Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
    by_cases hpos : 0<R
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hs hpS.le) (mul_pos hpos hpR)
    · have hposS : 0<s := by linarith only [hscale,hpos]
      exact add_pos_of_pos_of_nonneg (mul_pos hposS hpS) (mul_nonneg hR hpR.le)
  have hδ : 0<δ := ha.trans_le hmesh
  let η := 200000*δ
  have hη : 0<η := by dsimp [η]; positivity
  have hsp : s*Real.sqrt (p : ℝ)≤δ :=
    (le_add_of_nonneg_right (mul_nonneg hR hpR.le)).trans hmesh
  have hRp : R*(p : ℝ)≤δ :=
    (le_add_of_nonneg_left (mul_nonneg hs (Real.sqrt_nonneg _))).trans hmesh
  let e := independentSumResolventError ν R s η p
  have herror : e+10*a/η^2≤(2*η)⁻¹ :=
    independentSumResolventError_add_mesh_le_inv_two_height ν hHerm hR hs hσ
      hBound hmeanν hvariance hd hp hlog hδ.le hη (by rfl) hmesh hsp hRp hcube
  obtain ⟨N,hcard,hcover⟩ := exists_finset_spectral_neighborhood_net_card_sq hA₀ ha
  let X (ω : Ω) := A₀+∑ i,S ω i
  have hXHerm : ∀ᵐ ω ∂μ,(X ω).IsHermitian := by
    have hprod : ∀ᵐ x ∂Measure.pi ν,∀ i,(x i).IsHermitian :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hHerm i)
    have harray : ∀ᵐ ω ∂μ,∀ i,(S ω i).IsHermitian := by
      apply ae_of_ae_map (p := fun x : ι → M => ∀ i,(x i).IsHermitian) hS.aemeasurable
      rwa [hS.map_eq]
    filter_upwards [harray] with ω hω
    exact hA₀.add (isSelfAdjoint_sum _ fun i _ => hω i)
  have hGHerm : ∀ᵐ ω ∂μ,(G ω).IsHermitian := by
    apply ae_of_ae_map hG.aemeasurable
    rwa [hG.map_eq]
  have hsumMean : (∫ x : ι → M,∑ i,x i ∂Measure.pi ν)=0 := by
    have hZi (i : ι) : Integrable (id : M → M) (ν i) :=
      Integrable.of_bound measurable_id.aestronglyMeasurable R (hBound i)
    rw [integral_finsetSum Finset.univ (f := fun i (x : ι → M) => x i) (fun i _ =>
      (measurePreserving_eval ν i).integrable_comp_of_integrable (hZi i))]
    simp only [integral_eval, hmeanν, Finset.sum_const_zero]
  have hmeanρ : (∫ A : M,A ∂ρ)=A₀ := by simpa only [hsumMean,add_zero] using hmean
  have htailX : μ.real {ω | 4*(Fintype.card n : ℝ)*a<specNorm (X ω-A₀)} ≤
      (2*Fintype.card n : ℝ)*Real.exp (-(p : ℝ)) := by
    simp only [X,add_sub_cancel_left]
    rw [hS.measureReal_eq (p := fun x : ι → M =>
      4*(Fintype.card n : ℝ)*a<specNorm (∑ i,x i)) (by
        apply measurableSet_lt measurable_const
        change Measurable (fun x : ι → M => ‖∑ i,x i‖)
        fun_prop)]
    exact measureReal_specNorm_sum_pi_gt_bilinear_scale_le ν hHerm hR hs hpR
      hscale (by omega) hBound hmeanν hbilinear
  have htailG : μ.real {ω | 4*(Fintype.card n : ℝ)*a<specNorm (G ω-A₀)} ≤
      4*(Fintype.card n : ℝ)^2*Real.exp (-(p : ℝ)) := by
    have hraw := measureReal_specNorm_gaussian_sub_mean_gt_bilinear_scale_le
      ν hs hpR.le hBound hmeanν hbilinear ρ hcov
    rw [hmeanρ] at hraw
    have hh : 4*(Fintype.card n : ℝ)*s*Real.sqrt (p : ℝ)≤4*Fintype.card n*a := by
      dsimp [a]
      have hr := mul_nonneg (show (0 : ℝ)≤4*Fintype.card n by positivity)
        (mul_nonneg hR hpR.le)
      linear_combination hr
    apply (measureReal_mono (μ := μ) (show
      {ω | 4*(Fintype.card n : ℝ)*a<specNorm (G ω-A₀)} ⊆
        {ω | 4*(Fintype.card n : ℝ)*s*Real.sqrt (p : ℝ)<specNorm (G ω-A₀)}
          from fun _ hx => lt_of_le_of_lt hh hx)).trans
    rw [hG.measureReal_eq (p := fun A : M =>
      4*(Fintype.card n : ℝ)*s*Real.sqrt (p : ℝ)<specNorm (A-A₀)) (by
        apply measurableSet_lt measurable_const
        change Measurable (fun A : M => ‖A-A₀‖)
        fun_prop)]
    exact hraw
  have hcoverX : μ.real {ω | ¬∀ ξ∈spectrum ℝ (X ω),∃ u∈N,|ξ-u|≤a} ≤
      μ.real {ω | 4*(Fintype.card n : ℝ)*a<specNorm (X ω-A₀)} := by
    exact measureReal_mono (μ := μ) (fun ω hω =>
      lt_of_not_ge (fun hh => hω (hcover (X ω) hh)))
  have hcoverG : μ.real {ω | ¬∀ ξ∈spectrum ℝ (G ω),∃ u∈N,|ξ-u|≤a} ≤
      μ.real {ω | 4*(Fintype.card n : ℝ)*a<specNorm (G ω-A₀)} := by
    exact measureReal_mono (μ := μ) (fun ω hω =>
      lt_of_not_ge (fun hh => hω (hcover (G ω) hh)))
  have hgrid := measureReal_hausdorffDist_spectra_gt_le_resolvent_grid
    μ X G hXHerm hGHerm N hη (show (0 : ℝ)≤9 by norm_num) (by
      simpa only [show (9 : ℝ)+1=10 by norm_num] using herror)
  have hpoint (u : ℝ) : μ.real {ω |
      9*specNorm (resolvent (G ω) ((u : ℂ)+(η : ℂ)*Complex.I))+e<
        specNorm (resolvent (X ω) ((u : ℂ)+(η : ℂ)*Complex.I)) ∨
      9*specNorm (resolvent (X ω) ((u : ℂ)+(η : ℂ)*Complex.I))+e<
        specNorm (resolvent (G ω) ((u : ℂ)+(η : ℂ)*Complex.I))} ≤
          6*Real.exp (-(p : ℝ)) := by
    have hi : (((u : ℂ)+(η : ℂ)*Complex.I)).im=η := by simp
    simpa only [hi,abs_of_pos hη,X,e] using
      measureReal_two_sided_resolvent_comparison_failure_le ν hHerm hR hBound ρ hρHerm
        A₀ hA₀ hmean hcov ((u : ℂ)+(η : ℂ)*Complex.I) (by rw [hi]; exact hη.ne')
          hp hlog hs hmeanν hbilinear μ S G hS hG
  have hsum := Finset.sum_le_sum (s := N) (fun u _ => hpoint u)
  have hcardR : (N.card : ℝ)≤9*(Fintype.card n : ℝ)^2 := by exact_mod_cast hcard
  have hsum' : (∑ u∈N,μ.real {ω |
      9*specNorm (resolvent (G ω) ((u : ℂ)+(η : ℂ)*Complex.I))+e<
        specNorm (resolvent (X ω) ((u : ℂ)+(η : ℂ)*Complex.I)) ∨
      9*specNorm (resolvent (X ω) ((u : ℂ)+(η : ℂ)*Complex.I))+e<
        specNorm (resolvent (G ω) ((u : ℂ)+(η : ℂ)*Complex.I))}) ≤
          54*(Fintype.card n : ℝ)^2*Real.exp (-(p : ℝ)) := by
    calc
      _ ≤ ∑ _u∈N,6*Real.exp (-(p : ℝ)) := hsum
      _ = (N.card : ℝ)*(6*Real.exp (-(p : ℝ))) := by simp
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hcardR
          (by positivity : 0≤6*Real.exp (-(p : ℝ)))
        linear_combination hh
  have hdR : (1 : ℝ)≤Fintype.card n := by exact_mod_cast (show 1≤Fintype.card n by omega)
  have hdim : (2*Fintype.card n : ℝ)*Real.exp (-(p : ℝ)) ≤
      2*(Fintype.card n : ℝ)^2*Real.exp (-(p : ℝ)) := by
    have hh : (Fintype.card n : ℝ)≤(Fintype.card n : ℝ)^2 := by nlinarith only [hdR]
    have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(p : ℝ))).le
    linear_combination 2*hh'
  have htotal := hgrid.trans (add_le_add
    (add_le_add (hcoverX.trans htailX) (hcoverG.trans htailG)) hsum')
  have hradius : (2 : ℝ)*9*η=3600000*δ := by dsimp [η]; ring
  rw [hradius] at htotal
  dsimp only [X] at htotal
  linarith only [htotal,hdim]

end NLAlib
