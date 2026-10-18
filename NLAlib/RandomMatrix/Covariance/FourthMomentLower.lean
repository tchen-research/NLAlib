import NLAlib.RandomMatrix.Covariance.FourthMomentSummands
import NLAlib.RandomMatrix.Covariance.FourthMomentSampleSize
import NLAlib.RandomMatrix.Covariance.SampleCovarianceMoments
import NLAlib.RandomMatrix.Covariance.FourthMomentAggregate
import NLAlib.RandomMatrix.Covariance.FourthMomentProxy
import NLAlib.Probability.Concentration.Matrix.RealWeakVariance
import NLAlib.Matrix.Spectral.IdentityDefect

/-!
# Relative lower covariance estimation with fourth moments

The negative rank-one summands have a deterministic one-sided bound. Their
full covariance gives an actual Gaussian proxy; directional fourth moments
control its statistics. Whitening transports the resulting isotropic lower
bound to any positive-definite second moment.
Source: Tropp (2026), Theorem 3.3 and Section 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder
namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The exact sample count with constant 26 turns the Gaussian-proxy
three-term deviation bound into failure probability at most `δ`.
Source: Tropp (2026), Section 3.3.1. -/
theorem measureReal_gt_le_of_fourthMoment_sample_size [IsProbabilityMeasure μ]
    {L : Ω → ℝ} {v D n ε δ φ V : ℝ}
    (hv : 1 ≤ v) (hD : 1 ≤ D) (hn : 0 < n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 26 * v * max D (Real.log (D / δ)) / ε ^ 2 ≤ n)
    (hφ : φ ≤ Real.sqrt (12 * v * D / n))
    (hV : V ≤ (v + Real.sqrt (12 * v * D / n) / 3) / n)
    (htail : ∀ s : ℝ, 0 ≤ s →
      μ.real {ω | φ + Real.sqrt (2 * V * s) + (n⁻¹ / 3) * s < L ω} ≤
        D * Real.exp (-s)) :
    μ.real {ω | ε < L ω} ≤ δ := by
  let s := Real.log (D / δ)
  have hD0 : 0 < D := by linarith
  have hs : 0 ≤ s := Real.log_nonneg (by apply (le_div_iff₀ hδ).mpr; linarith)
  have hthreshold : φ + Real.sqrt (2 * V * s) + (n⁻¹ / 3) * s ≤ ε := by
    have hroot : Real.sqrt (2 * V * s) ≤
        Real.sqrt (2 * s * (v + Real.sqrt (12 * v * D / n) / 3) / n) := by
      apply Real.sqrt_le_sqrt
      calc
        2 * V * s = (2 * s) * V := by ring
        _ ≤ (2 * s) * ((v + Real.sqrt (12 * v * D / n) / 3) / n) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
        _ = _ := by ring
    have hc : (n⁻¹ / 3) * s = s / (3 * n) := by ring
    rw [hc]
    have hsize' := sqrt_add_sqrt_add_div_le_of_sample_size hv (show 0 ≤ D by linarith)
      hs hn hε hε1 hsize
    linarith
  have hprob := (measureReal_mono (fun ω hω => lt_of_le_of_lt hthreshold hω)).trans (htail s hs)
  have he : D * Real.exp (-s) = δ := by
    rw [Real.exp_neg, Real.exp_log (div_pos hD0 hδ)]
    field_simp
  exact hprob.trans_eq he

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- For an isotropic real vector law with finite fourth moments, the exact
sample count `26 * β² * max(d, log(d/δ)) / ε²` ensures a relative lower
covariance bound except on an event of probability at most `δ`.
Source: Tropp (2026), Theorem 3.3.
atlas: sample-covariance-fourth-moment-lower -/
theorem measureReal_not_smul_one_le_sampleCovariance_pi_le
    (μ : Measure (d → ℝ)) [IsProbabilityMeasure μ]
    (hd : 2 ≤ Fintype.card d)
    (hμ : MemLp (id : (d → ℝ) → d → ℝ) 4 μ)
    (hisotropic : (∫ x, vecMulVec x x ∂μ) = (1 : Matrix d d ℝ))
    {β ε δ : ℝ} (hβ : 1 ≤ β)
    (hfourth : ∀ a : d → ℝ,
      Var[fun x => (x ⬝ᵥ a) ^ 2; μ] ≤ β ^ 2 * (∫ x, (x ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {N : ℕ}
    (hsize : 26 * β ^ 2 * max (Fintype.card d : ℝ)
      (Real.log ((Fintype.card d : ℝ) / δ)) / ε ^ 2 ≤ (N : ℝ)) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {x | ¬ ((1 - ε) • (1 : Matrix d d ℝ) ≤ sampleCovariance x)} ≤ δ := by
  have hdpos : 0 < Fintype.card d := by omega
  let : Nonempty d := Fintype.card_pos_iff.mp hdpos
  have hNreal : 0 < (N : ℝ) := by
    have hdreal : 0 < (Fintype.card d : ℝ) := by exact_mod_cast hdpos
    have hmax : 0 < max (Fintype.card d : ℝ) (Real.log ((Fintype.card d : ℝ) / δ)) :=
      lt_of_lt_of_le hdreal (le_max_left _ _)
    have hp : 0 < 26 * β ^ 2 * max (Fintype.card d : ℝ)
        (Real.log ((Fintype.card d : ℝ) / δ)) / ε ^ 2 := by positivity
    exact hp.trans_le hsize
  have hN : 0 < N := by exact_mod_cast hNreal
  let : NeZero N := ⟨hN.ne'⟩
  let P := Measure.pi (fun _ : Fin N => μ)
  let Y : (Fin N → d → ℝ) → Matrix d d ℝ := fun x => 1 - sampleCovariance x
  obtain ⟨γ, hγ, hγmean, hγHerm, hγcov, htail⟩ :=
    exists_gaussian_covarianceDefect_pi μ hμ hisotropic hN
  let : IsGaussian γ := hγ
  let c : NNReal := ⟨β ^ 2 / (N : ℝ), by positivity⟩
  have hc : (c : ℝ) = β ^ 2 / (N : ℝ) := rfl
  have hY2 : MemLp Y 2 P :=
    (memLp_const (1 : Matrix d d ℝ)).sub (memLp_two_sampleCovariance_pi hμ)
  have hYmean : (∫ x, Y x ∂P) = 0 := integral_one_sub_sampleCovariance_pi_eq_zero hμ hisotropic
  have hYvar (u : d → ℝ) : Var[fun x => quadForm (Y x) u; P] ≤
      (c : ℝ) * ‖WithLp.toLp 2 u‖ ^ 4 := by
    rw [hc]
    simpa only [Fintype.card_fin, id_eq, Y, P] using
      variance_quadForm_one_sub_sampleCovariance_pi_le (ι := Fin N) hμ hisotropic hfourth u
  have hstats := quadraticWeakVariance_le_and_integral_lambdaMax_le_of_covariance_eq_real
    P Y hY2 hYmean γ hγHerm hγmean hγcov c hd hYvar
  have hφ : (∫ Z, lambdaMax Z ∂γ) ≤ Real.sqrt (12 * β ^ 2 * Fintype.card d / (N : ℝ)) := by
    have he : 12 * (c : ℝ) * Fintype.card d = 12 * β ^ 2 * Fintype.card d / (N : ℝ) := by
      rw [hc]
      ring
    simpa only [he] using hstats.2
  have hV : gaussianProxyVariance γ (N : ℝ)⁻¹ ≤
      (β ^ 2 + Real.sqrt (12 * β ^ 2 * Fintype.card d / (N : ℝ)) / 3) / (N : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hφ (show 0 ≤ (N : ℝ)⁻¹ by positivity)
    have h2 := hstats.1
    change quadraticWeakVariance γ ≤ β ^ 2 / (N : ℝ) at h2
    dsimp [gaussianProxyVariance]
    calc
      (N : ℝ)⁻¹ * (∫ Z, lambdaMax Z ∂γ) / 3 + quadraticWeakVariance γ ≤
          (N : ℝ)⁻¹ * Real.sqrt (12 * β ^ 2 * Fintype.card d / (N : ℝ)) / 3 +
            β ^ 2 / (N : ℝ) := by linarith
      _ = _ := by ring
  have hprob := measureReal_gt_le_of_fourthMoment_sample_size
    (μ := P) (L := fun x => lambdaMax (realMatrixComplexification (Y x) : Matrix d d ℂ))
    (show 1 ≤ β ^ 2 by nlinarith)
    (show 1 ≤ (Fintype.card d : ℝ) by exact_mod_cast (show 1 ≤ Fintype.card d by omega))
    hNreal hε hε1.le hδ hδ1 hsize hφ hV htail
  apply (measureReal_mono ?_).trans hprob
  intro x hx
  exact lt_lambdaMax_complexification_one_sub_of_not_smul_one_le
    (posSemidef_sampleCovariance x).isHermitian hx

open scoped Matrix.Norms.L2Operator in
/-- A positive-definite actual second moment is estimated from below with
failure probability at most `δ` using only finite fourth moments and the
directional fourth-moment variance bound. The sample-size constant is exactly
26. No observation-norm bound is assumed.
Source: Tropp (2026), Theorem 3.3.
atlas: sample-covariance-fourth-moment-lower -/
theorem measureReal_not_smul_le_sampleCovariance_pi_le
    (μ : Measure (d → ℝ)) [IsProbabilityMeasure μ]
    (hd : 2 ≤ Fintype.card d)
    (hμ : MemLp (id : (d → ℝ) → d → ℝ) 4 μ)
    (K : Matrix d d ℝ) (hK : K.PosDef)
    (hsecond : (∫ x, vecMulVec x x ∂μ) = K)
    {β ε δ : ℝ} (hβ : 1 ≤ β)
    (hfourth : ∀ a : d → ℝ,
      Var[fun x => (x ⬝ᵥ a) ^ 2; μ] ≤ β ^ 2 * (∫ x, (x ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {N : ℕ}
    (hsize : 26 * β ^ 2 * max (Fintype.card d : ℝ)
      (Real.log ((Fintype.card d : ℝ) / δ)) / ε ^ 2 ≤ (N : ℝ)) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {x | ¬ ((1 - ε) • K ≤ sampleCovariance x)} ≤ δ := by
  obtain ⟨S, hS, hwhite, hSiso⟩ := exists_isUnit_whitening_second_moment
    (hμ.mono_exponent (by norm_num)) K hK hsecond
  let L := (Matrix.mulVecLin S).toContinuousLinearMap
  let ν := μ.map L
  have hL : HasLaw L ν μ := ⟨L.continuous.measurable.aemeasurable, rfl⟩
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
  have hν4 : MemLp (id : (d → ℝ) → d → ℝ) 4 ν := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id L.continuous.measurable.aemeasurable).mpr
    exact L.comp_memLp' hμ
  have hνiso : (∫ x, vecMulVec x x ∂ν) = (1 : Matrix d d ℝ) := by
    have he := hL.integral_comp (f := fun x => vecMulVec x x) (by fun_prop)
    exact he.symm.trans hSiso
  have hνfourth (a : d → ℝ) :
      Var[fun x => (x ⬝ᵥ a) ^ 2; ν] ≤ β ^ 2 * (∫ x, (x ⬝ᵥ a) ^ 2 ∂ν) ^ 2 := by
    have hv := hL.covariance_fun_comp
      (f := fun x => (x ⬝ᵥ a) ^ 2) (g := fun x => (x ⬝ᵥ a) ^ 2) (by fun_prop) (by fun_prop)
    rw [covariance_self (by fun_prop), covariance_self (by fun_prop)] at hv
    have hm := hL.integral_comp (f := fun x => (x ⬝ᵥ a) ^ 2) (by fun_prop)
    rw [← hv, ← hm]
    exact variance_sq_dotProduct_mulVec_le hfourth S a
  have hb := measureReal_not_smul_one_le_sampleCovariance_pi_le
    ν hd hν4 hνiso hβ hνfourth hε hε1 hδ hδ1 hsize
  let P := Measure.pi (fun _ : Fin N => μ)
  have hmaps (i : Fin N) : HasLaw (fun x : Fin N → d → ℝ => L (x i)) ν P :=
    hL.fun_comp (measurePreserving_eval (fun _ : Fin N => μ) i).hasLaw
  have hpi : HasLaw (fun x : Fin N → d → ℝ => fun i => L (x i))
      (Measure.pi (fun _ : Fin N => ν)) P :=
    (iIndepFun_pi (fun _ : Fin N => L.continuous.measurable.aemeasurable)).hasLaw_pi hmaps
  have hcont : Continuous (sampleCovariance : (Fin N → d → ℝ) → Matrix d d ℝ) := by
    change Continuous (fun x : Fin N → d → ℝ =>
      (Fintype.card (Fin N) : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (star (x i)))
    fun_prop
  have hset : MeasurableSet {x : Fin N → d → ℝ |
      ¬ ((1 - ε) • (1 : Matrix d d ℝ) ≤ sampleCovariance x)} :=
    ((isClosed_setOf_le_realMatrix ((1 - ε) • (1 : Matrix d d ℝ))).preimage hcont).measurableSet.compl
  have he := hpi.measureReal_eq hset
  have hsets : {x : Fin N → d → ℝ | ¬ ((1 - ε) • K ≤ sampleCovariance x)} =
      {x : Fin N → d → ℝ |
        ¬ ((1 - ε) • (1 : Matrix d d ℝ) ≤ sampleCovariance (fun i => L (x i)))} := by
    ext x
    exact not_congr (smul_le_sampleCovariance_iff_whitened hS hwhite x (1 - ε))
  change P.real _ ≤ δ
  rw [hsets, he]
  exact hb

open scoped Matrix.Norms.L2Operator in
/-- The relative covariance lower bound for actual iid observations with
their specified common law. This native-law version retains a full
positive-definite covariance and the exact sample-size constant 26.
Source: Tropp (2026), Theorem 3.3.
atlas: sample-covariance-fourth-moment-lower -/
theorem measureReal_not_smul_le_sampleCovariance_le_of_hasLaw
    {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (W : Fin N → Ω → d → ℝ)
    (μ : Measure (d → ℝ)) [IsProbabilityMeasure μ]
    (hW : ∀ i, HasLaw (W i) μ P) (hind : iIndepFun W P)
    (hd : 2 ≤ Fintype.card d)
    (hμ : MemLp (id : (d → ℝ) → d → ℝ) 4 μ)
    (K : Matrix d d ℝ) (hK : K.PosDef)
    (hsecond : (∫ x, vecMulVec x x ∂μ) = K)
    {β ε δ : ℝ} (hβ : 1 ≤ β)
    (hfourth : ∀ a : d → ℝ,
      Var[fun x => (x ⬝ᵥ a) ^ 2; μ] ≤ β ^ 2 * (∫ x, (x ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 26 * β ^ 2 * max (Fintype.card d : ℝ)
      (Real.log ((Fintype.card d : ℝ) / δ)) / ε ^ 2 ≤ (N : ℝ)) :
    P.real {ω | ¬ ((1 - ε) • K ≤ sampleCovariance (fun i => W i ω))} ≤ δ := by
  have hpi := hind.hasLaw_pi hW
  have hcont : Continuous (sampleCovariance : (Fin N → d → ℝ) → Matrix d d ℝ) := by
    change Continuous (fun x : Fin N → d → ℝ =>
      (Fintype.card (Fin N) : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (star (x i)))
    fun_prop
  have hset : MeasurableSet {x : Fin N → d → ℝ | ¬ ((1 - ε) • K ≤ sampleCovariance x)} :=
    ((isClosed_setOf_le_realMatrix ((1 - ε) • K)).preimage hcont).measurableSet.compl
  rw [hpi.measureReal_eq hset]
  exact measureReal_not_smul_le_sampleCovariance_pi_le
    μ hd hμ K hK hsecond hβ hfourth hε hε1 hδ hδ1 hsize

end NLAlib
