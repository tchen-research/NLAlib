import NLAlib.Matrix.Norms.Net
import NLAlib.Probability.SubGaussian.Moments
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.Complex.Exponential
import NLAlib.Matrix.Basic.QuadraticFunctional
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Expected norm from sub-Gaussian quadratic marginals

A real symmetric matrix whose unit quadratic forms are sub-Gaussian has
expected spectral norm at most `sqrt (12 c d)` in dimension at least two.
The proof uses a `1/8`-net of size at most `17^d`, the `4/3` norming factor,
and the already established finite sub-Gaussian maximal inequality.
Source: Tropp (2026), Section 3.3.1, and the post-BMV covariance roadmap.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset Real

namespace NLAlib

private theorem log_two_mul_card_le (d k : ℕ) (hd : 2 ≤ d)
    (hk : (k : ℝ) ≤ (17 : ℝ) ^ d) (hkpos : 0 < k) :
    log (2 * (k : ℝ)) ≤ 27 / 8 * d := by
  have h17 : log (17 : ℝ) ≤ 3 := by
    apply (log_le_iff_le_exp (by norm_num)).mpr
    have h := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 6
    norm_num [sum_range_succ] at h
    linarith
  have h2 : log (2 : ℝ) ≤ 3 / 4 := by
    apply (log_le_iff_le_exp (by norm_num)).mpr
    have h := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num) 3
    norm_num [sum_range_succ] at h
    linarith
  have hlog := log_le_log (show (0 : ℝ) < k by exact_mod_cast hkpos) hk
  rw [log_pow] at hlog
  rw [log_mul (by norm_num) (by exact_mod_cast hkpos.ne')]
  have hmul := mul_le_mul_of_nonneg_left h17 (show (0 : ℝ) ≤ d by positivity)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

open scoped Matrix.Norms.L2Operator in
/-- Unit sub-Gaussian quadratic forms of a real symmetric random matrix give
an integrable spectral norm and the bound `sqrt (12 c d)`, with no independence
assumption between its entries. Source: Tropp (2026), Section 3.3.1.
atlas: sample-covariance-fourth-moment-lower (partial) -/
theorem integrable_specNorm_and_integral_le_sqrt_of_quadratic_hasSubgaussianMGF
    {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℝ) (hX : Measurable X)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (c : NNReal) (hd : 2 ≤ Fintype.card n)
    (hsg : ∀ u : n → ℝ, ‖WithLp.toLp 2 u‖ = 1 →
      HasSubgaussianMGF (fun ω => quadForm (X ω) u) c μ) :
    Integrable (fun ω => specNorm (X ω)) μ ∧
      (∫ ω, specNorm (X ω) ∂μ) ≤ sqrt (12 * (c : ℝ) * Fintype.card n) := by
  classical
  have hn : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨N, hNunit, hNcard, hNcover⟩ :=
    exists_finset_sphere_net n (show (0 : ℝ) < 1 / 8 by norm_num)
  norm_num at hNcard
  have hNnonempty : N.Nonempty := by
    let u : n → ℝ := Pi.single (Classical.arbitrary n) 1
    have hu : u ⬝ᵥ u = 1 := by simp only [u, single_dotProduct, Pi.single_eq_same, one_mul]
    obtain ⟨x, hx, _⟩ := hNcover u hu
    exact ⟨x, hx⟩
  let : Nonempty N := hNnonempty.to_subtype
  let Y : N → Ω → ℝ := fun u ω => quadForm (X ω) (u : n → ℝ)
  have hunit (u : N) : ‖WithLp.toLp 2 (u : n → ℝ)‖ = 1 := by
    have h := norm_toLp_sq_eq_dotProduct_self (u : n → ℝ)
    rw [hNunit u u.property] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 (u : n → ℝ))]
  have hY (u : N) : HasSubgaussianMGF (Y u) c μ := hsg u (hunit u)
  let m : Ω → ℝ := fun ω => ⨆ u : N, |Y u ω|
  have hm : Integrable m μ := integrable_iSup_abs_of_hasSubgaussianMGF Y c hY
  have hm0 (ω : Ω) : 0 ≤ m ω := by
    obtain ⟨u⟩ := ‹Nonempty N›
    change 0 ≤ ⨆ u : N, |Y u ω|
    exact (abs_nonneg (Y u ω)).trans
      (le_ciSup (f := fun u : N => |Y u ω|) (Finite.bddAbove_range _) u)
  have hbound : ∀ᵐ ω ∂μ, specNorm (X ω) ≤ (4 / 3 : ℝ) * m ω := by
    filter_upwards [hHerm] with ω hω
    have h := specNorm_le_div_of_net_quadForm hω N (ε := 1 / 8) (M := m ω)
      (by norm_num) (by norm_num) (hm0 ω)
      (fun u hu => by
        have he := norm_toLp_sq_eq_dotProduct_self u
        rw [hNunit u hu] at he
        nlinarith [norm_nonneg (WithLp.toLp 2 u)])
      (fun y hy => by
        have he : y ⬝ᵥ y = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hy, one_pow]
        obtain ⟨x, hx, hxy⟩ := hNcover y he
        refine ⟨x, hx, ?_⟩
        have h := norm_toLp_sq_eq_dotProduct_self (x - y)
        rw [← h] at hxy
        nlinarith [norm_nonneg (WithLp.toLp 2 (x - y))])
      (fun u hu => by
        change |Y ⟨u, hu⟩ ω| ≤ ⨆ v : N, |Y v ω|
        exact le_ciSup (f := fun v : N => |Y v ω|) (Finite.bddAbove_range _) (⟨u, hu⟩ : N))
    convert h using 1
    ring
  have hi : Integrable (fun ω => specNorm (X ω)) μ := by
    apply (hm.const_mul (4 / 3 : ℝ)).mono'
    · have hc : Continuous (fun A : Matrix n n ℝ => specNorm A) := by
        simp only [specNorm_eq_norm]
        fun_prop
      exact (hc.measurable.comp hX).aestronglyMeasurable
    · filter_upwards [hbound] with ω hω
      simpa only [Real.norm_eq_abs, abs_of_nonneg (specNorm_nonneg _)] using hω
  refine ⟨hi, ?_⟩
  have hmax := integral_iSup_abs_le_sqrt_of_hasSubgaussianMGF Y c hY
  have hlog : log (2 * (Fintype.card N : ℝ)) ≤ 27 / 8 * Fintype.card n := by
    rw [Fintype.card_coe]
    exact log_two_mul_card_le _ _ hd hNcard hNnonempty.card_pos
  have hnorm := integral_mono_ae hi (hm.const_mul (4 / 3 : ℝ)) hbound
  rw [integral_const_mul] at hnorm
  refine hnorm.trans ((mul_le_mul_of_nonneg_left hmax (by norm_num)).trans ?_)
  have harg : 2 * (c : ℝ) * log (2 * (Fintype.card N : ℝ)) ≤
      2 * (c : ℝ) * (27 / 8 * Fintype.card n) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hs := Real.sqrt_le_sqrt harg
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤
      2 * (c : ℝ) * (27 / 8 * Fintype.card n) by positivity)
  have hfinal := Real.sq_sqrt (show (0 : ℝ) ≤ 12 * (c : ℝ) * Fintype.card n by positivity)
  nlinarith [Real.sqrt_nonneg (2 * (c : ℝ) * log (2 * (Fintype.card N : ℝ))),
    Real.sqrt_nonneg (12 * (c : ℝ) * Fintype.card n)]

open scoped Matrix.Norms.L2Operator in
/-- A fixed real quadratic observable under a centered Gaussian matrix law is
sub-Gaussian with any upper bound on its actual variance. No independence
between matrix entries or nonsingular covariance is required. -/
theorem hasSubgaussianMGF_quadForm_gaussian
    {n : Type*} [Fintype n] [DecidableEq n]
    (γ : Measure (Matrix n n ℝ)) [IsGaussian γ]
    (hmean : (∫ Z, Z ∂γ) = 0) (u : n → ℝ) (c : NNReal)
    (hvariance : Var[fun Z => quadForm Z u; γ] ≤ c) :
    HasSubgaussianMGF (fun Z => quadForm Z u) c γ := by
  let L : Matrix n n ℝ →L[ℝ] ℝ := quadFormContinuousLinearMap u
  let v : NNReal := (Var[fun Z => quadForm Z u; γ]).toNNReal
  have hLi := L.integral_comp_comm (IsGaussian.integrable_id (μ := γ))
  change (∫ Z, L Z ∂γ) = L (∫ Z, Z ∂γ) at hLi
  have hm : (∫ Z, L Z ∂γ) = 0 := by rw [hLi, hmean, map_zero]
  have hmap : γ.map L = gaussianReal 0 v := by
    have hmap' := IsGaussian.map_eq_gaussianReal (μ := γ) L
    rw [hm] at hmap'
    exact hmap'
  have hq : AEMeasurable (fun Z => quadForm Z u) γ := L.continuous.measurable.aemeasurable
  have hbase : HasSubgaussianMGF (fun Z => quadForm Z u) v γ := by
    rw [← HasSubgaussianMGF.id_map_iff hq]
    change HasSubgaussianMGF id v (γ.map L)
    rw [hmap]
    exact hasSubgaussianMGF_id_gaussianReal v
  have hvc : (v : ℝ) ≤ c := by
    simpa only [v, Real.coe_toNNReal _ (variance_nonneg _ _)] using hvariance
  refine ⟨hbase.integrable_exp_mul, fun t => (hbase.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hvc (sq_nonneg t)) (by norm_num)

open scoped Matrix.Norms.L2Operator in
/-- A centered real symmetric Gaussian law has expected spectral norm at most
`sqrt (12 c d)` when every unit quadratic form has actual variance at most `c`.
Integrability is proved as part of the conclusion. Source: Tropp (2026),
Section 3.3.1, the sphere-net bound used in the fourth-moment covariance theorem.
atlas: sample-covariance-fourth-moment-lower (partial) -/
theorem integrable_specNorm_and_integral_le_sqrt_gaussian_of_quadratic_variance
    {n : Type*} [Fintype n] [DecidableEq n]
    (γ : Measure (Matrix n n ℝ)) [IsGaussian γ]
    (hmean : (∫ Z, Z ∂γ) = 0) (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian)
    (c : NNReal) (hd : 2 ≤ Fintype.card n)
    (hvariance : ∀ u : n → ℝ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => quadForm Z u; γ] ≤ c) :
    Integrable (fun Z => specNorm Z) γ ∧
      (∫ Z, specNorm Z ∂γ) ≤ sqrt (12 * (c : ℝ) * Fintype.card n) :=
  integrable_specNorm_and_integral_le_sqrt_of_quadratic_hasSubgaussianMGF
    id measurable_id hHerm c hd
    (fun u hu => hasSubgaussianMGF_quadForm_gaussian γ hmean u c (hvariance u hu))

end NLAlib
