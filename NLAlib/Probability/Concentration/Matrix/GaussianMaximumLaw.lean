import NLAlib.Probability.Concentration.Matrix.GaussianMaximum
import NLAlib.Probability.Concentration.Matrix.ExpectExtremaIntegrable
import NLAlib.Probability.Concentration.Matrix.GaussianTraceExponential
import NLAlib.Probability.Gaussian.Basic.MatrixSeriesRepresentation
import Mathlib.Probability.IdentDistrib

/-!
# Maximum-eigenvalue concentration for actual Hermitian Gaussian laws

A faithful Hermitian scalar-series realization transports the weak quadratic
variance concentration theorem to arbitrary centered Gaussian matrix laws.
Singular covariance, zero variance and deterministic Hermitian shifts are
included. Measurability follows from a continuous Hermitian-part extension.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- The centered maximum eigenvalue under any actual centered Hermitian
Gaussian law has a sub-Gaussian MGF with its quadratic-form weak variance.
The variance hypothesis quantifies only unit-vector quadratic forms and
includes singular Gaussian covariance and zero weak variance.
Source: Gaussian concentration in Tropp (2026), Proposition 4.7.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem hasSubgaussianMGF_lambdaMax_add_gaussian
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) :
    HasSubgaussianMGF
      (fun Z => lambdaMax (D + Z) - ∫ H, lambdaMax (D + H) ∂γ)
      ⟨σ ^ 2, sq_nonneg σ⟩ γ := by
  obtain ⟨A, hA, hrep⟩ := exists_hermitian_gaussian_series_representation γ hmean hHerm
  let J := (n × n) ⊕ (n × n)
  let S : (J → ℝ) → M := fun x => ∑ i, x i • A i
  have hSm : Measurable S := by fun_prop
  have hid : IdentDistrib S (id : M → M) (gaussianVector J) γ :=
    ⟨hSm.aemeasurable, aemeasurable_id, by simpa only [Measure.map_id] using hrep.symm⟩
  have hvarianceS : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun x : J → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector J] ≤ σ ^ 2 := by
    intro u hu
    have hq : Measurable (fun Z : M => (quadForm Z u).re) := by
      simp only [quadForm, dotProduct, Matrix.mulVec]
      fun_prop
    have he := (hid.comp hq).variance_eq
    have he' : Var[fun x : J → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector J] =
        Var[fun Z => (quadForm Z u).re; γ] := by
      simpa only [Function.comp_def, id_eq, S] using he
    exact he'.trans_le (hvariance u hu)
  have hsg := hasSubgaussianMGF_lambdaMax_affineSeries_of_quadratic_variance
    D hD A hA hσ hvarianceS
  have ho : AEMeasurable (fun Z : M => lambdaMax (D + Z)) ((gaussianVector J).map S) := by
    rw [← hrep]
    exact aemeasurable_lambdaMax_add_of_ae_isHermitian D hD aemeasurable_id hHerm
  have hobs := hid.comp_of_aemeasurable ho
  simp only [Function.comp_def, id_eq, S] at hobs
  have hmeanobs : (∫ x : J → ℝ, lambdaMax (D + ∑ i, x i • A i) ∂gaussianVector J) =
      ∫ Z, lambdaMax (D + Z) ∂γ := hobs.integral_eq
  have hcenter := hobs.sub_const (∫ H, lambdaMax (D + H) ∂γ)
  have hsg' : HasSubgaussianMGF
      (fun x : J → ℝ => lambdaMax (D + ∑ i, x i • A i) -
        ∫ H, lambdaMax (D + H) ∂γ) ⟨σ ^ 2, sq_nonneg σ⟩ (gaussianVector J) := by
    rw [← hmeanobs]
    exact hsg
  exact hsg'.congr_identDistrib hcenter

open scoped Matrix.Norms.L2Operator in
/-- The largest eigenvalue at a fixed Hermitian shift is integrable under
an actual Gaussian law with any finite weak quadratic variance bound. -/
theorem integrable_lambdaMax_add_gaussian
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) :
    Integrable (fun Z => lambdaMax (D + Z)) γ := by
  have h := (hasSubgaussianMGF_lambdaMax_add_gaussian γ D hD hHerm hmean hσ hvariance).integrable
  have hh := h.add (integrable_const (∫ H, lambdaMax (D + H) ∂γ))
  simpa only [Pi.add_def, sub_add_cancel] using hh

open scoped Matrix.Norms.L2Operator in
/-- The uncentered maximum-eigenvalue MGF under an actual Hermitian Gaussian
law is controlled by its actual mean and weak quadratic variance at every
real exponential parameter. No exponential moment hypothesis is needed.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem integral_exp_mul_lambdaMax_add_gaussian_le
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) (t : ℝ) :
    (∫ Z, Real.exp (t * lambdaMax (D + Z)) ∂γ) ≤
      Real.exp (t * (∫ Z, lambdaMax (D + Z) ∂γ) + t ^ 2 * σ ^ 2 / 2) := by
  let f : M → ℝ := fun Z => lambdaMax (D + Z)
  let m : ℝ := ∫ Z, f Z ∂γ
  have hsg := hasSubgaussianMGF_lambdaMax_add_gaussian γ D hD hHerm hmean hσ hvariance
  have he : mgf f γ t = mgf (fun Z => f Z - m) γ t * Real.exp (t * m) := by
    simpa only [sub_add_cancel] using
      (mgf_add_const (X := fun Z => f Z - m) (μ := γ) (t := t) m)
  change mgf f γ t ≤ Real.exp (t * m + t ^ 2 * σ ^ 2 / 2)
  rw [he]
  calc
    _ ≤ Real.exp (σ ^ 2 * t ^ 2 / 2) * Real.exp (t * m) :=
      mul_le_mul_of_nonneg_right (hsg.mgf_le t) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

open scoped Matrix.Norms.L2Operator in
/-- The native Gaussian maximum-eigenvalue MGF after an arbitrary scalar
rescaling has weak variance multiplied by the squared scale. -/
theorem hasSubgaussianMGF_lambdaMax_add_smul_gaussian
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) (c : ℝ) :
    HasSubgaussianMGF
      (fun Z => lambdaMax (D + c • Z) - ∫ H, lambdaMax (D + c • H) ∂γ)
      ⟨c ^ 2 * σ ^ 2, mul_nonneg (sq_nonneg c) (sq_nonneg σ)⟩ γ := by
  let L : M →L[ℝ] M := c • ContinuousLinearMap.id ℝ _
  have hL (Z : M) : L Z = c • Z := rfl
  have hhermL : ∀ᵐ Z ∂γ.map L, Z.IsHermitian := by
    apply (ae_map_iff L.continuous.measurable.aemeasurable ?_).mpr
    · filter_upwards [hHerm] with Z hZ
      simpa only [hL] using hZ.smul (IsSelfAdjoint.all c)
    · exact (isClosed_eq (by fun_prop : Continuous (fun Z : M => Zᴴ)) continuous_id).measurableSet
  have hmeanL : (∫ Z, Z ∂γ.map L) = 0 := by
    have hm := integral_map (μ := γ) (φ := L) (f := fun Z : M => Z)
      L.continuous.measurable.aemeasurable aestronglyMeasurable_id
    have hli := L.integral_comp_comm (IsGaussian.integrable_id (μ := γ))
    simp only [id_eq] at hli
    rw [hm, hli, hmean, map_zero]
  have hvarL : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ.map L] ≤ (|c| * σ) ^ 2 := by
    intro u hu
    have hq : (fun Z : M => (quadForm (L Z) u).re) =
        fun Z => c * (quadForm Z u).re := by
      ext Z
      simp only [hL, quadForm, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hqm : Measurable (fun Z : M => (quadForm Z u).re) := by
      simp only [quadForm, dotProduct, Matrix.mulVec]
      fun_prop
    rw [variance_map hqm.aemeasurable L.continuous.measurable.aemeasurable]
    change Var[fun Z => (quadForm (L Z) u).re; γ] ≤ _
    rw [hq, variance_const_mul]
    simpa only [mul_pow, sq_abs] using
      mul_le_mul_of_nonneg_left (hvariance u hu) (sq_nonneg c)
  have hsg := hasSubgaussianMGF_lambdaMax_add_gaussian (γ.map L) D hD hhermL hmeanL
    (mul_nonneg (abs_nonneg c) hσ) hvarL
  have hi := integrable_lambdaMax_add_gaussian (γ.map L) D hD hhermL hmeanL
    (mul_nonneg (abs_nonneg c) hσ) hvarL
  have hmi := integral_map L.continuous.measurable.aemeasurable hi.aestronglyMeasurable
  have hpull := HasSubgaussianMGF.of_map L.continuous.measurable.aemeasurable hsg
  rw [hmi] at hpull
  simpa only [Function.comp_def, hL, mul_pow, sq_abs] using hpull

open scoped Matrix.Norms.L2Operator in
/-- The exponential moment of a rescaled shifted Gaussian maximum eigenvalue
is controlled by its actual mean and squared-scale weak variance. -/
theorem integral_exp_lambdaMax_add_smul_gaussian_le
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) (c : ℝ) :
    (∫ Z, Real.exp (lambdaMax (D + c • Z)) ∂γ) ≤
      Real.exp ((∫ Z, lambdaMax (D + c • Z) ∂γ) + c ^ 2 * σ ^ 2 / 2) := by
  let f : M → ℝ := fun Z => lambdaMax (D + c • Z)
  let m : ℝ := ∫ Z, f Z ∂γ
  have hsg := hasSubgaussianMGF_lambdaMax_add_smul_gaussian γ D hD hHerm hmean hσ hvariance c
  have he : mgf f γ 1 = mgf (fun Z => f Z - m) γ 1 * Real.exp m := by
    simpa only [sub_add_cancel, one_mul] using
      (mgf_add_const (X := fun Z => f Z - m) (μ := γ) (t := 1) m)
  have hgoal : mgf f γ 1 ≤ Real.exp (m + c ^ 2 * σ ^ 2 / 2) := by
    rw [he]
    have hh := hsg.mgf_le 1
    simp only [one_pow, mul_one] at hh
    calc
      _ ≤ Real.exp (c ^ 2 * σ ^ 2 / 2) * Real.exp m :=
        mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  simpa only [mgf, one_mul] using hgoal

open scoped Matrix.Norms.L2Operator in
/-- The trace exponential of a shifted scaled Gaussian matrix is bounded in
expectation by dimension times the exponential of its actual expected maximum
eigenvalue and half its weak quadratic variance. -/
theorem integral_traceExp_add_smul_gaussian_le_exp_mean
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) (c : ℝ) :
    (∫ Z, traceExp (D + c • Z) ∂γ) ≤
      (Fintype.card n : ℝ) *
        Real.exp ((∫ Z, lambdaMax (D + c • Z) ∂γ) + c ^ 2 * σ ^ 2 / 2) := by
  have hsg := hasSubgaussianMGF_lambdaMax_add_smul_gaussian γ D hD hHerm hmean hσ hvariance c
  have hexp := (hsg.integrable_exp_mul 1).mul_const
    (Real.exp (∫ Z, lambdaMax (D + c • Z) ∂γ))
  have hi : Integrable (fun Z => Real.exp (lambdaMax (D + c • Z))) γ := by
    simpa only [one_mul, ← Real.exp_add, sub_add_cancel] using hexp
  have ht := integrable_traceExp_add_smul_gaussian γ D hD hHerm c
  have hmono := integral_mono_ae ht (hi.const_mul (Fintype.card n : ℝ))
    (hHerm.mono fun Z hZ => traceExp_le_card_mul_exp_lambdaMax _
      (hD.add (hZ.smul (IsSelfAdjoint.all c))))
  rw [integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (integral_exp_lambdaMax_add_smul_gaussian_le γ D hD hHerm hmean hσ hvariance c)
    (Nat.cast_nonneg _))

end NLAlib
