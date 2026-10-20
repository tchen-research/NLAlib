import NLAlib.Matrix.Functions.KTransformSubsolution
import NLAlib.Matrix.Functions.KTransformOrderedContinuation
import NLAlib.Matrix.Functions.KTransformGlobalInjectivity
import NLAlib.Matrix.Functions.KTransformPotentialFrechet
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The actual K-potential normalization at negative infinity -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The genuine integrated logarithmic determinant is continuous at zero,
by joint smoothness near its actual compact sample-support fibre. -/
theorem continuousAt_integral_matrixKLogDetKernel_zero
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support) :
    ContinuousAt (fun X : M => ∫ T : selfAdjoint M, matrixKLogDetKernel X T.val ∂ν) 0 := by
  have hval : ContDiff ℝ 1 (fun T : selfAdjoint M => (T : M)) :=
    (selfAdjoint.submodule ℝ M).subtypeL.contDiff
  have hA : ContDiff ℝ 1 (fun p : M × selfAdjoint M => 1 + p.2.val * p.1) :=
    contDiff_const.add ((hval.comp contDiff_snd).mul contDiff_fst)
  have hdet : ContDiff ℝ 1 (fun p : M × selfAdjoint M => (1 + p.2.val * p.1).det.re) :=
    Complex.reCLM.contDiff.comp ((Matrix.contDiff_det 1).comp hA)
  let U : Set (M × selfAdjoint M) := {p | (1 + p.2.val * p.1).det.re ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hdet.continuous continuous_const
  have hF : ContDiffOn ℝ 1
      (fun p : M × selfAdjoint M => Real.log (1 + p.2.val * p.1).det.re) U :=
    hdet.contDiffOn.log (fun _ hp => hp)
  have hp (T : selfAdjoint M) (_hT : T ∈ ν.support) : ((0 : M), T) ∈ U := by simp [U]
  exact (differentiableAt_integral_of_contDiffOn_compact_support ν hν
    (fun p : M × selfAdjoint M => Real.log (1 + p.2.val * p.1).det.re) U hU hF 0 hp).continuousAt

/-- Positivity and order of the genuine resolvent sandwich control its
actual spectral norm uniformly on an ordered positive sample-gap cone. -/
theorem norm_integral_matrixKInverseSandwich_le_of_le
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (Y Z : M) (hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef)
    (hgapZ : ∀ T ∈ ν.support, (Z + T.val).PosDef) (hYZ : Y ≤ Z) :
    ‖∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν‖ ≤
      ‖∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν‖ := by
  have hiY := integrable_matrixKInverseSandwich ν hν Y hgapY
  have hiZ := integrable_matrixKInverseSandwich ν hν Z hgapZ
  have hnonneg : 0 ≤ ∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ν.support_mem_ae] with T hT
    have hTH : T.val.IsHermitian := T.property
    have hp := (hgapZ T hT).inv.posSemidef.mul_mul_conjTranspose_same T.val
    exact Matrix.nonneg_iff_posSemidef.mpr (by simpa only [hTH.eq] using hp)
  apply CStarAlgebra.norm_le_norm_of_nonneg_of_le hnonneg
  apply integral_mono_ae hiZ hiY
  filter_upwards [ν.support_mem_ae] with T hT
  have hle : Y + T.val ≤ Z + T.val := by
    simpa only [add_comm] using add_le_add_right hYZ T.val
  have hinv : (Z + T.val)⁻¹ ≤ (Y + T.val)⁻¹ := by
    simpa only [← Matrix.nonsing_inv_eq_ringInverse] using
      CStarAlgebra.ringInverse_le_ringInverse hle (hgapY T hT).isStrictlyPositive
  have hTH : T.val.IsHermitian := T.property
  have hp := (Matrix.le_iff.mp hinv).mul_mul_conjTranspose_same T.val
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, hTH.eq] using hp

/-- An actual ordered scalar K solution differs from its leading inverse
term by a uniform bound supplied by the original sample law and seed. -/
theorem norm_inverse_add_scalar_le_of_matrixKTransform_eq
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (Y Z : M) (hZ : Z.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef)
    (hgapZ : ∀ T ∈ ν.support, (Z + T.val).PosDef) (hYZ : Y ≤ Z)
    (u : ℝ) (hK : matrixKTransform ν α Z⁻¹ = (u : ℂ) • 1) :
    ‖Z + (α * u) • (1 : M)‖ ≤ α *
      (‖∫ T : selfAdjoint M, T.val ∂ν‖ +
        ‖∫ T : selfAdjoint M, T.val * (Y + T.val)⁻¹ * T.val ∂ν‖) := by
  have hfix := matrixKInverseIteration_eq_add_transform ν hν α hα.ne' ((u : ℂ) • 1) Z hZ hgapZ
  rw [hK, sub_self, smul_zero, add_zero] at hfix
  have he : Z + (α * u) • (1 : M) = α •
      ((∫ T : selfAdjoint M, T.val ∂ν) -
        (∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν)) := by
    have hsm : (u : ℂ) • (1 : M) = u • (1 : M) :=
      IsScalarTower.algebraMap_smul ℂ u (1 : M)
    rw [matrixKInverseIteration, hsm] at hfix
    calc
      _ = (α • ((∫ T : selfAdjoint M, T.val ∂ν) -
          (∫ T : selfAdjoint M, T.val * (Z + T.val)⁻¹ * T.val ∂ν) - u • 1)) +
          (α * u) • (1 : M) := congrArg (fun W : M => W + (α * u) • 1) hfix.symm
      _ = _ := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
  apply mul_le_mul_of_nonneg_left _ hα.le
  have hn := norm_integral_matrixKInverseSandwich_le_of_le ν hν Y Z hgapY hgapZ hYZ
  exact (norm_sub_le _ _).trans (by linarith)

variable [Nonempty n]

/-- Actual scalar stable solutions have a uniform inverse asymptotic
error on a negative ray, constructed by genuine ordered continuation
and native global uniqueness. -/
theorem exists_eventually_norm_inverse_add_scalar_le
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : ℝ → M)
    (hsol : ∀ᶠ u : ℝ in atBot, S u ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (S u) = (u : ℂ) • 1) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atBot, ‖(S u)⁻¹ + (α * u) • (1 : M)‖ ≤ C := by
  obtain ⟨u₀, hS₀, hK₀⟩ := hsol.exists
  obtain ⟨Y, hY, hYS⟩ : ∃ Y : selfAdjoint M,
      Y ∈ matrixKInverseStableDomain ν α ∧ Y.val⁻¹ = S u₀ := by
    have hmem : S u₀ ∈ (fun Y : selfAdjoint M => Y.val⁻¹) ''
        matrixKInverseStableDomain ν α := by
      rw [image_inverse_matrixKInverseStableDomain ν hν α hα]
      exact hS₀
    exact hmem
  refine ⟨α * (‖∫ T : selfAdjoint M, T.val ∂ν‖ +
    ‖∫ T : selfAdjoint M, T.val * (Y.val + T.val)⁻¹ * T.val ∂ν‖), ?_⟩
  filter_upwards [hsol, eventually_lt_atBot u₀] with u hu huu
  have hH : (((u₀ - u : ℝ) : ℂ) • (1 : M)).PosDef := by
    rw [show (((u₀ - u : ℝ) : ℂ) • (1 : M)) = (u₀ - u) • (1 : M) from
      IsScalarTower.algebraMap_smul ℂ (u₀ - u) (1 : M)]
    exact Matrix.PosDef.one.smul (sub_pos.mpr huu)
  obtain ⟨Z, hZY, hZ, hKZ⟩ :=
    exists_ordered_matrixKTransform_inverse_solution ν hν α hα Y hY
      (((u₀ - u : ℝ) : ℂ) • (1 : M)) hH
  have hKZ' : matrixKTransform ν α Z.val⁻¹ = (u : ℂ) • (1 : M) := by
    rw [hYS, hK₀, Complex.ofReal_sub, sub_smul] at hKZ
    convert hKZ using 1
    module
  have hSZ : S u = Z.val⁻¹ := by
    have hZst : Z.val⁻¹ ∈ matrixKStableDomain ν α := by
      rw [← image_inverse_matrixKInverseStableDomain ν hν α hα]
      exact ⟨Z, hZ, rfl⟩
    exact (matrixKTransform_eq_iff_eq_of_quadratic_pos ν hν α hα (S u) Z.val⁻¹
      hu.1.1 hZst.1 hu.1.2.1 hZst.2.1 hu.1.2.2 hZst.2.2).mp (hu.2.trans hKZ'.symm)
  rw [hSZ, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hZ.1.isUnit)]
  exact norm_inverse_add_scalar_le_of_matrixKTransform_eq ν hν α hα Y.val Z.val hZ.1
    hY.2.1 hZ.2.1 (Matrix.le_iff.mpr hZY.posSemidef) u hKZ'

/-- The actual stable scalar K branch has its native matrix normalization
at negative infinity. Neither normalization nor a resolvent bound is assumed. -/
theorem tendsto_neg_mul_smul_matrixKTransform_scalar_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : ℝ → M)
    (hsol : ∀ᶠ u : ℝ in atBot, S u ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (S u) = (u : ℂ) • 1) :
    Tendsto (fun u : ℝ => (-α * u) • S u) atBot (𝓝 (1 : M)) := by
  obtain ⟨C, hC⟩ := exists_eventually_norm_inverse_add_scalar_le ν hν α hα S hsol
  have hinv : Tendsto (fun u : ℝ => (-α * u)⁻¹) atBot (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atBot_of_neg (neg_neg_of_pos hα))
  have hzero : Tendsto (fun u : ℝ => (-α * u)⁻¹ •
      ((S u)⁻¹ + (α * u) • (1 : M))) atBot (𝓝 (0 : M)) :=
    hinv.zero_smul_isBoundedUnder_le ⟨C, hC⟩
  have hnorm : Tendsto (fun u : ℝ => (-α * u)⁻¹ • (S u)⁻¹) atBot (𝓝 (1 : M)) := by
    have ht := hzero.add_const (1 : M)
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with u hu
    have hne : -α * u ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hα.ne') hu.ne
    have he : (-α * u)⁻¹ * (α * u) = -1 := by field_simp [hα.ne', hu.ne]
    simp only [smul_add, smul_smul, he, neg_one_smul]
    abel
  have hcont : ContinuousAt (fun X : M => X⁻¹) (1 : M) :=
    (hasFDerivAt_matrixInverse (1 : M) isUnit_one).continuousAt
  have hlim : Tendsto (fun u : ℝ => ((-α * u)⁻¹ • (S u)⁻¹)⁻¹) atBot (𝓝 (1 : M)) := by
    simpa only [inv_one, Function.comp_def] using hcont.tendsto.comp hnorm
  apply hlim.congr'
  filter_upwards [hsol, eventually_lt_atBot (0 : ℝ)] with u hu hup
  have hne : -α * u ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hα.ne') hup.ne
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hu.1.1.isUnit), mul_inv_cancel₀ hne, one_smul]

/-- Actual scalar stable K solutions tend to zero at negative infinity. -/
theorem tendsto_matrixKTransform_scalar_solution_zero
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : ℝ → M)
    (hsol : ∀ᶠ u : ℝ in atBot, S u ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (S u) = (u : ℂ) • 1) :
    Tendsto S atBot (𝓝 (0 : M)) := by
  have hnorm := tendsto_neg_mul_smul_matrixKTransform_scalar_solution ν hν α hα S hsol
  have hinv : Tendsto (fun u : ℝ => (-α * u)⁻¹) atBot (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atBot_of_neg (neg_neg_of_pos hα))
  have hzero : Tendsto (fun u : ℝ => (-α * u)⁻¹ • ((-α * u) • S u))
      atBot (𝓝 (0 : M)) := by simpa only [zero_smul] using hinv.smul hnorm
  apply hzero.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with u hu
  rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hα.ne') hu.ne), one_smul]

/-- The true finite-matrix variational potential has exactly the native
logarithmic-potential normalization at negative infinity. The scalar
solutions are actual stable K solutions; their matrix asymptotics and
all logarithmic determinant limits are proved from the original law.
Source: Montanari--Saeed (2026), Theorem 2.
atlas: block-wishart-log-potential (partial) -/
theorem tendsto_matrixKPotential_scalar_solution_sub_log
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : ℝ → M)
    (hsol : ∀ᶠ u : ℝ in atBot, S u ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (S u) = (u : ℂ) • 1) :
    Tendsto (fun u : ℝ => matrixKPotential ν α u (S u) / Fintype.card n - Real.log (-u))
      atBot (𝓝 (0 : ℝ)) := by
  let Z : ℝ → M := fun u => (-α * u) • S u
  have hZ : Tendsto Z atBot (𝓝 (1 : M)) :=
    tendsto_neg_mul_smul_matrixKTransform_scalar_solution ν hν α hα S hsol
  have hSzero := tendsto_matrixKTransform_scalar_solution_zero ν hν α hα S hsol
  have hI : Tendsto (fun u : ℝ => ∫ T : selfAdjoint M, matrixKLogDetKernel (S u) T.val ∂ν)
      atBot (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, matrixKLogDetKernel, Matrix.mul_zero, add_zero,
      Matrix.det_one, Complex.one_re, Real.log_one, integral_zero] using
      (continuousAt_integral_matrixKLogDetKernel_zero ν hν).tendsto.comp hSzero
  have hdet : Tendsto (fun u : ℝ => (Z u).det.re) atBot (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.det_one, Complex.one_re] using
      (Complex.continuous_re.comp (continuous_id.matrix_det : Continuous (fun X : M => X.det))).tendsto
        (1 : M) |>.comp hZ
  have hlog : Tendsto (fun u : ℝ => Real.log (Z u).det.re) atBot (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one] using hdet.log one_ne_zero
  have htrace : Tendsto (fun u : ℝ => (Z u).trace.re) atBot (𝓝 (Fintype.card n : ℝ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.trace_one, Complex.natCast_re] using
      (Complex.continuous_re.comp (continuous_id.matrix_trace : Continuous (fun X : M => X.trace))).tendsto
        (1 : M) |>.comp hZ
  have hlim : Tendsto (fun u : ℝ => ((Z u).trace.re - (Fintype.card n : ℝ) +
      α * (∫ T : selfAdjoint M, matrixKLogDetKernel (S u) T.val ∂ν) -
      Real.log (Z u).det.re) / Fintype.card n) atBot (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, mul_zero, add_zero, sub_zero, zero_div] using
      (((htrace.sub_const (Fintype.card n : ℝ)).add (hI.const_mul α)).sub hlog).div_const
        (Fintype.card n : ℝ)
  apply hlim.congr'
  filter_upwards [hsol, eventually_lt_atBot (0 : ℝ)] with u hu hup
  have hc : 0 < -α * u := mul_pos_of_neg_of_neg (neg_neg_of_pos hα) hup
  have hd : 0 < (S u).det.re := (Complex.pos_iff.mp hu.1.1.det_pos).1
  have hdetZ : (Z u).det.re = (-α * u) ^ Fintype.card n * (S u).det.re := by
    dsimp only [Z]
    rw [Matrix.det_smul_of_tower]
    simp only [Complex.smul_re, smul_eq_mul]
  have hlogZ : Real.log (Z u).det.re =
      (Fintype.card n : ℝ) * (Real.log α + Real.log (-u)) + Real.log (S u).det.re := by
    rw [hdetZ, Real.log_mul (pow_ne_zero _ hc.ne') hd.ne', Real.log_pow]
    rw [show -α * u = α * (-u) by ring,
      Real.log_mul hα.ne' (neg_pos.mpr hup).ne']
  have htrZ : (Z u).trace.re = (-α * u) * (S u).trace.re := by
    simp only [Z, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hk : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  dsimp only [matrixKPotential]
  rw [htrZ, hlogZ]
  field_simp
  ring

end NLAlib
