import NLAlib.Probability.Concentration.Matrix.GaussianProxy

/-!
# Lower Gaussian-proxy bounds from one-sided lower summand bounds

Negating the original summands gives the minimum-eigenvalue comparison under
an independent lower bound. Centered Gaussian symmetry identifies the shifted
Gaussian mean and leaves the actual weak-variance budget unchanged.
Source: Tropp (2026), Corollary 1.3.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- Independent centered Hermitian summands with a one-sided lower bound
satisfy the Gaussian-proxy expectation and lower-tail guarantees for their
minimum eigenvalue. The original upper bound is unnecessary. Strict events
include all zero-parameter endpoints, and a positive lower bound parameter
allows non-strict events. Source: Tropp (2026), Corollary 1.3.
atlas: gaussian-proxy-eigenvalue-comparison -/
theorem integral_lambdaMin_sum_ge_and_measure_lt_le_gaussian_proxy_of_hasLaw
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : Fin N → Ω → M) (ν : Fin N → Measure M)
    (hW : ∀ i, HasLaw (W i) (ν i) P) (hind : iIndepFun W P)
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ H, H ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ H ∂ν i, H.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ i, ∀ᵐ H ∂ν i, (-R) • (1 : M) ≤ H)
    (γ : Measure M) [IsGaussian γ]
    (hγHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hγmean : ∫ Z, Z ∂γ = 0)
    (hγcov : ∀ a b,
      (∑ i, cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ν i]) =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ])
    (D : M) (hD : D.IsHermitian) :
    (∫ Z, lambdaMin (D + Z) ∂γ) -
          Real.sqrt (2 * gaussianProxyVariance γ R * Real.log (Fintype.card n)) -
          (R / 3) * Real.log (Fintype.card n) ≤
        (∫ ω, lambdaMin ((∑ i, W i ω) + D) ∂P) ∧
    (∀ s : ℝ, 0 ≤ s → P.real {ω |
        lambdaMin ((∑ i, W i ω) + D) < (∫ Z, lambdaMin (D + Z) ∂γ) -
          Real.sqrt (2 * gaussianProxyVariance γ R * s) - (R / 3) * s} ≤
            (Fintype.card n : ℝ) * Real.exp (-s)) ∧
    (0 < R → ∀ s : ℝ, 0 ≤ s → P.real {ω |
        lambdaMin ((∑ i, W i ω) + D) ≤ (∫ Z, lambdaMin (D + Z) ∂γ) -
          Real.sqrt (2 * gaussianProxyVariance γ R * s) - (R / 3) * s} ≤
            (Fintype.card n : ℝ) * Real.exp (-s)) := by
  let (i : Fin N) : IsProbabilityMeasure (ν i) :=
    (hW i).isProbabilityMeasure_iff.mp inferInstance
  let η : Fin N → Measure M := fun i => (ν i).map (fun H : M => -H)
  let (i : Fin N) : IsProbabilityMeasure (η i) :=
    (ν i).isProbabilityMeasure_map (by fun_prop)
  have hlaw (i : Fin N) : HasLaw (fun H : M => -H) (η i) (ν i) := ⟨by fun_prop, rfl⟩
  have hWneg (i : Fin N) : HasLaw (fun ω => -W i ω) (η i) P := (hlaw i).comp (hW i)
  have hindneg : iIndepFun (fun i ω => -W i ω) P :=
    hind.comp (fun _ H => -H) (fun _ => by fun_prop)
  have hη2 (i : Fin N) : MemLp (matrixRealCoordinates : M → J → ℝ) 2 (η i) := by
    apply (memLp_map_measure_iff continuous_matrixRealCoordinates.aestronglyMeasurable
      (by fun_prop : AEMeasurable (fun H : M => -H) (ν i))).mpr
    simpa only [Function.comp_def, map_neg, Pi.neg_def] using (hν2 i).neg
  have hηmean (i : Fin N) : (∫ H, H ∂η i) = 0 := by
    have hm := integral_map (μ := ν i) (φ := fun H : M => -H) (f := fun H : M => H)
      (by fun_prop) aestronglyMeasurable_id
    rw [hm, integral_neg, hνmean i, neg_zero]
  have hHermSet : MeasurableSet {H : M | H.IsHermitian} :=
    (isClosed_eq (by fun_prop : Continuous (fun H : M => Hᴴ)) continuous_id).measurableSet
  have hηHerm (i : Fin N) : ∀ᵐ H ∂η i, H.IsHermitian := by
    apply (ae_map_iff (by fun_prop : AEMeasurable (fun H : M => -H) (ν i)) hHermSet).mpr
    exact (hνHerm i).mono fun H hH => hH.neg
  have hηbound (i : Fin N) : ∀ᵐ H ∂η i, H ≤ R • (1 : M) := by
    have hbset : MeasurableSet {H : M | H ≤ R • (1 : M)} :=
      (isClosed_le continuous_id continuous_const).measurableSet
    apply (ae_map_iff (by fun_prop : AEMeasurable (fun H : M => -H) (ν i)) hbset).mpr
    filter_upwards [hbound i] with H hH
    simpa only [neg_smul, neg_neg] using neg_le_neg hH
  have hηcov (i : Fin N) (a b : J) :
      cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; η i] =
        cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ν i] := by
    have he := (hlaw i).covariance_fun_comp
      ((measurable_pi_apply a).comp measurable_matrixRealCoordinates).aemeasurable
      ((measurable_pi_apply b).comp measurable_matrixRealCoordinates).aemeasurable
    simp only [Function.comp_def, map_neg, Pi.neg_apply] at he
    change cov[-(fun H => matrixRealCoordinates H a), -(fun H => matrixRealCoordinates H b); ν i] = _ at he
    simp only [covariance_neg_left, covariance_neg_right, neg_neg] at he
    exact he.symm
  have hcov : ∀ a b,
      (∑ i, cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; η i]) =
        cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ] := by
    intro a b
    simpa only [hηcov] using hγcov a b
  have h := integral_lambdaMax_sum_le_and_measure_gt_le_gaussian_proxy_of_hasLaw
    (fun i ω => -W i ω) η hWneg hindneg hη2 hηmean hηHerm hR hηbound
    γ hγHerm hγmean hcov (-D) hD.neg
  have hmaxneg (ω : Ω) : lambdaMax ((∑ i, -W i ω) + -D) =
      -lambdaMin ((∑ i, W i ω) + D) := by
    have he : (∑ i, -W i ω) + -D = -((∑ i, W i ω) + D) := by
      simp only [Finset.sum_neg_distrib, neg_add]
    rw [he, lambdaMax_neg]
  have hγmax : (∫ Z, lambdaMax (-D + Z) ∂γ) = -(∫ Z, lambdaMin (D + Z) ∂γ) := by
    have hi := integrable_lambdaMax_add_gaussian γ (-D) hD.neg hγHerm hγmean
      (Real.sqrt_nonneg (quadraticWeakVariance γ))
      (fun u hu => variance_re_quadForm_le_sq_sqrt_quadraticWeakVariance_gaussian γ hu)
    have hs := IsGaussian.integral_comp_neg_eq_of_integral_eq_zero γ hγmean
      (fun Z => lambdaMax (-D + Z)) hi
    have he (Z : M) : lambdaMax (-D + -Z) = -lambdaMin (D + Z) := by
      rw [← neg_add, lambdaMax_neg]
    simp_rw [he] at hs
    rw [integral_neg] at hs
    exact hs.symm
  refine ⟨?_, ?_, ?_⟩
  · have he := h.1
    simp_rw [hmaxneg] at he
    rw [integral_neg, hγmax] at he
    linarith
  · intro s hs
    have hset : {ω | lambdaMin ((∑ i, W i ω) + D) < (∫ Z, lambdaMin (D + Z) ∂γ) -
          Real.sqrt (2 * gaussianProxyVariance γ R * s) - (R / 3) * s} =
        {ω | (∫ Z, lambdaMax (-D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
          (R / 3) * s < lambdaMax ((∑ i, -W i ω) + -D)} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hmaxneg, hγmax]
      constructor <;> intro hh <;> linarith
    rw [hset]
    exact h.2.1 s hs
  · intro hRpos s hs
    have hset : {ω | lambdaMin ((∑ i, W i ω) + D) ≤ (∫ Z, lambdaMin (D + Z) ∂γ) -
          Real.sqrt (2 * gaussianProxyVariance γ R * s) - (R / 3) * s} =
        {ω | (∫ Z, lambdaMax (-D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
          (R / 3) * s ≤ lambdaMax ((∑ i, -W i ω) + -D)} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hmaxneg, hγmax]
      constructor <;> intro hh <;> linarith
    rw [hset]
    exact h.2.2 hRpos s hs

end NLAlib
