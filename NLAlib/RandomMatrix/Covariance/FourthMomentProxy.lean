import NLAlib.RandomMatrix.Covariance.FourthMomentAggregate
import NLAlib.Probability.Concentration.Matrix.GaussianProxyExistence

/-!
# The actual Gaussian proxy of the empirical covariance defect

Finite fourth observation moments and isotropy supply the full covariance,
centering, and deterministic one-sided hypotheses of Gaussian replacement.
Source: Tropp (2026), Section 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder
namespace NLAlib
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
local notation "M" => Matrix d d ℂ

open scoped Matrix.Norms.L2Operator in
/-- The normalized empirical covariance defect has an actual centered
Hermitian Gaussian proxy with matching full-entry covariance and the sharp
one-sided upper tail. No proxy-existence premise is imposed.
Source: Tropp (2026), Theorems 1.1 and 3.3. -/
theorem exists_gaussian_covarianceDefect_pi
    (μ : Measure (d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : (d → ℝ) → d → ℝ) 4 μ)
    (hisotropic : (∫ x, vecMulVec x x ∂μ) = (1 : Matrix d d ℝ))
    {N : ℕ} (hN : 0 < N) :
    ∃ γ : Measure M, IsGaussian γ ∧ (∫ Z, Z ∂γ) = 0 ∧
      (∀ᵐ Z ∂γ, Z.IsHermitian) ∧
      (∀ a b, cov[fun x : Fin N → d → ℝ => matrixRealCoordinates
        (realMatrixComplexification (1 - sampleCovariance x) : M) a,
        fun x => matrixRealCoordinates (realMatrixComplexification (1 - sampleCovariance x) : M) b;
        Measure.pi (fun _ : Fin N => μ)] =
          cov[fun Z => matrixRealCoordinates Z a, fun Z => matrixRealCoordinates Z b; γ]) ∧
      ∀ s : ℝ, 0 ≤ s → (Measure.pi (fun _ : Fin N => μ)).real
        {x | (∫ Z, lambdaMax Z ∂γ) +
          Real.sqrt (2 * gaussianProxyVariance γ (N : ℝ)⁻¹ * s) + ((N : ℝ)⁻¹ / 3) * s <
          lambdaMax (realMatrixComplexification (1 - sampleCovariance x) : M)} ≤
            (Fintype.card d : ℝ) * Real.exp (-s) := by
  let F : (d → ℝ) → M := fun x => realMatrixComplexification (covarianceDefectTerm N x)
  have hF : Measurable F := by
    dsimp [F, covarianceDefectTerm]
    fun_prop
  let ν : Fin N → Measure M := fun _ => μ.map F
  let P := Measure.pi (fun _ : Fin N => μ)
  let W : Fin N → (Fin N → d → ℝ) → M := fun i x => F (x i)
  have hW (i : Fin N) : HasLaw (W i) (ν i) P := by
    exact (show HasLaw F (μ.map F) μ from ⟨hF.aemeasurable, rfl⟩).fun_comp
      (measurePreserving_eval (fun _ : Fin N => μ) i).hasLaw
  have hind : iIndepFun W P := iIndepFun_pi (fun _ => hF.aemeasurable)
  have hν2 (i : Fin N) : MemLp (matrixRealCoordinates : M → ((d × d) ⊕ (d × d) → ℝ)) 2 (ν i) := by
    apply (memLp_map_measure_iff continuous_matrixRealCoordinates.aestronglyMeasurable hF.aemeasurable).mpr
    exact memLp_two_matrixRealCoordinates_complex_covarianceDefectTerm hμ N
  have hνmean (i : Fin N) : (∫ Z, Z ∂ν i) = 0 := by
    have he := (show HasLaw F (ν i) μ from ⟨hF.aemeasurable, rfl⟩).integral_eq
    exact he.symm.trans (integral_complex_covarianceDefectTerm_eq_zero
      (hμ.mono_exponent (by norm_num)) hisotropic N)
  have hνHerm (i : Fin N) : ∀ᵐ Z ∂ν i, Z.IsHermitian := by
    apply (ae_map_iff hF.aemeasurable
      (isClosed_eq (by fun_prop : Continuous (fun A : M => Aᴴ)) continuous_id).measurableSet).mpr
    exact Filter.Eventually.of_forall fun x =>
      (isHermitian_covarianceDefectTerm N x).map (algebraMap ℝ ℂ) (fun r => by simp)
  have hνbound (i : Fin N) : ∀ᵐ Z ∂ν i, Z ≤ (N : ℝ)⁻¹ • (1 : M) := by
    apply (ae_map_iff hF.aemeasurable
      (isClosed_le continuous_id continuous_const).measurableSet).mpr
    filter_upwards [] with x
    have he : (realMatrixComplexification (covarianceDefectTerm N x) : M) ≤
        realMatrixComplexification ((N : ℝ)⁻¹ • (1 : Matrix d d ℝ)) :=
      (realMatrixComplexification_le_iff _ _).mpr (covarianceDefectTerm_le N x)
    simpa only [map_smul, map_one, F, id_eq] using he
  obtain ⟨γ, hγ, hγmean, hγHerm, hγcov, htail⟩ :=
    exists_isGaussian_integral_lambdaMax_sum_le_and_measure_gt_le_of_hasLaw
      W ν hW hind hν2 hνmean hνHerm (show 0 ≤ (N : ℝ)⁻¹ by positivity) hνbound
  have hsum (x : Fin N → d → ℝ) :
      (∑ i, W i x) = (realMatrixComplexification (1 - sampleCovariance x) : M) := by
    change (∑ i, realMatrixComplexification (covarianceDefectTerm N (x i))) = _
    rw [← map_sum, sum_covarianceDefectTerm hN]
  refine ⟨γ, hγ, hγmean, hγHerm, ?_, ?_⟩
  · simpa only [hsum] using hγcov
  · simpa only [zero_add, add_zero, hsum] using (htail 0 isHermitian_zero).2.1

end NLAlib
