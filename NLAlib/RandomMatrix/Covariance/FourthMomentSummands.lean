import NLAlib.RandomMatrix.Covariance.WhiteningMoments
import NLAlib.Matrix.Spectral.Complexification
import NLAlib.Matrix.Basic.RealCoordinates

/-!
# One-sided summands of the sample covariance defect

The rank-one observations may be unbounded. Their negative centered versions
nevertheless have the deterministic upper bound needed by Gaussian-proxy
concentration. Source: Tropp (2026), Section 3.3.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder
namespace NLAlib
variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d]
  {μ : Measure Ω}

/-- The normalized real covariance defect contributed by one observation. -/
def covarianceDefectTerm (N : ℕ) (x : d → ℝ) : Matrix d d ℝ :=
  (N : ℝ)⁻¹ • (1 - vecMulVec x x)

/-- A negative centered rank-one observation has the required one-sided
upper bound even when the vector has unbounded norm. -/
theorem covarianceDefectTerm_le (N : ℕ) (x : d → ℝ) :
    covarianceDefectTerm N x ≤ (N : ℝ)⁻¹ • (1 : Matrix d d ℝ) := by
  apply (Matrix.le_iff).mpr
  change ((N : ℝ)⁻¹ • (1 : Matrix d d ℝ) -
    (N : ℝ)⁻¹ • (1 - vecMulVec x x)).PosSemidef
  rw [← smul_sub, sub_sub_cancel]
  exact (posSemidef_vecMulVec_self_star x).smul (by positivity)

/-- Every normalized real covariance defect is symmetric. -/
theorem isHermitian_covarianceDefectTerm (N : ℕ) (x : d → ℝ) :
    (covarianceDefectTerm N x).IsHermitian := by
  exact (isHermitian_one.sub (posSemidef_vecMulVec_self_star x).isHermitian).smul
    (IsSelfAdjoint.all (N : ℝ)⁻¹)

open scoped Matrix.Norms.L2Operator in
/-- Finite fourth vector moments give square integrability of each
normalized negative centered rank-one observation. -/
theorem memLp_two_covarianceDefectTerm [IsProbabilityMeasure μ]
    {X : Ω → d → ℝ} (hX : MemLp X 4 μ) (N : ℕ) :
    MemLp (fun ω => covarianceDefectTerm N (X ω)) 2 μ := by
  exact ((memLp_const (1 : Matrix d d ℝ)).sub
    (memLp_two_vecMulVec_self_of_memLp_four hX)).const_smul ((N : ℝ)⁻¹)

open scoped Matrix.Norms.L2Operator in
/-- Isotropy makes the actual mean of each normalized covariance defect
zero. -/
theorem integral_covarianceDefectTerm_eq_zero [IsProbabilityMeasure μ]
    {X : Ω → d → ℝ} (hX : MemLp X 2 μ)
    (hisotropic : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = (1 : Matrix d d ℝ)) (N : ℕ) :
    (∫ ω, covarianceDefectTerm N (X ω) ∂μ) = 0 := by
  rw [show (fun ω => covarianceDefectTerm N (X ω)) =
      fun ω => (N : ℝ)⁻¹ • ((1 : Matrix d d ℝ) - vecMulVec (X ω) (X ω)) from rfl,
    integral_smul, integral_sub (integrable_const _) (integrable_vecMulVec_self_of_memLp_two hX)]
  simp only [integral_const, probReal_univ, one_smul, hisotropic, sub_self, smul_zero]

omit [Fintype d] in
/-- Summing the normalized covariance defects gives identity minus the
actual empirical covariance. The sample count is positive here. -/
theorem sum_covarianceDefectTerm {N : ℕ} (hN : 0 < N) (X : Fin N → d → ℝ) :
    (∑ i, covarianceDefectTerm N (X i)) = 1 - sampleCovariance X := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [covarianceDefectTerm, ← Finset.smul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul,
    sampleCovariance, star_trivial]

open scoped Matrix.Norms.L2Operator in
/-- Complexifying the normalized real covariance defect preserves its
finite second moments and all full real and imaginary entry moments. -/
theorem memLp_two_matrixRealCoordinates_complex_covarianceDefectTerm
    [IsProbabilityMeasure μ] {X : Ω → d → ℝ} (hX : MemLp X 4 μ) (N : ℕ) :
    MemLp (fun ω => matrixRealCoordinates
      (realMatrixComplexification (covarianceDefectTerm N (X ω)) : Matrix d d ℂ)) 2 μ := by
  let L := (realMatrixComplexification (n := d) (𝕜 := ℂ)).toLinearMap.toContinuousLinearMap
  exact (matrixRealCoordinatesContinuousLinearEquiv (m := d) (n := d)).toContinuousLinearMap.comp_memLp'
    (L.comp_memLp' (memLp_two_covarianceDefectTerm hX N))

open scoped Matrix.Norms.L2Operator in
/-- The actual mean of the complexified isotropic covariance defect is
zero, rather than a separately imposed centering assumption. -/
theorem integral_complex_covarianceDefectTerm_eq_zero [IsProbabilityMeasure μ]
    {X : Ω → d → ℝ} (hX : MemLp X 2 μ)
    (hisotropic : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = (1 : Matrix d d ℝ)) (N : ℕ) :
    (∫ ω, (realMatrixComplexification (covarianceDefectTerm N (X ω)) : Matrix d d ℂ) ∂μ) = 0 := by
  let L := (realMatrixComplexification (n := d) (𝕜 := ℂ)).toLinearMap.toContinuousLinearMap
  have hi : Integrable (fun ω => covarianceDefectTerm N (X ω)) μ :=
    ((integrable_const (1 : Matrix d d ℝ)).sub
      (integrable_vecMulVec_self_of_memLp_two hX)).smul ((N : ℝ)⁻¹)
  change (∫ ω, L (covarianceDefectTerm N (X ω)) ∂μ) = 0
  rw [L.integral_comp_comm hi, integral_covarianceDefectTerm_eq_zero hX hisotropic, map_zero]

end NLAlib
