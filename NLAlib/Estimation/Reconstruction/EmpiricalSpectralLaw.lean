import NLAlib.Matrix.Functions.CFCQuadratic
import NLAlib.Matrix.Spectral.TraceEigenvalues
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Estimation.Reconstruction.ChebyshevRegression

/-!
# Empirical spectral probability laws

Every eigenvalue is counted with its algebraic multiplicity. Finite atomic
integration agrees with normalized trace, so the law and its scaling identity
are independent of the chosen spectral basis.
Source: the finite spectral theorem; MMRS, Section 5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix Polynomial
open scoped ENNReal NNReal
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The empirical eigenvalue law of a real symmetric matrix. Its total mass
is one in positive dimension and zero in dimension zero. -/
def empiricalSpectralLaw {A : Matrix n n ℝ} (hA : A.IsHermitian) : Measure ℝ :=
  ((Fintype.card n : ℝ≥0)⁻¹) • ∑ i, Measure.dirac (hA.eigenvalues i)

instance empiricalSpectralLaw_isFiniteMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    IsFiniteMeasure (empiricalSpectralLaw hA) := by
  unfold empiricalSpectralLaw
  infer_instance

instance empiricalSpectralLaw_isProbabilityMeasure [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : IsProbabilityMeasure (empiricalSpectralLaw hA) := by
  constructor
  simp only [empiricalSpectralLaw, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [ENNReal.smul_def]
  simp only [smul_eq_mul]
  rw [ENNReal.coe_inv (show (Fintype.card n : ℝ≥0) ≠ 0 by
    exact_mod_cast Fintype.card_ne_zero (α := n)), ENNReal.coe_natCast]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero (α := n)) (by simp)

/-- Every test function is integrable against the finite atomic law. -/
theorem integrable_empiricalSpectralLaw {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Integrable f (empiricalSpectralLaw hA) := by
  unfold empiricalSpectralLaw
  apply Integrable.smul_measure_nnreal
  apply integrable_finsetSum_measure.mpr
  exact fun i _ => integrable_dirac (by simp)

/-- Integration against the spectral law is the normalized finite eigenvalue sum. -/
theorem integral_empiricalSpectralLaw {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalSpectralLaw hA = (∑ i, f (hA.eigenvalues i)) / Fintype.card n := by
  rw [empiricalSpectralLaw, integral_smul_nnreal_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_natCast, smul_eq_mul]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The spectral law integrates arbitrary functions to normalized functional
calculus trace. No continuity assumption is needed on a finite spectrum. -/
theorem integral_empiricalSpectralLaw_eq_trace_cfc {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalSpectralLaw hA = (cfc f A).trace / Fintype.card n := by
  rw [integral_empiricalSpectralLaw, hA.cfc_eq, Matrix.IsHermitian.cfc,
    trace_conjStarAlgAut, Matrix.trace_diagonal]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- Exact matrix interpretation of the moments used by simplex recovery. -/
theorem chebyshevMoments_empiricalSpectralLaw {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (j : ℕ) :
    chebyshevMoments (empiricalSpectralLaw hA) j =
      (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n := by
  rw [chebyshevMoments, integral_empiricalSpectralLaw_eq_trace_cfc,
    cfc_polynomial _ _ hA.isSelfAdjoint]

open scoped Matrix.Norms.L2Operator in
/-- A spectral-norm contraction has its entire empirical law in `[-1,1]`. -/
theorem ae_mem_Icc_empiricalSpectralLaw {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hbound : specNorm A ≤ 1) :
    ∀ᵐ x ∂empiricalSpectralLaw hA, x ∈ Set.Icc (-1 : ℝ) 1 := by
  have he (i : n) : hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    calc
      _ = ‖hA.eigenvalues i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖hA.eigenvalues‖ := norm_le_pi_norm _ _
      _ = specNorm A := hA.specNorm_eq_norm_eigenvalues.symm
      _ ≤ 1 := hbound
  unfold empiricalSpectralLaw
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  simpa using he i

open scoped Matrix.Norms.L2Operator in
/-- Dilation of a symmetric matrix dilates its empirical spectral law. -/
theorem empiricalSpectralLaw_smul {A : Matrix n n ℝ} (hA : A.IsHermitian) (S : ℝ) :
    empiricalSpectralLaw (hA.smul (show IsSelfAdjoint S by simp [IsSelfAdjoint])) =
      (empiricalSpectralLaw hA).map (fun x => S * x) := by
  apply Measure.ext
  intro E hE
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (empiricalSpectralLaw (hA.smul (show IsSelfAdjoint S by simp [IsSelfAdjoint]))).real E =
    ((empiricalSpectralLaw hA).map (fun x => S * x)).real E
  rw [← integral_indicator_one hE, ← integral_indicator_one hE]
  change (∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂empiricalSpectralLaw _) =
    ∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂(empiricalSpectralLaw hA).map (fun x => S * x)
  rw [integral_map (by fun_prop : AEMeasurable (fun x : ℝ => S * x) (empiricalSpectralLaw hA))
      ((measurable_const.indicator hE).aestronglyMeasurable),
    integral_empiricalSpectralLaw_eq_trace_cfc, integral_empiricalSpectralLaw_eq_trace_cfc]
  rw [cfc_comp_const_mul S _ A
    (((spectrum ℝ A).toFinite.image _).continuousOn _) hA.isSelfAdjoint]

end NLAlib
