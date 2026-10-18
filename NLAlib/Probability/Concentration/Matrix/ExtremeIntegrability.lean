import NLAlib.Probability.Concentration.Matrix.ExpectExtremaIntegrable
import NLAlib.Matrix.Basic.RealCoordinates
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrability of largest Hermitian eigenvalues

Finite matrix first moments control both signs of the largest eigenvalue by
the spectral norm. Full-coordinate second moments therefore suffice for the
shifted, rescaled and finite-sum observables in Gaussian-proxy expectation
bounds, without any Gaussian or negative-exponential-moment hypothesis.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n Ω : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [MeasurableSpace Ω]
  {μ : Measure Ω}

open scoped Matrix.Norms.L2Operator in
/-- Integrability of all full real entry coordinates yields integrability of
the largest eigenvalue for an almost surely Hermitian matrix. -/
theorem integrable_lambdaMax_of_integrable_matrixRealCoordinates
    {X : Ω → Matrix n n ℂ}
    (hX : Integrable (fun ω => matrixRealCoordinates (X ω)) μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    Integrable (fun ω => lambdaMax (X ω)) μ := by
  let C := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  have hi := C.symm.toContinuousLinearMap.integrable_comp hX
  have he (ω : Ω) : C.symm (matrixRealCoordinates (X ω)) = X ω :=
    matrixRealCoordinates.symm_apply_apply (X ω)
  have hmatrix : Integrable X μ := by
    simpa only [ContinuousLinearEquiv.coe_coe, he] using hi
  exact integrable_lambdaMax_of_integrable hmatrix hHerm

open scoped Matrix.Norms.L2Operator in
/-- Finite second entry moments suffice for the largest eigenvalue at every
fixed Hermitian shift and arbitrary real scale. No lower spectral bound or
negative exponential moments are required. -/
theorem integrable_lambdaMax_add_smul_of_memLp_matrixRealCoordinates [IsFiniteMeasure μ]
    (D : Matrix n n ℂ) (hD : D.IsHermitian) {X : Ω → Matrix n n ℂ}
    (hX : MemLp (fun ω => matrixRealCoordinates (X ω)) 2 μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (c : ℝ) :
    Integrable (fun ω => lambdaMax (D + c • X ω)) μ := by
  let C := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  have hi := C.symm.toContinuousLinearMap.integrable_comp (hX.integrable one_le_two)
  have he (ω : Ω) : C.symm (matrixRealCoordinates (X ω)) = X ω :=
    matrixRealCoordinates.symm_apply_apply (X ω)
  have hmatrix : Integrable X μ := by
    simpa only [ContinuousLinearEquiv.coe_coe, he] using hi
  apply integrable_lambdaMax_of_integrable ((integrable_const D).add (hmatrix.smul c))
  exact hHerm.mono fun ω hω => hD.add (hω.smul (IsSelfAdjoint.all c))

open scoped Matrix.Norms.L2Operator in
/-- A finite real linear combination of almost surely Hermitian matrices with
finite second entry moments has an integrable largest eigenvalue after a
fixed Hermitian shift. Independence is unnecessary for this moment assertion. -/
theorem integrable_lambdaMax_add_sum_smul_of_memLp_matrixRealCoordinates
    [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (D : Matrix n n ℂ) (hD : D.IsHermitian) (c : ι → ℝ)
    (X : ι → Ω → Matrix n n ℂ)
    (hX : ∀ i, MemLp (fun ω => matrixRealCoordinates (X i ω)) 2 μ)
    (hHerm : ∀ i, ∀ᵐ ω ∂μ, (X i ω).IsHermitian) :
    Integrable (fun ω => lambdaMax (D + ∑ i, c i • X i ω)) μ := by
  let C := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  have hmatrix (i : ι) : Integrable (X i) μ := by
    have hi := C.symm.toContinuousLinearMap.integrable_comp ((hX i).integrable one_le_two)
    have he (ω : Ω) : C.symm (matrixRealCoordinates (X i ω)) = X i ω :=
      matrixRealCoordinates.symm_apply_apply (X i ω)
    simpa only [ContinuousLinearEquiv.coe_coe, he] using hi
  have hsum : Integrable (fun ω => D + ∑ i, c i • X i ω) μ :=
    (integrable_const D).add
      (integrable_finsetSum Finset.univ (fun i _ => (hmatrix i).smul (c i)))
  apply integrable_lambdaMax_of_integrable hsum
  filter_upwards [ae_all_iff.mpr hHerm] with ω hω
  exact hD.add (isSelfAdjoint_sum _ (fun i _ => (hω i).smul (IsSelfAdjoint.all (c i))))

end NLAlib
