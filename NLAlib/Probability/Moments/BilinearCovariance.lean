import NLAlib.ForMathlib.Probability.ComplexCovariance
import NLAlib.ForMathlib.Analysis.Matrix.BilinearFunctional
import NLAlib.Matrix.Basic.RealCoordinates

/-!
# Native matrix bilinear moments under full covariance matching

Full real/imaginary entry covariance transports the squared modulus of
arbitrary bilinear observations. Centered observations permit different
matrix means. This preserves the sigma-star geometry of
arXiv:2201.05142v3 without an entry-independence assumption.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {n Ω Ω' : Type*} [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
/-- Actual equal matrix means and full entry covariances preserve squared
bilinear moments for arbitrary complex probes. -/
theorem integral_norm_sq_bilinear_eq_of_matrix_mean_covariance_eq
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → M} {Y : Ω' → M} (hX : MemLp X 2 μ) (hY : MemLp Y 2 ν)
    (hmean : (∫ ω, X ω ∂μ) = ∫ ω, Y ω ∂ν)
    (hcov : ∀ i j : J,
      cov[(fun ω => matrixRealCoordinates (X ω) i),
        (fun ω => matrixRealCoordinates (X ω) j); μ] =
      cov[(fun ω => matrixRealCoordinates (Y ω) i),
        (fun ω => matrixRealCoordinates (Y ω) j); ν]) (v w : n → ℂ) :
    (∫ ω, ‖star v ⬝ᵥ (X ω *ᵥ w)‖ ^ 2 ∂μ) =
      ∫ ω, ‖star v ⬝ᵥ (Y ω *ᵥ w)‖ ^ 2 ∂ν := by
  let E := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  let L := ((Matrix.bilinearCLM v w).restrictScalars ℝ).comp E.symm.toContinuousLinearMap
  have hEX := E.toContinuousLinearMap.comp_memLp' hX
  have hEY := E.toContinuousLinearMap.comp_memLp' hY
  have hm : (∫ ω, E (X ω) ∂μ) = ∫ ω, E (Y ω) ∂ν := by
    calc
      _ = E (∫ ω, X ω ∂μ) := E.toContinuousLinearMap.integral_comp_comm (hX.integrable one_le_two)
      _ = E (∫ ω, Y ω ∂ν) := congrArg E hmean
      _ = _ := (E.toContinuousLinearMap.integral_comp_comm (hY.integrable one_le_two)).symm
  have hL (A : M) : L (E A) = star v ⬝ᵥ (A *ᵥ w) := by
    change star v ⬝ᵥ (E.symm (E A) *ᵥ w) = star v ⬝ᵥ (A *ᵥ w)
    rw [E.symm_apply_apply]
  have h := integral_norm_sq_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    hEX hEY hm hcov L
  change (∫ ω, ‖L (E (X ω))‖ ^ 2 ∂μ) = ∫ ω, ‖L (E (Y ω))‖ ^ 2 ∂ν at h
  simpa only [hL] using h

open scoped Matrix.Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
/-- Full real/imaginary entry covariance alone preserves actual centered
bilinear squared-modulus moments, even when the matrix means differ. -/
theorem integral_norm_sq_centered_bilinear_eq_of_matrix_covariance_eq
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → M} {Y : Ω' → M} (hX : MemLp X 2 μ) (hY : MemLp Y 2 ν)
    (hcov : ∀ i j : J,
      cov[(fun ω => matrixRealCoordinates (X ω) i),
        (fun ω => matrixRealCoordinates (X ω) j); μ] =
      cov[(fun ω => matrixRealCoordinates (Y ω) i),
        (fun ω => matrixRealCoordinates (Y ω) j); ν]) (v w : n → ℂ) :
    (∫ ω, ‖star v ⬝ᵥ ((X ω - ∫ z, X z ∂μ) *ᵥ w)‖ ^ 2 ∂μ) =
      ∫ ω, ‖star v ⬝ᵥ ((Y ω - ∫ z, Y z ∂ν) *ᵥ w)‖ ^ 2 ∂ν := by
  have hXc : MemLp (fun ω => X ω-∫ z, X z ∂μ) 2 μ := hX.sub (memLp_const _)
  have hYc : MemLp (fun ω => Y ω-∫ z, Y z ∂ν) 2 ν := hY.sub (memLp_const _)
  have hm : (∫ ω, (X ω-∫ z, X z ∂μ) ∂μ) =
      ∫ ω, (Y ω-∫ z, Y z ∂ν) ∂ν := by
    rw [integral_sub (hX.integrable one_le_two) (integrable_const _),
      integral_sub (hY.integrable one_le_two) (integrable_const _)]
    simp
  apply integral_norm_sq_bilinear_eq_of_matrix_mean_covariance_eq hXc hYc hm _ v w
  intro i j
  let E := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  have hXi : MemLp (fun ω => matrixRealCoordinates (X ω) i) 2 μ :=
    (E.toContinuousLinearMap.comp_memLp' hX).eval i
  have hXj : MemLp (fun ω => matrixRealCoordinates (X ω) j) 2 μ :=
    (E.toContinuousLinearMap.comp_memLp' hX).eval j
  have hYi : MemLp (fun ω => matrixRealCoordinates (Y ω) i) 2 ν :=
    (E.toContinuousLinearMap.comp_memLp' hY).eval i
  have hYj : MemLp (fun ω => matrixRealCoordinates (Y ω) j) 2 ν :=
    (E.toContinuousLinearMap.comp_memLp' hY).eval j
  simp only [map_sub, Pi.sub_apply]
  rw [covariance_sub_const_left (hXi.integrable one_le_two),
    covariance_sub_const_right (hXj.integrable one_le_two),
    covariance_sub_const_left (hYi.integrable one_le_two),
    covariance_sub_const_right (hYj.integrable one_le_two)]
  exact hcov i j

end NLAlib
