import NLAlib.Matrix.Functions.ResolventDerivatives
import NLAlib.Matrix.Functions.HermitianCoordinates
import NLAlib.Matrix.Norms.TraceSpectral

/-!
# Globally bounded Hermitian resolvent tests in real coordinates

Native self-adjoint reconstruction makes the resolvent tests and their real
Fréchet derivatives bounded on the entire coordinate space. This discharges
the analytic hypotheses of Gaussian Stein and differentiation under expectation.
Source: the supplied Cauchy-transform reroute, analytic justification.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial ContinuousLinearMap
open scoped Matrix Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n) ⊕ (n×n)
local notation "L" => (hermitianMatrixFromRealCoordinates : (J → ℝ) →L[ℝ] M)

private theorem norm_square_le_square_norm (A : M) : ‖A^2‖ ≤ ‖A‖^2 := by
  simpa only [pow_two] using norm_mul_le A A

/-- Two three-resolvent insertion words have the uniform expected power of
the nonreal-shift denominator, times the direction's spectral norm. -/
theorem specNorm_resolventSquareDifference_le (ζ : ℂ) (A B H : M)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hζ : ζ.im ≠ 0) :
    specNorm (resolventSquareDifference ζ A B H) ≤ 2 * |ζ.im|⁻¹^3 * specNorm H := by
  let c := |ζ.im|⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (abs_nonneg _)
  have hRA : ‖resolvent A ζ‖ ≤ c := hA.specNorm_resolvent_le hζ
  have hRB : ‖resolvent B ζ‖ ≤ c := hB.specNorm_resolvent_le hζ
  have hRA2 : ‖(resolvent A ζ)^2‖ ≤ c^2 :=
    (norm_square_le_square_norm _).trans (pow_le_pow_left₀ (norm_nonneg _) hRA 2)
  have hRB2 : ‖(resolvent B ζ)^2‖ ≤ c^2 :=
    (norm_square_le_square_norm _).trans (pow_le_pow_left₀ (norm_nonneg _) hRB 2)
  have h₁ : ‖(resolvent A ζ)^2 * H * resolvent B ζ‖ ≤ c^3 * ‖H‖ := by
    calc
      _ ≤ (‖(resolvent A ζ)^2‖ * ‖H‖) * ‖resolvent B ζ‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (c^2 * ‖H‖) * c := by gcongr
      _ = _ := by ring
  have h₂ : ‖resolvent A ζ * H * (resolvent B ζ)^2‖ ≤ c^3 * ‖H‖ := by
    calc
      _ ≤ (‖resolvent A ζ‖ * ‖H‖) * ‖(resolvent B ζ)^2‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (c * ‖H‖) * c^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖(resolvent A ζ)^2 * H * resolvent B ζ‖ +
        ‖resolvent A ζ * H * (resolvent B ζ)^2‖ := norm_add_le _ _
    _ ≤ c^3 * ‖H‖ + c^3 * ‖H‖ := add_le_add h₁ h₂
    _ = _ := by simp only [specNorm_eq_norm]; dsimp [c]; ring

/-- The norm of the actual squared-resolvent derivative is uniformly bounded. -/
theorem norm_rationalBlockMap_resolvent_sq_le (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    ‖rationalBlockMap 1 ((C ζ-X)^2) A A‖ ≤ 2 * |ζ.im|⁻¹^3 := by
  apply opNorm_le_bound _ (by positivity)
  intro H
  rw [rationalBlockMap_apply,rationalBlockDifference_resolvent_sq ζ A A H hA hA hζ]
  exact specNorm_resolventSquareDifference_le ζ A A H hA hA hζ

/-- The actual normalized trace-resolvent derivative has a dimension-free bound. -/
theorem norm_traceResolventDerivative_le (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    ‖traceResolventDerivative ζ A‖ ≤ |ζ.im|⁻¹^2 := by
  apply opNorm_le_bound _ (sq_nonneg _)
  intro H
  rw [traceResolventDerivative_apply]
  calc
    _ ≤ specNorm (H*(resolvent A ζ)^2) := norm_normalizedTrace_le_specNorm _
    _ ≤ specNorm H * specNorm ((resolvent A ζ)^2) := specNorm_mul_le _ _
    _ ≤ specNorm H * |ζ.im|⁻¹^2 := by
      apply mul_le_mul_of_nonneg_left _ (specNorm_nonneg H)
      exact (norm_square_le_square_norm _).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hA.specNorm_resolvent_le hζ) 2)
    _ = _ := mul_comm _ _

/-- Actual squared resolvent after native Hermitian reconstruction. -/
def hermitianCoordinateSquaredResolvent (ζ : ℂ) (x : J → ℝ) : M :=
  (resolvent (L x) ζ)^2

/-- Its actual real Fréchet derivative in full real entry coordinates. -/
def hermitianCoordinateSquaredResolventDerivative (ζ : ℂ) (x : J → ℝ) : (J → ℝ) →L[ℝ] M :=
  ((rationalBlockMap 1 ((C ζ-X)^2) (L x) (L x)).restrictScalars ℝ).comp L

/-- Actual normalized trace resolvent after native Hermitian reconstruction. -/
def hermitianCoordinateTraceResolvent (ζ : ℂ) (x : J → ℝ) : ℂ :=
  normalizedTrace (resolvent (L x) ζ)

/-- Its actual real Fréchet derivative. -/
def hermitianCoordinateTraceResolventDerivative (ζ : ℂ) (x : J → ℝ) : (J → ℝ) →L[ℝ] ℂ :=
  ((traceResolventDerivative ζ (L x)).restrictScalars ℝ).comp L

/-- Globally defined coordinate squared resolvents are genuinely differentiable. -/
theorem hasFDerivAt_hermitianCoordinateSquaredResolvent (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    HasFDerivAt (hermitianCoordinateSquaredResolvent ζ)
      (hermitianCoordinateSquaredResolventDerivative ζ x) x := by
  rw [show hermitianCoordinateSquaredResolvent ζ =
    (fun y : J → ℝ => (resolvent (L y) ζ)^2) from rfl]
  simpa only [hermitianCoordinateSquaredResolventDerivative,Function.comp_def] using!
    ((hasFDerivAt_resolvent_sq_of_isHermitian ζ (L x)
      (isHermitian_hermitianMatrixFromRealCoordinates x) hζ).restrictScalars ℝ).comp x (L).hasFDerivAt

/-- Globally defined coordinate trace resolvents are genuinely differentiable. -/
theorem hasFDerivAt_hermitianCoordinateTraceResolvent (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    HasFDerivAt (hermitianCoordinateTraceResolvent ζ)
      (hermitianCoordinateTraceResolventDerivative ζ x) x := by
  rw [show hermitianCoordinateTraceResolvent ζ =
    (fun y : J → ℝ => normalizedTrace (resolvent (L y) ζ)) from rfl]
  simpa only [hermitianCoordinateTraceResolventDerivative,Function.comp_def] using!
    (hasFDerivAt_normalizedTrace_resolvent_real ζ (L x)
      (isHermitian_hermitianMatrixFromRealCoordinates x) hζ).comp x (L).hasFDerivAt

/-- Every coordinate test value has the required uniform squared bound. -/
theorem specNorm_hermitianCoordinateSquaredResolvent_le (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    specNorm (hermitianCoordinateSquaredResolvent ζ x) ≤ |ζ.im|⁻¹^2 :=
  (norm_square_le_square_norm _).trans (pow_le_pow_left₀ (norm_nonneg _)
    ((isHermitian_hermitianMatrixFromRealCoordinates x).specNorm_resolvent_le hζ) 2)

/-- Every normalized trace test value has the required uniform bound. -/
theorem norm_hermitianCoordinateTraceResolvent_le (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    ‖hermitianCoordinateTraceResolvent ζ x‖ ≤ |ζ.im|⁻¹ :=
  (norm_normalizedTrace_le_specNorm _).trans
    ((isHermitian_hermitianMatrixFromRealCoordinates x).specNorm_resolvent_le hζ)

/-- Real coordinate squared-resolvent derivatives are uniformly bounded. -/
theorem norm_hermitianCoordinateSquaredResolventDerivative_le
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    ‖hermitianCoordinateSquaredResolventDerivative ζ x‖ ≤ 2 * |ζ.im|⁻¹^3 * ‖L‖ := by
  have h := norm_rationalBlockMap_resolvent_sq_le ζ (L x)
    (isHermitian_hermitianMatrixFromRealCoordinates x) hζ
  have hr : ‖(rationalBlockMap 1 ((C ζ-X)^2) (L x) (L x)).restrictScalars ℝ‖ ≤
      2 * |ζ.im|⁻¹^3 := by simpa only [norm_restrictScalars] using h
  exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

/-- Real coordinate trace-resolvent derivatives are uniformly bounded. -/
theorem norm_hermitianCoordinateTraceResolventDerivative_le
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    ‖hermitianCoordinateTraceResolventDerivative ζ x‖ ≤ |ζ.im|⁻¹^2 * ‖L‖ := by
  have h := norm_traceResolventDerivative_le ζ (L x)
    (isHermitian_hermitianMatrixFromRealCoordinates x) hζ
  have hr : ‖(traceResolventDerivative ζ (L x)).restrictScalars ℝ‖ ≤ |ζ.im|⁻¹^2 := by
    simpa only [norm_restrictScalars] using h
  exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

private theorem isUnit_coordinate_shift (ζ : ℂ) (hζ : ζ.im ≠ 0) (x : J → ℝ) :
    IsUnit (aeval (L x) (C ζ-X)) := by
  simpa only [map_sub,aeval_C,aeval_X,Algebra.algebraMap_eq_smul_one] using
    (isHermitian_hermitianMatrixFromRealCoordinates x).isUnit_smul_one_sub_of_im_ne_zero hζ

private theorem continuous_rationalBlockMap_coordinate_diagonal (P Q : ℂ[X])
    (hQ : ∀ x : J → ℝ, IsUnit (aeval (L x) Q)) :
    Continuous (fun x : J → ℝ => rationalBlockMap P Q (L x) (L x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  simpa only [Function.comp_def] using
    (continuousAt_rationalBlockMap P Q (L x) (L x) (hQ x) (hQ x)).comp
      (x := x) (f := fun y : J → ℝ => (L y,L y)) ((L).continuous.prodMk (L).continuous).continuousAt

/-- The squared-resolvent derivative varies continuously on the whole real
coordinate space; nonreal shifts remain invertible at every reconstructed point. -/
theorem continuous_hermitianCoordinateSquaredResolventDerivative (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    Continuous (hermitianCoordinateSquaredResolventDerivative (n := n) ζ) := by
  have hQ (x : J → ℝ) : IsUnit (aeval (L x) ((C ζ-X)^2)) := by
    simpa only [map_pow] using (isUnit_coordinate_shift ζ hζ x).pow 2
  have hr := continuous_rationalBlockMap_coordinate_diagonal 1 ((C ζ-X)^2) hQ
  exact ((continuous_restrictScalars ℝ).comp hr).clm_comp continuous_const

/-- The trace-resolvent derivative also varies continuously on the whole real
coordinate space. -/
theorem continuous_hermitianCoordinateTraceResolventDerivative (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    Continuous (hermitianCoordinateTraceResolventDerivative (n := n) ζ) := by
  have hr : Continuous (fun x : J → ℝ => rationalBlockMap 1 (C ζ-X) (L x) (L x)) :=
    continuous_rationalBlockMap_coordinate_diagonal 1 (C ζ-X) (isUnit_coordinate_shift (n := n) ζ hζ)
  have ht : Continuous (fun x : J → ℝ => traceResolventDerivative ζ (L x)) :=
    continuous_const.clm_comp hr
  exact ((continuous_restrictScalars ℝ).comp ht).clm_comp continuous_const

/-- Pair a full real-coordinate direction with a matrix by normalized trace. -/
def hermitianCoordinateTraceProduct : (J → ℝ) →L[ℝ] M →L[ℝ] ℂ :=
  (((compL ℝ M M ℂ)
      ((normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ)).comp
    ((mul ℂ M).bilinearRestrictScalars ℝ)).comp L

@[simp] theorem hermitianCoordinateTraceProduct_apply (x : J → ℝ) (A : M) :
    hermitianCoordinateTraceProduct x A = normalizedTrace (L x * A) := rfl

/-- The coordinate derivative is exactly the trace bilinear pairing with the
actual squared-resolvent test, the primitive relation used by interpolation. -/
theorem hermitianCoordinateTraceResolventDerivative_apply (ζ : ℂ) (x h : J → ℝ) :
    hermitianCoordinateTraceResolventDerivative ζ x h =
      hermitianCoordinateTraceProduct h (hermitianCoordinateSquaredResolvent ζ x) := by
  have he : hermitianCoordinateTraceResolventDerivative ζ x h =
      traceResolventDerivative ζ (L x) (L h) := rfl
  rw [he,traceResolventDerivative_apply]
  rfl

/-- The coordinate squared-resolvent derivative is the actual two-word ordered
insertion along the Hermitian reconstruction of the direction. -/
theorem hermitianCoordinateSquaredResolventDerivative_apply (ζ : ℂ) (hζ : ζ.im ≠ 0)
    (x h : J → ℝ) :
    hermitianCoordinateSquaredResolventDerivative ζ x h =
      resolventSquareDifference ζ (L x) (L x) (L h) := by
  have he : hermitianCoordinateSquaredResolventDerivative ζ x h =
      rationalBlockMap 1 ((C ζ-X)^2) (L x) (L x) (L h) := rfl
  rw [he,rationalBlockMap_apply,rationalBlockDifference_resolvent_sq ζ (L x) (L x) (L h)
    (isHermitian_hermitianMatrixFromRealCoordinates x)
    (isHermitian_hermitianMatrixFromRealCoordinates x) hζ]

end NLAlib
