import NLAlib.Matrix.Functions.ResolventCoordinateOperator

/-!
# Finite coefficient fields of the actual resolvent derivative

The native continuous pi-ring equivalence replaces the derivative operator
by its finite array of values on the coordinate basis. Its inverse evaluates
exactly to the original derivative; this conversion affects only analytic
domination and introduces no factor into the operator identities.
Source: arXiv:2201.05142v3, §6.4 Lemma 6.11.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open ContinuousLinearMap
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

private theorem norm_piRing_le {κ V : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (D : (κ → ℝ) →L[ℝ] V) :
    ‖ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) κ D‖ ≤ ‖D‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg D)).mpr
  intro j
  change ‖D (Pi.single j 1)‖ ≤ ‖D‖
  simpa only [Pi.norm_single, norm_one, mul_one] using D.le_opNorm (Pi.single j 1)

private theorem opNorm_piRing_le {κ V : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖(ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) κ).toContinuousLinearMap‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro D
  simpa only [one_mul] using! norm_piRing_le D

private theorem hasFDerivAt_piRing_comp
    {κ V W : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : W → (κ → ℝ) →L[ℝ] V) (D : W →L[ℝ] (κ → ℝ) →L[ℝ] V) (y : W)
    (hf : HasFDerivAt f D y) :
    HasFDerivAt (fun w => ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) κ (f w))
      ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) κ).toContinuousLinearMap.comp D) y := by
  exact (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := V) κ).toContinuousLinearMap.hasFDerivAt.comp y hf

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "F" => J → M
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)
local notation "T" => (ContinuousLinearEquiv.piRing J : (E →L[ℝ] M) ≃L[ℝ] F)

/-- Coordinate-basis values of the actual operator resolvent derivative. -/
def hermitianCoordinateResolventCoefficients (A : M) (ζ : ℂ) (y : E) : F :=
  T (hermitianCoordinateResolventDeriv A ζ y)

/-- The actual derivative of the finite resolvent coefficient field. -/
def hermitianCoordinateResolventCoefficientsDeriv (A : M) (ζ : ℂ) (y : E) : E →L[ℝ] F :=
  (T).toContinuousLinearMap.comp (hermitianCoordinateResolventSecondDeriv A ζ y)

/-- Evaluation of a direction against a finite operator coefficient array. -/
def hermitianCoordinateCoefficientPairing : E →L[ℝ] F →L[ℝ] M :=
  ((compL ℝ F (E →L[ℝ] M) M).flip (T).symm.toContinuousLinearMap).comp (apply ℝ M)

@[simp] theorem hermitianCoordinateCoefficientPairing_apply (h : E) (v : F) :
    hermitianCoordinateCoefficientPairing h v = (T).symm v h := rfl

@[simp] theorem hermitianCoordinateCoefficientPairing_coefficients
    (A : M) (ζ : ℂ) (y h : E) :
    hermitianCoordinateCoefficientPairing h (hermitianCoordinateResolventCoefficients A ζ y) =
      hermitianCoordinateResolventDeriv A ζ y h := by
  rw [hermitianCoordinateCoefficientPairing_apply, hermitianCoordinateResolventCoefficients,
    ContinuousLinearEquiv.symm_apply_apply]

theorem hermitianCoordinateCoefficientPairing_sub_coefficients
    (A : M) (ζ : ℂ) (y z h : E) :
    hermitianCoordinateCoefficientPairing h
      (hermitianCoordinateResolventCoefficients A ζ y-hermitianCoordinateResolventCoefficients A ζ z) =
        hermitianCoordinateResolventDeriv A ζ y h-hermitianCoordinateResolventDeriv A ζ z h := by
  rw [map_sub, hermitianCoordinateCoefficientPairing_coefficients,
    hermitianCoordinateCoefficientPairing_coefficients]

@[simp] theorem hermitianCoordinateCoefficientPairing_coefficientsDeriv
    (A : M) (ζ : ℂ) (y k h : E) :
    hermitianCoordinateCoefficientPairing h (hermitianCoordinateResolventCoefficientsDeriv A ζ y k) =
      hermitianCoordinateResolventSecondDeriv A ζ y k h := by
  rw [hermitianCoordinateCoefficientPairing_apply]
  change (T).symm (T (hermitianCoordinateResolventSecondDeriv A ζ y k)) h = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem hasFDerivAt_hermitianCoordinateResolventCoefficients (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    HasFDerivAt (hermitianCoordinateResolventCoefficients A ζ)
      (hermitianCoordinateResolventCoefficientsDeriv A ζ y) y := by
  have h := hasFDerivAt_piRing_comp
    (hermitianCoordinateResolventDeriv A ζ) (hermitianCoordinateResolventSecondDeriv A ζ y) y
    (by simpa only using! hasFDerivAt_hermitianCoordinateResolventDeriv A hA ζ hζ y)
  exact h

theorem continuous_hermitianCoordinateResolventCoefficients (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) : Continuous (hermitianCoordinateResolventCoefficients A ζ) :=
  (T).continuous.comp (continuous_hermitianCoordinateResolventDeriv A hA ζ hζ)

theorem continuous_hermitianCoordinateResolventCoefficientsDeriv (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) : Continuous (hermitianCoordinateResolventCoefficientsDeriv A ζ) :=
  (continuous_hermitianCoordinateResolventSecondDeriv A hA ζ hζ).const_clm_comp (T).toContinuousLinearMap

theorem norm_hermitianCoordinateResolventCoefficients_le (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    ‖hermitianCoordinateResolventCoefficients A ζ y‖ ≤ |ζ.im|⁻¹^2 * ‖L‖ :=
  (norm_piRing_le _).trans (norm_hermitianCoordinateResolventDeriv_le A hA ζ hζ y)

theorem norm_hermitianCoordinateResolventCoefficientsDeriv_le (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    ‖hermitianCoordinateResolventCoefficientsDeriv A ζ y‖ ≤ 2 * |ζ.im|⁻¹^3 * ‖L‖^2 := by
  apply (opNorm_comp_le _ _).trans
  have hT := opNorm_piRing_le (κ := J) (V := M)
  calc
    ‖(T).toContinuousLinearMap‖ * ‖hermitianCoordinateResolventSecondDeriv A ζ y‖ ≤
        1 * (2 * |ζ.im|⁻¹^3 * ‖L‖^2) :=
      mul_le_mul hT (norm_hermitianCoordinateResolventSecondDeriv_le A hA ζ hζ y)
        (norm_nonneg (hermitianCoordinateResolventSecondDeriv A ζ y)) zero_le_one
    _ = _ := one_mul _

end NLAlib
