import NLAlib.Matrix.Functions.ResolventDerivatives
import NLAlib.Matrix.Functions.HermitianCoordinates
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Operator resolvents in full real and imaginary coordinates

The primitive and derivative fields are actual resolvent matrices and actual
continuous linear maps, without an assumed analytic or norm-estimate package.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial ContinuousLinearMap
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
private theorem hasFDerivAt_sandwich_comp
    {V W R : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedRing R] [NormedAlgebra ℝ R]
    (f : V → R) (D : V →L[ℝ] R) (L : W →L[ℝ] R) (y : V)
    (hf : HasFDerivAt f D y) :
    HasFDerivAt (fun w => (mulLeftRight ℝ R (f w) (f w)).comp L)
      (((compL ℝ W R R).flip L).comp
        (((mulLeftRight ℝ R (f y)).comp D) + ((mulLeftRight ℝ R).comp D).flip (f y))) y := by
  have hleft : HasFDerivAt (fun w => mulLeftRight ℝ R (f w))
      ((mulLeftRight ℝ R).comp D) y :=
    by
      apply HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := R)
        (G := R →L[ℝ] R →L[ℝ] R) y (f := f) (f' := D) ?_ hf
      convert! (mulLeftRight ℝ R).hasFDerivAt
  have hT := hleft.clm_apply hf
  exact ((compL ℝ W R R).flip L).hasFDerivAt.comp y hT

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- The actual operator resolvent after Hermitian reconstruction, with a
fixed deterministic matrix offset. -/
def hermitianCoordinateResolvent (A : M) (ζ : ℂ) (y : E) : M :=
  resolvent (A + L y) ζ

/-- The native single-insertion resolvent derivative. -/
def hermitianCoordinateResolventDeriv (A : M) (ζ : ℂ) (y : E) : E →L[ℝ] M :=
  ((rationalBlockMap 1 (C ζ-X) (A+L y) (A+L y)).restrictScalars ℝ).comp L

/-- The native derivative of the actual single-insertion field, bundled as
a continuous bilinear map. Its two ordered insertion words are proved below. -/
def hermitianCoordinateResolventSecondDeriv (A : M) (ζ : ℂ) (y : E) :
    E →L[ℝ] E →L[ℝ] M :=
  let R := hermitianCoordinateResolvent A ζ y
  let T := hermitianCoordinateResolventDeriv A ζ y
  ((compL ℝ E M M).flip L).comp
    (((mulLeftRight ℝ M R).comp T) + ((mulLeftRight ℝ M).comp T).flip R)

@[simp] theorem hermitianCoordinateResolventDeriv_apply (A : M) (ζ : ℂ) (y h : E) :
    hermitianCoordinateResolventDeriv A ζ y h =
      hermitianCoordinateResolvent A ζ y * L h * hermitianCoordinateResolvent A ζ y := by
  simp only [hermitianCoordinateResolventDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', rationalBlockMap_apply,
    rationalBlockDifference_resolvent, hermitianCoordinateResolvent]

private theorem hermitianCoordinateResolventDeriv_eq (A : M) (ζ : ℂ) (y : E) :
    hermitianCoordinateResolventDeriv A ζ y =
      (mulLeftRight ℝ M (hermitianCoordinateResolvent A ζ y)
        (hermitianCoordinateResolvent A ζ y)).comp L := by
  ext h i j
  simp only [hermitianCoordinateResolventDeriv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply]

theorem hasFDerivAt_hermitianCoordinateResolvent (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    HasFDerivAt (hermitianCoordinateResolvent A ζ)
      (hermitianCoordinateResolventDeriv A ζ y) y := by
  have hH := hA.add (isHermitian_hermitianMatrixFromRealCoordinates y)
  have hr := (hasFDerivAt_resolvent_of_isHermitian ζ (A + L y) hH hζ).restrictScalars ℝ
  have ha : HasFDerivAt (fun w : E => A + L w) L y := (L).hasFDerivAt.const_add A
  simpa only [hermitianCoordinateResolventDeriv, hermitianCoordinateResolvent,
    Function.comp_def] using! hr.comp y ha

theorem continuous_hermitianCoordinateResolvent (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) : Continuous (hermitianCoordinateResolvent A ζ) :=
  continuous_iff_continuousAt.mpr fun y =>
    (hasFDerivAt_hermitianCoordinateResolvent A hA ζ hζ y).continuousAt

theorem continuous_hermitianCoordinateResolventDeriv (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) : Continuous (hermitianCoordinateResolventDeriv A ζ) := by
  have hR := continuous_hermitianCoordinateResolvent A hA ζ hζ
  simp_rw [show hermitianCoordinateResolventDeriv A ζ = fun y =>
    (mulLeftRight ℝ M (hermitianCoordinateResolvent A ζ y)
      (hermitianCoordinateResolvent A ζ y)).comp L from
    funext (hermitianCoordinateResolventDeriv_eq A ζ)]
  exact (((mulLeftRight ℝ M).continuous.comp hR).clm_apply hR).clm_comp_const L

theorem hasFDerivAt_hermitianCoordinateResolventDeriv (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    HasFDerivAt (hermitianCoordinateResolventDeriv A ζ)
      (hermitianCoordinateResolventSecondDeriv A ζ y) y := by
  have hr := hasFDerivAt_hermitianCoordinateResolvent A hA ζ hζ y
  have h := hasFDerivAt_sandwich_comp
    (hermitianCoordinateResolvent A ζ) (hermitianCoordinateResolventDeriv A ζ y) L y
    (by simpa only using! hr)
  simpa only [← hermitianCoordinateResolventDeriv_eq,
    hermitianCoordinateResolventSecondDeriv] using! h

@[simp] theorem hermitianCoordinateResolventSecondDeriv_apply
    (A : M) (ζ : ℂ) (y k h : E) :
    hermitianCoordinateResolventSecondDeriv A ζ y k h =
      hermitianCoordinateResolvent A ζ y * L h * hermitianCoordinateResolvent A ζ y *
          L k * hermitianCoordinateResolvent A ζ y +
        hermitianCoordinateResolvent A ζ y * L k * hermitianCoordinateResolvent A ζ y *
          L h * hermitianCoordinateResolvent A ζ y := by
  simp only [hermitianCoordinateResolventSecondDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    add_apply, hermitianCoordinateResolventDeriv_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  noncomm_ring

theorem continuous_hermitianCoordinateResolventSecondDeriv
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    Continuous (hermitianCoordinateResolventSecondDeriv A ζ) := by
  have hR := continuous_hermitianCoordinateResolvent A hA ζ hζ
  have hD := continuous_hermitianCoordinateResolventDeriv A hA ζ hζ
  have hleft : Continuous (fun y =>
      (mulLeftRight ℝ M (hermitianCoordinateResolvent A ζ y)).comp
        (hermitianCoordinateResolventDeriv A ζ y)) :=
    ((mulLeftRight ℝ M).continuous.comp hR).clm_comp hD
  have hflip : Continuous (fun y =>
      ((mulLeftRight ℝ M).comp (hermitianCoordinateResolventDeriv A ζ y)).flip) :=
    by simpa only [coe_flipₗᵢ] using!
      (flipₗᵢ ℝ E M (M →L[ℝ] M)).continuous.comp
        (hD.const_clm_comp (mulLeftRight ℝ M))
  exact (hleft.add (hflip.clm_apply hR)).const_clm_comp ((compL ℝ E M M).flip L)

/-- The actual Hermitian process implies the resolvent's uniform spectral bound. -/
theorem specNorm_hermitianCoordinateResolvent_le (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    specNorm (hermitianCoordinateResolvent A ζ y) ≤ |ζ.im|⁻¹ :=
  (hA.add (isHermitian_hermitianMatrixFromRealCoordinates y)).specNorm_resolvent_le hζ

/-- Operator-derivative bounds only discharge analytic domination, not a
coordinate-wise substitute for the final matrix comparison estimate. -/
theorem norm_hermitianCoordinateResolventDeriv_le (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    ‖hermitianCoordinateResolventDeriv A ζ y‖ ≤ |ζ.im|⁻¹ ^ 2 * ‖L‖ := by
  have hr : ‖hermitianCoordinateResolvent A ζ y‖ ≤ |ζ.im|⁻¹ :=
    specNorm_hermitianCoordinateResolvent_le A hA ζ hζ y
  rw [hermitianCoordinateResolventDeriv_eq]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ M _ _).trans
  nlinarith [norm_nonneg (hermitianCoordinateResolvent A ζ y), abs_nonneg ζ.im]

theorem norm_hermitianCoordinateResolventSecondDeriv_le (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (y : E) :
    ‖hermitianCoordinateResolventSecondDeriv A ζ y‖ ≤
      2 * |ζ.im|⁻¹ ^ 3 * ‖L‖ ^ 2 := by
  have hr : ‖hermitianCoordinateResolvent A ζ y‖ ≤ |ζ.im|⁻¹ :=
    specNorm_hermitianCoordinateResolvent_le A hA ζ hζ y
  apply opNorm_le_bound _ (by positivity)
  intro k
  apply opNorm_le_bound _ (by positivity)
  intro h
  rw [hermitianCoordinateResolventSecondDeriv_apply]
  apply (norm_add_le _ _).trans
  have hb (h k : E) :
      ‖hermitianCoordinateResolvent A ζ y * L h * hermitianCoordinateResolvent A ζ y *
          L k * hermitianCoordinateResolvent A ζ y‖ ≤
        |ζ.im|⁻¹ ^ 3 * ‖L‖ ^ 2 * ‖k‖ * ‖h‖ := by
    calc
      _ ≤ ‖hermitianCoordinateResolvent A ζ y‖ * ‖L h‖ *
          ‖hermitianCoordinateResolvent A ζ y‖ * ‖L k‖ *
          ‖hermitianCoordinateResolvent A ζ y‖ := by
        calc
          _ ≤ ‖hermitianCoordinateResolvent A ζ y * L h *
              hermitianCoordinateResolvent A ζ y * L k‖ *
              ‖hermitianCoordinateResolvent A ζ y‖ := norm_mul_le _ _
          _ ≤ (‖hermitianCoordinateResolvent A ζ y * L h *
              hermitianCoordinateResolvent A ζ y‖ * ‖L k‖) *
              ‖hermitianCoordinateResolvent A ζ y‖ := by gcongr; exact norm_mul_le _ _
          _ ≤ ((‖hermitianCoordinateResolvent A ζ y * L h‖ *
              ‖hermitianCoordinateResolvent A ζ y‖) * ‖L k‖) *
              ‖hermitianCoordinateResolvent A ζ y‖ := by gcongr; exact norm_mul_le _ _
          _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ |ζ.im|⁻¹ * (‖L‖ * ‖h‖) * |ζ.im|⁻¹ * (‖L‖ * ‖k‖) * |ζ.im|⁻¹ := by
        gcongr <;> exact (L).le_opNorm _
      _ = _ := by ring
  calc
    _ ≤ |ζ.im|⁻¹ ^ 3 * ‖L‖ ^ 2 * ‖k‖ * ‖h‖ +
        |ζ.im|⁻¹ ^ 3 * ‖L‖ ^ 2 * ‖h‖ * ‖k‖ := add_le_add (hb h k) (hb k h)
    _ = _ := by ring

end NLAlib
