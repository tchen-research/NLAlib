import NLAlib.ForMathlib.Analysis.Calculus.SegmentRemainder
import NLAlib.Matrix.Functions.ResolventMomentDerivatives
import NLAlib.Matrix.Functions.ResolventMomentDerivativeBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Literal cubic inverse words in actual normalized-moment Taylor cancellation

Prerequisite for
`independent-sum-spectrum-universality`. The C3 assumption of the generic
Taylor identity is discharged by the actual Hermitian resolvent primitive.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- The genuine cubic Taylor kernel for the native normalized complex
mixed moment, with its unit-square parameterization. -/
def resolventMomentTaylorKernel (A : M) (ζ : ℂ) (p : ℕ) (a : ℝ) (x D V : E) : ℂ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
    iteratedFDeriv ℝ 3 (fun y : E => normalizedTrace
      (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p))
      (x - a • V + v • (a • (V + u • D))) ![V + u • D, D, D]

/-- The Taylor kernel is continuous in its actual three coordinate inputs.
Compact parameter integration is applied in this finite real coordinate space. -/
theorem continuous_resolventMomentTaylorKernel (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (a : ℝ) :
    Continuous (fun t : E × E × E => resolventMomentTaylorKernel A ζ p a t.1 t.2.1 t.2.2) := by
  let Φ : E → ℂ := fun y => normalizedTrace
    (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)
  let K : ((E × E × E) × ℝ) × ℝ → ℂ := fun t =>
    iteratedFDeriv ℝ 3 Φ
      (t.1.1.1 - a • t.1.1.2.2 + t.2 • (a • (t.1.1.2.2 + t.1.2 • t.1.1.2.1)))
      ![t.1.1.2.2 + t.1.2 • t.1.1.2.1, t.1.1.2.1, t.1.1.2.1]
  have hΦ : ContDiff ℝ 3 Φ := contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p
  have hthird := hΦ.continuous_iteratedFDeriv'
  have hpath : Continuous (fun t : ((E × E × E) × ℝ) × ℝ =>
      t.1.1.1 - a • t.1.1.2.2 + t.2 • (a • (t.1.1.2.2 + t.1.2 • t.1.1.2.1))) := by fun_prop
  have hdirs : Continuous (fun t : ((E × E × E) × ℝ) × ℝ =>
      ![t.1.1.2.2 + t.1.2 • t.1.1.2.1, t.1.1.2.1, t.1.1.2.1]) := by fun_prop
  have hK : Continuous K := continuous_eval.comp ((hthird.comp hpath).prodMk hdirs)
  have hv := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun q : (E × E × E) × ℝ => fun v : ℝ => K (q, v)) hK
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hu := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun q : E × E × E => fun u : ℝ => ∫ v in Set.Icc (0 : ℝ) 1, K ((q, u), v)) hv
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  simpa only [resolventMomentTaylorKernel, K, Φ,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Icc_eq_integral_Ioc] using hu

/-- The native cubic kernel has a constant envelope from actual bounded
matrix directions. No coordinate norm or coordinate third moment occurs. -/
theorem norm_resolventMomentTaylorKernel_le (A : M) (hA : A.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (a : ℝ) (x D V : E)
    {r : ℝ} (hr : 0 ≤ r) (hD : ‖L D‖ ≤ r) (hV : ‖L V‖ ≤ r) :
    ‖resolventMomentTaylorKernel A ζ p a x D V‖ ≤
      2 * ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) *
        (|ζ.im|⁻¹) ^ (2 * p + 3) * r ^ 3 := by
  let C : ℝ := 2 * ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
    ((2 * p + 2 : ℕ) : ℝ) * (|ζ.im|⁻¹) ^ (2 * p + 3) * r ^ 3
  have hdir (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) 1) : ‖L (V + u • D)‖ ≤ 2 * r := by
    rw [map_add, map_smul]
    calc
      _ ≤ ‖L V‖ + ‖u • L D‖ := norm_add_le _ _
      _ = ‖L V‖ + u * ‖L D‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1.le]
      _ ≤ r + u * r := add_le_add hV (mul_le_mul_of_nonneg_left hD hu.1.le)
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hr]
  have hb (u v : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ 3 (fun y : E => normalizedTrace
        (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p))
        (x - a • V + v • (a • (V + u • D))) ![V + u • D, D, D]‖ ≤ C := by
    have h := norm_iteratedFDeriv_three_normalizedTrace_mixed_resolvent_coordinate_apply_le
      A hA ζ hζ p (x - a • V + v • (a • (V + u • D))) ![V + u • D, D, D]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    calc
      _ ≤ _ := h
      _ ≤ ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) *
          (|ζ.im|⁻¹) ^ (2 * p + 3) * (2 * r) * r * r := by
        gcongr
        exact hdir u hu
      _ = C := by dsimp only [C]; ring
  unfold resolventMomentTaylorKernel
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq
    (by simp [C])
  intro u hu
  have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le zero_le_one] using hu
  exact (intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
    (fun v _ => hb u v hu')).trans_eq (by simp)

/-- Exact actual gradient/Hessian cancellation in terms of its native kernel. -/
theorem fderiv_sub_sub_smul_iteratedFDeriv_two_normalizedTrace_mixed_eq_kernel
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    (x D V : E) (a : ℝ) :
    let Φ : E → ℂ := fun y => normalizedTrace
      (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)
    (fderiv ℝ Φ (x + a • D) - fderiv ℝ Φ x) D -
        a • iteratedFDeriv ℝ 2 Φ (x - a • V) ![D, D] =
      a ^ 2 • resolventMomentTaylorKernel A ζ p a x D V := by
  have hc := contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p (r := 3)
  exact hc.fderiv_sub_sub_smul_iteratedFDeriv_two_eq_smul_sq_integral_three x D V a

/-- The actual primitive's Taylor cancellation is the exact finite sum of
literal ordered inverse words, with the unnormalized a² coefficient. -/
theorem fderiv_sub_sub_smul_iteratedFDeriv_two_normalizedTrace_mixed_eq_sum
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    (x D V : E) (a : ℝ) :
    let Φ : E → ℂ := fun y => normalizedTrace
      (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)
    (fderiv ℝ Φ (x + a • D) - fderiv ℝ Φ x) D -
        a • iteratedFDeriv ℝ 2 Φ (x - a • V) ![D, D] =
      a ^ 2 • ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        ∑ i : Fin (p + p), ∑ j : Fin (p + p + 1), ∑ k : Fin (p + p + 2),
          normalizedTrace (hermitianCoordinateResolventWord A
            (resolventWordInsert (resolventWordInsert
              (resolventWordInsert (mixedResolventWord ζ p) i (L D)) j (L D))
                k (L (V + u • D)))
            (x - a • V + v • (a • (V + u • D)))) := by
  dsimp only
  have hc := contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p (r := 3)
  have h := hc.fderiv_sub_sub_smul_iteratedFDeriv_two_eq_smul_sq_integral_three x D V a
  simp_rw [iteratedFDeriv_three_normalizedTrace_mixed_resolvent_coordinate_apply A hA ζ hζ p] at h
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

end NLAlib
