import NLAlib.Matrix.Functions.ResolventWordDerivativeBounds
import NLAlib.Matrix.Functions.ResolventMomentDerivatives
import NLAlib.Matrix.Norms.TraceSpectral

/-!
# Uniform domination for the actual normalized mixed moment

Prerequisite for
`independent-sum-spectrum-universality`. No moment comparison is a premise.
The observation uses the actual dimension-normalized trace, including d=0.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Sections 6.3–6.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

omit [Fintype n] in
/-- Every mixed-word shift has the same inverse imaginary-part bound. -/
theorem inv_abs_im_mixedResolventWord (ζ : ℂ) (p : ℕ) :
    ∀ i, |((mixedResolventWord (n := n) ζ p) i).1.im|⁻¹ = |ζ.im|⁻¹ := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mixedResolventWord, Fin.append_left]
  · simp only [mixedResolventWord, Fin.append_right, Complex.star_def,
      Complex.conj_im, abs_neg]

/-- Identity coefficients have mass at most one in every finite matrix dimension. -/
theorem prod_norm_snd_mixedResolventWord_le_one (ζ : ℂ) (p : ℕ) :
    (∏ i, ‖((mixedResolventWord (n := n) ζ p) i).2‖) ≤ 1 := by
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [mixedResolventWord, Fin.append_left, specNorm_eq_norm] using (specNorm_one_le (n := n) (𝕜 := ℂ))
  · simpa only [mixedResolventWord, Fin.append_right, specNorm_eq_norm] using (specNorm_one_le (n := n) (𝕜 := ℂ))

/-- Contractive normalized trace preserves every native derivative bound of
its actual inverse word. -/
theorem norm_iteratedFDeriv_normalizedTrace_mixed_resolvent_coordinate_le_word
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p k : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ k (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) y‖ ≤
      ‖iteratedFDeriv ℝ k (hermitianCoordinateResolventWord A (mixedResolventWord ζ p)) y‖ := by
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hT : ‖T‖ ≤ 1 := by
    simpa only [T, ContinuousLinearMap.norm_restrictScalars] using
      (norm_toContinuousLinearMap_normalizedTraceLinearMap_le_one (n := n) (𝕜 := ℂ))
  have hc := contDiff_hermitianCoordinateResolventWord A hA
    (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p) (r := ⊤)
  have heq : (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) =
        T ∘ hermitianCoordinateResolventWord A (mixedResolventWord ζ p) := by
    funext x
    simp only [Function.comp_apply, T, ContinuousLinearMap.coe_restrictScalars',
      LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
      hermitianCoordinateResolventWord_mixed]
  rw [heq]
  exact (T.norm_iteratedFDeriv_comp_left hc.contDiffAt (by simp)).trans
    ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans_eq (one_mul _))

/-- The actual complex normalized mixed trace has a global primitive bound. -/
theorem norm_normalizedTrace_mixed_resolvent_coordinate_le
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (y : E) :
    ‖normalizedTrace (resolvent (A + L y) ζ ^ p *
      resolvent (A + L y) (star ζ) ^ p)‖ ≤ |ζ.im|⁻¹ ^ (2 * p) := by
  have hb := norm_hermitianCoordinateResolventWord_le A hA (mixedResolventWord ζ p)
    (im_ne_zero_mixedResolventWord ζ hζ p) (inv_nonneg.mpr (abs_nonneg _))
    (fun i => (inv_abs_im_mixedResolventWord ζ p i).le) y
  have ht := norm_iteratedFDeriv_normalizedTrace_mixed_resolvent_coordinate_le_word
    A hA ζ hζ p 0 y
  simp only [norm_iteratedFDeriv_zero] at ht
  calc
    _ ≤ _ := ht.trans hb
    _ ≤ |ζ.im|⁻¹ ^ (p + p) * 1 := by
      gcongr
      exact prod_norm_snd_mixedResolventWord_le_one (n := n) ζ p
    _ = _ := by rw [two_mul, mul_one]

/-- Global real-gradient domination for the actual complex normalized trace. -/
theorem norm_fderiv_normalizedTrace_mixed_resolvent_coordinate_le
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (y : E) :
    ‖fderiv ℝ (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) y‖ ≤
        (2 * p : ℕ) * |ζ.im|⁻¹ ^ (2 * p + 1) * ‖L‖ := by
  have hb := norm_fderiv_hermitianCoordinateResolventWord_le A hA (mixedResolventWord ζ p)
    (im_ne_zero_mixedResolventWord ζ hζ p) (inv_nonneg.mpr (abs_nonneg _))
    (fun i => (inv_abs_im_mixedResolventWord ζ p i).le) y
  have ht := norm_iteratedFDeriv_normalizedTrace_mixed_resolvent_coordinate_le_word
    A hA ζ hζ p 1 y
  simp only [norm_iteratedFDeriv_one] at ht
  calc
    _ ≤ _ := ht.trans hb
    _ ≤ ((p + p : ℕ) : ℝ) * |ζ.im|⁻¹ ^ (p + p + 1) * 1 * ‖L‖ := by
      gcongr
      exact prod_norm_snd_mixedResolventWord_le_one (n := n) ζ p
    _ = _ := by simp only [two_mul, mul_one]

/-- Global Hessian domination for the actual complex normalized trace. -/
theorem norm_iteratedFDeriv_two_normalizedTrace_mixed_resolvent_coordinate_le
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ 2 (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) y‖ ≤
        (2 * p : ℕ) * (2 * p + 1 : ℕ) * |ζ.im|⁻¹ ^ (2 * p + 2) * ‖L‖ ^ 2 := by
  have hb := norm_iteratedFDeriv_two_hermitianCoordinateResolventWord_le A hA
    (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p)
    (inv_nonneg.mpr (abs_nonneg _)) (fun i => (inv_abs_im_mixedResolventWord ζ p i).le) y
  have ht := norm_iteratedFDeriv_normalizedTrace_mixed_resolvent_coordinate_le_word
    A hA ζ hζ p 2 y
  calc
    _ ≤ _ := ht.trans hb
    _ ≤ ((p + p : ℕ) : ℝ) * (p + p + 1) * |ζ.im|⁻¹ ^ (p + p + 2) * 1 * ‖L‖ ^ 2 := by
      gcongr <;> first
      | exact prod_norm_snd_mixedResolventWord_le_one (n := n) ζ p
      | norm_num
    _ = _ := by simp only [two_mul, Nat.cast_add, Nat.cast_one, mul_one]

/-- Global cubic derivative domination for the actual complex normalized trace. -/
theorem norm_iteratedFDeriv_three_normalizedTrace_mixed_resolvent_coordinate_le
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ 3 (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) y‖ ≤
        (2 * p : ℕ) * (2 * p + 1 : ℕ) * (2 * p + 2 : ℕ) *
          |ζ.im|⁻¹ ^ (2 * p + 3) * ‖L‖ ^ 3 := by
  have hb := norm_iteratedFDeriv_three_hermitianCoordinateResolventWord_le A hA
    (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p)
    (inv_nonneg.mpr (abs_nonneg _)) (fun i => (inv_abs_im_mixedResolventWord ζ p i).le) y
  have ht := norm_iteratedFDeriv_normalizedTrace_mixed_resolvent_coordinate_le_word
    A hA ζ hζ p 3 y
  calc
    _ ≤ _ := ht.trans hb
    _ ≤ ((p + p : ℕ) : ℝ) * (p + p + 1) * (p + p + 2) *
        |ζ.im|⁻¹ ^ (p + p + 3) * 1 * ‖L‖ ^ 3 := by
      gcongr <;> first
      | exact prod_norm_snd_mixedResolventWord_le_one (n := n) ζ p
      | norm_num
    _ = _ := by simp only [two_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_one]

/-- Actual normalized complex cubic derivatives are bounded only by the
three reconstructed matrix directions, not by their coordinate norms. -/
theorem norm_iteratedFDeriv_three_normalizedTrace_mixed_resolvent_coordinate_apply_le
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    (y : E) (h : Fin 3 → E) :
    ‖iteratedFDeriv ℝ 3 (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) y h‖ ≤
      ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) *
        (|ζ.im|⁻¹) ^ (2 * p + 3) * ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := by
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hT : ‖T‖ ≤ 1 := by
    simpa only [T, ContinuousLinearMap.norm_restrictScalars] using
      (norm_toContinuousLinearMap_normalizedTraceLinearMap_le_one (n := n) (𝕜 := ℂ))
  have hc := contDiff_hermitianCoordinateResolventWord A hA
    (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p) (r := ⊤)
  have heq : (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) =
        T ∘ hermitianCoordinateResolventWord A (mixedResolventWord ζ p) := by
    funext x
    simp only [Function.comp_apply, T, ContinuousLinearMap.coe_restrictScalars',
      LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
      hermitianCoordinateResolventWord_mixed]
  rw [heq, T.iteratedFDeriv_comp_left hc.contDiffAt (by simp)]
  change ‖T (iteratedFDeriv ℝ 3
    (hermitianCoordinateResolventWord A (mixedResolventWord ζ p)) y h)‖ ≤ _
  have hb := norm_iteratedFDeriv_three_hermitianCoordinateResolventWord_apply_le A hA
    (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p)
    (inv_nonneg.mpr (abs_nonneg _)) (fun i => (inv_abs_im_mixedResolventWord ζ p i).le) y h
  calc
    _ ≤ ‖iteratedFDeriv ℝ 3
        (hermitianCoordinateResolventWord A (mixedResolventWord ζ p)) y h‖ :=
      (T.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans_eq (one_mul _))
    _ ≤ _ := hb
    _ ≤ ((p + p : ℕ) : ℝ) * (p + p + 1) * (p + p + 2) * (|ζ.im|⁻¹) ^ (p + p + 3) *
        1 * ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := by
      gcongr <;> first
      | exact prod_norm_snd_mixedResolventWord_le_one (n := n) ζ p
      | norm_num
    _ = _ := by simp only [two_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_one]

end NLAlib
