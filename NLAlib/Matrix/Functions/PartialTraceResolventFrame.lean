import NLAlib.Matrix.Structured.NormalizedPartialTrace
import NLAlib.Matrix.Structured.CoefficientTraceFrame
import NLAlib.Matrix.Functions.HermitianResolvent

/-! # The true normalized partial-trace resolvent gradient frame

The Frobenius trace-probe factor is exactly the ensemble dimension, while
normalization contributes its inverse square. The actual coefficient
covariance is retained, making the GUE endpoint budget of order N⁻².
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Kronecker
namespace NLAlib
variable {d n κ : Type*} [Fintype d] [Fintype n] [Fintype κ]
  [DecidableEq d] [DecidableEq n] [DecidableEq κ]

open scoped Matrix.Norms.L2Operator in
/-- Actual normalized partial traces of the native single-insertion
resolvent derivatives have their squared-coordinate frame bounded by the
true coefficient covariance divided by ensemble dimension and by the fourth
power of imaginary height. No probability or frame specification is assumed. -/
theorem sum_norm_normalizedPartialTrace_resolvent_sandwich_sq_le
    (C : κ → Matrix (d×n) (d×n) ℂ)
    {X : Matrix (d×n) (d×n) ℂ} (hX : X.IsHermitian)
    {ζ : ℂ} (hζ : ζ.im≠0) (a b : d) :
    (∑ k, ‖normalizedPartialTrace (resolvent X ζ*C k*resolvent X ζ) a b‖^2) ≤
      specNorm (coefficientCovariance C)/(Fintype.card n : ℝ)*|ζ.im|⁻¹^4 := by
  rcases isEmpty_or_nonempty n with hn|hn
  · let := hn
    simp [normalizedPartialTrace,Fintype.card_eq_zero]
  · let := hn
    have hN : (Fintype.card n : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    let R := resolvent X ζ
    let P := (Matrix.single b a 1 : Matrix d d ℂ)⊗ₖ(1 : Matrix n n ℂ)
    let U := R*P*R
    have hR : specNorm R≤|ζ.im|⁻¹ := hX.specNorm_resolvent_le hζ
    have hF : frobSq U≤(Fintype.card n : ℝ)*|ζ.im|⁻¹^4 := by
      calc
        _ ≤ frobSq (R*P)*specNorm R^2 := frobSq_mul_le_frobSq_mul_specNorm_sq _ _
        _ ≤ (specNorm R^2*frobSq P)*specNorm R^2 :=
          mul_le_mul_of_nonneg_right (frobSq_mul_le_specNorm_sq_mul_frobSq R P) (sq_nonneg _)
        _ = (Fintype.card n : ℝ)*specNorm R^4 := by
          rw [show frobSq P=(Fintype.card n : ℝ) from frobSq_single_kronecker_one b a]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (specNorm_nonneg _) hR _) (Nat.cast_nonneg _)
    have he (k : κ) :
        normalizedPartialTrace (R*C k*R) a b=(Fintype.card n : ℂ)⁻¹*(U*C k).trace := by
      rw [normalizedPartialTrace_apply_eq_trace]
      congr 1
      dsimp only [U]
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle' P (R*C k) R
    have hsum : (∑ k, ‖normalizedPartialTrace (R*C k*R) a b‖^2) =
        (Fintype.card n : ℝ)⁻¹^2*(∑ k, ‖(U*C k).trace‖^2) := by
      simp_rw [he,norm_mul,norm_inv,Complex.norm_natCast,mul_pow]
      rw [Finset.mul_sum]
    rw [hsum]
    calc
      _ ≤ (Fintype.card n : ℝ)⁻¹^2*(specNorm (coefficientCovariance C)*frobSq U) :=
        mul_le_mul_of_nonneg_left
          (sum_norm_trace_mul_sq_le_coefficientCovariance_mul_frobSq C U) (sq_nonneg _)
      _ ≤ (Fintype.card n : ℝ)⁻¹^2*
          (specNorm (coefficientCovariance C)*((Fintype.card n : ℝ)*|ζ.im|⁻¹^4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hF (specNorm_nonneg _)) (sq_nonneg _)
      _ = _ := by field_simp [hN]

end NLAlib
