import NLAlib.Matrix.Functions.ResolventMoments
import NLAlib.Matrix.Norms.NormalizedModulusMoments

/-!
# Normalized modulus bounds for nonreal Hermitian resolvents

The native uniform resolvent norm bound absorbs extra inverse powers, while
normalized power-mean monotonicity retains the fractional actual Gram moment.
Source: the trace-word estimates in Brailovskaya--van Handel,
arXiv:2201.05142v3, Lemma 6.9 and the high-moment comparison of Theorem 6.8.
This does not itself prove high-moment Gaussian universality.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Higher actual Hermitian resolvent modulus moments are controlled by
one fractional even Gram moment and exactly the unused powers of the
imaginary height. Positive moment order and empty matrix dimensions are
included; no positive eigenvalue or spectral gap is assumed. -/
theorem _root_.Matrix.IsHermitian.re_normalizedTrace_cfcAbs_resolvent_pow_le
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p L : ℕ} (hp : 0 < p) (hL : 2 * p - 1 ≤ L) :
    (normalizedTrace (CFC.abs (resolvent A ζ) ^ L)).re ≤
      (|ζ.im|⁻¹) ^ (L - (2 * p - 1)) *
        resolventEvenMoment A ζ p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  have h := re_normalizedTrace_cfcAbs_pow_le_pow_mul_moment_rpow
    (resolvent A ζ) (inv_nonneg.mpr (abs_nonneg _)) (hA.specNorm_resolvent_le hζ)
    (k := 2 * p - 1) (j := 2 * p) (by omega) (by omega) hL
  rw [re_normalizedTrace_cfcAbs_pow_two_mul] at h
  simpa only [RCLike.re_eq_complex_re, resolventEvenMoment] using h

open scoped Matrix.Norms.L2Operator in
/-- The precise modulus factor for a cubic inverse-moment word with `ell`
Neumann insertions is `|Im zeta|^(-(4+ell))` times the fractional actual
even Gram moment. All positive integer orders and empty dimensions apply. -/
theorem _root_.Matrix.IsHermitian.re_normalizedTrace_cfcAbs_resolvent_pow_two_mul_add_three_le
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (ell : ℕ) :
    (normalizedTrace (CFC.abs (resolvent A ζ) ^ (2 * p + 3 + ell))).re ≤
      (|ζ.im|⁻¹) ^ (4 + ell) *
        resolventEvenMoment A ζ p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  simpa only [show 2 * p + 3 + ell - (2 * p - 1) = 4 + ell by omega] using
    hA.re_normalizedTrace_cfcAbs_resolvent_pow_le hζ hp (L := 2 * p + 3 + ell) (by omega)

end NLAlib
