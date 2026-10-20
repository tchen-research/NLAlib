import NLAlib.Matrix.Functions.HermitianResolvent
import NLAlib.Matrix.Norms.SchattenMixedPowers

/-!
# Exact mixed powers of a native Hermitian resolvent

The native total resolvent of a Hermitian matrix is normal at every spectral
parameter, even on the real spectrum. Mixed powers at a parameter and its
conjugate therefore have the singular values and Schatten norms of the
corresponding modulus power. Only later norm estimates require nonreal shifts.
Source: the common-resolvent word estimates underlying Brailovskaya--van Handel,
arXiv:2201.05142v3, Proposition 5.1 and Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder ENNReal
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A Hermitian matrix's native total resolvent commutes with its adjoint at
all spectral parameters, without an invertibility premise. -/
theorem _root_.Matrix.IsHermitian.commute_resolvent_conjTranspose
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (ζ : 𝕜) :
    Commute (resolvent A ζ) (resolvent A ζ)ᴴ := by
  rw [hA.conjTranspose_resolvent]
  exact commute_resolvent A ζ (star ζ)

open scoped Matrix.Norms.L2Operator in
/-- The modulus of a mixed native resolvent power is exactly the total power
of its modulus, including zero exponents and empty matrix dimensions. -/
theorem cfcAbs_resolvent_pow_mul_resolvent_star_pow
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (ζ : 𝕜) (a b : ℕ) :
    CFC.abs (resolvent A ζ ^ a * resolvent A (star ζ) ^ b) =
      CFC.abs (resolvent A ζ) ^ (a + b) := by
  simpa only [hA.conjTranspose_resolvent] using
    cfcAbs_mul_pow_conjTranspose_pow (hA.commute_resolvent_conjTranspose ζ) a b

open scoped Matrix.Norms.L2Operator in
/-- Each in-dimension singular value of a mixed native resolvent power is the
corresponding resolvent singular value raised to its total degree. -/
theorem singularValues_resolvent_pow_mul_resolvent_star_pow
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (ζ : 𝕜) (a b : ℕ)
    (i : Fin (Fintype.card n)) :
    singularValues (resolvent A ζ ^ a * resolvent A (star ζ) ^ b) i =
      singularValues (resolvent A ζ) i ^ (a + b) := by
  simpa only [hA.conjTranspose_resolvent] using
    singularValues_mul_pow_conjTranspose_pow (hA.commute_resolvent_conjTranspose ζ) a b i

open scoped Matrix.Norms.L2Operator in
/-- Exact finite Schatten power-sum formula for mixed native resolvent powers.
The formula holds at every real exponent, in particular all positive ones. -/
theorem schattenNormReal_resolvent_pow_mul_resolvent_star_pow_eq_sum
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (ζ : 𝕜) (a b : ℕ) (q : ℝ) :
    schattenNormReal (resolvent A ζ ^ a * resolvent A (star ζ) ^ b) q =
      (∑ i : Fin (Fintype.card n), singularValues (resolvent A ζ) i ^
        (((a + b : ℕ) : ℝ) * q)) ^ (1 / q) := by
  simpa only [hA.conjTranspose_resolvent] using
    schattenNormReal_mul_pow_conjTranspose_pow_eq_sum
      (hA.commute_resolvent_conjTranspose ζ) a b q

open scoped Matrix.Norms.L2Operator in
/-- Positive arc lengths with the actual total length collapse the product of
native resolvent Schatten norms to the ordinary modulus trace. No spectral
parameter, invertibility, or nonempty-dimension restriction is needed. -/
theorem prod_schattenNormReal_resolvent_mixed_powers_eq_re_trace_cfcAbs_pow
    {ι : Type*} [Fintype ι] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (ζ : 𝕜) (a b : ι → ℕ) {L : ℕ} (hL : ∑ j, (a j + b j) = L)
    (hLpos : 0 < L) (hArc : ∀ j, 0 < a j + b j) :
    (∏ j, schattenNormReal (resolvent A ζ ^ a j * resolvent A (star ζ) ^ b j)
      ((L : ℝ) / (a j + b j : ℕ))) =
      RCLike.re (CFC.abs (resolvent A ζ) ^ L).trace := by
  simpa only [hA.conjTranspose_resolvent] using
    prod_schattenNormReal_mixed_powers_eq_re_trace_cfcAbs_pow
      (hA.commute_resolvent_conjTranspose ζ) a b hL hLpos hArc

open scoped Matrix.Norms.L2Operator in
/-- The exact native common-resolvent product in the main extended Schatten
interface. Its literal arc exponents satisfy the generic positive-length allocation identities,
so this identity plugs into multilinear Schatten interpolation directly. -/
theorem prod_schattenNorm_resolvent_mixed_powers_eq_re_trace_cfcAbs_pow
    {ι : Type*} [Fintype ι] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (ζ : 𝕜) (a b : ι → ℕ) {L : ℕ} (hL : ∑ j, (a j + b j) = L)
    (hLpos : 0 < L) (hArc : ∀ j, 0 < a j + b j) :
    (∏ j, schattenNorm (resolvent A ζ ^ a j * resolvent A (star ζ) ^ b j)
      (ENNReal.ofReal ((L : ℝ) / (a j + b j : ℕ)))) =
      RCLike.re (CFC.abs (resolvent A ζ) ^ L).trace := by
  simpa only [hA.conjTranspose_resolvent] using
    prod_schattenNorm_mixed_powers_eq_re_trace_cfcAbs_pow
      (hA.commute_resolvent_conjTranspose ζ) a b hL hLpos hArc

end NLAlib
