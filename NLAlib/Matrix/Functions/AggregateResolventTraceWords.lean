import NLAlib.Matrix.Functions.AggregateTraceWords
import NLAlib.Matrix.Functions.ResolventMixedPowers
import NLAlib.Matrix.Functions.ResolventModulusMoments
import NLAlib.ForMathlib.Analysis.FiniteReciprocalExponents

/-!
# Bare aggregate common-resolvent trace words

The coefficient arrays are actual finite Hermitian matrix families with a
realized aggregate square bound in each slot. The common resolvent may be
chosen together with all coefficients: this is a pointwise deterministic
estimate, with no independence or marginal-law assumptions. Positive mixed
arcs collapse the Schatten product exactly, retaining normalized trace and
the fractional actual even resolvent moment without a dimension factor.
Source: the q=infinity multilinear mechanism of Brailovskaya--van Handel,
arXiv:2201.05142v3, Proposition 5.1 and Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder ENNReal
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Literal ordinary-trace words with common mixed resolvent arcs have the
sharp aggregate coefficient factor times one ordinary modulus trace. The
algebraic statement holds for total resolvents at every spectral parameter. -/
theorem norm_sum_trace_resolvent_mixed_word_le_cfcAbs_trace
    {k : ℕ} (hk : 2 ≤ k) (Z : ι → Fin k → Matrix n n ℂ)
    (hHerm : ∀ i j, (Z i j).IsHermitian) {r M : ℝ} (hr : 0 ≤ r)
    (hZ : ∀ i j, specNorm (Z i j) ≤ r)
    (hMass : ∀ j, specNorm (∑ i, Z i j ^ 2) ≤ M)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (ζ : ℂ)
    (a b : Fin k → ℕ) {L : ℕ} (hL : ∑ j, (a j + b j) = L)
    (hLpos : 0 < L) (hArc : ∀ j, 0 < a j + b j) :
    ‖∑ i, (List.ofFn (fun j => Z i j *
      (resolvent A ζ ^ a j * resolvent A (star ζ) ^ b j))).prod.trace‖ ≤
      r ^ (k - 2) * M * (CFC.abs (resolvent A ζ) ^ L).trace.re := by
  have hsSum : ∑ j, ((a j + b j : ℕ) : ℝ) = (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hs0 (j : Fin k) : (0 : ℝ) < (a j + b j : ℕ) := by exact_mod_cast hArc j
  obtain ⟨hp, hsum⟩ := ENNReal.one_le_ofReal_div_and_sum_inv_toReal_eq_one
    (fun j => ((a j + b j : ℕ) : ℝ)) hsSum hL0 hs0
  have h := norm_sumTraceWordMultilinear_le_prod_schattenNorm hk Z hHerm hr hZ hMass
    (fun j => ENNReal.ofReal ((L : ℝ) / (a j + b j : ℕ))) hp hsum
    (fun j => resolvent A ζ ^ a j * resolvent A (star ζ) ^ b j)
  rw [prod_schattenNorm_resolvent_mixed_powers_eq_re_trace_cfcAbs_pow hA ζ a b hL hLpos hArc] at h
  simpa only [sumTraceWordMultilinear_apply, RCLike.re_eq_complex_re] using h

omit [DecidableEq n] in
private theorem norm_sum_normalizedTrace_eq_div_card
    (W : ι → Matrix n n ℂ) :
    ‖∑ i, normalizedTrace (W i)‖ = ‖∑ i, (W i).trace‖ / (Fintype.card n : ℝ) := by
  simp only [normalizedTrace, ← Finset.mul_sum]
  rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv, mul_comm]

open scoped Matrix.Norms.L2Operator in
/-- Normalizing the actual finite trace-word sum divides the sharp modulus
trace by the same dimension. The native normalization includes empty matrices. -/
theorem norm_sum_normalizedTrace_resolvent_mixed_word_le_cfcAbs_trace
    {k : ℕ} (hk : 2 ≤ k) (Z : ι → Fin k → Matrix n n ℂ)
    (hHerm : ∀ i j, (Z i j).IsHermitian) {r M : ℝ} (hr : 0 ≤ r)
    (hZ : ∀ i j, specNorm (Z i j) ≤ r)
    (hMass : ∀ j, specNorm (∑ i, Z i j ^ 2) ≤ M)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (ζ : ℂ)
    (a b : Fin k → ℕ) {L : ℕ} (hL : ∑ j, (a j + b j) = L)
    (hLpos : 0 < L) (hArc : ∀ j, 0 < a j + b j) :
    ‖∑ i, normalizedTrace ((List.ofFn (fun j => Z i j *
      (resolvent A ζ ^ a j * resolvent A (star ζ) ^ b j))).prod)‖ ≤
      r ^ (k - 2) * M * (normalizedTrace (CFC.abs (resolvent A ζ) ^ L)).re := by
  have h := norm_sum_trace_resolvent_mixed_word_le_cfcAbs_trace
    hk Z hHerm hr hZ hMass hA ζ a b hL hLpos hArc
  have htrace : (CFC.abs (resolvent A ζ) ^ L).trace.re / (Fintype.card n : ℝ) =
      (normalizedTrace (CFC.abs (resolvent A ζ) ^ L)).re := by
    have ht := re_normalizedTrace_cfcAbs_pow_eq_sum_div_card (resolvent A ζ) L
    rw [← re_trace_cfcAbs_pow_eq_sum_singularValues (resolvent A ζ) L] at ht
    simpa only [RCLike.re_eq_complex_re] using ht.symm
  rw [norm_sum_normalizedTrace_eq_div_card]
  calc
    _ ≤ (r ^ (k - 2) * M * (CFC.abs (resolvent A ζ) ^ L).trace.re) /
        (Fintype.card n : ℝ) :=
      div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
    _ = _ := by rw [← htrace, mul_div_assoc]

open scoped Matrix.Norms.L2Operator in
/-- A literal normalized common-resolvent word is bounded by the realized
aggregate square mass, the remaining imaginary-height powers and one
fractional actual even resolvent moment. No coefficient/resolvent independence
is needed; radius zero, k=2 and empty dimensions are included. -/
theorem norm_sum_normalizedTrace_resolvent_mixed_word_le_resolventEvenMoment
    {k : ℕ} (hk : 2 ≤ k) (Z : ι → Fin k → Matrix n n ℂ)
    (hHerm : ∀ i j, (Z i j).IsHermitian) {r M : ℝ} (hr : 0 ≤ r)
    (hZ : ∀ i j, specNorm (Z i j) ≤ r)
    (hMass : ∀ j, specNorm (∑ i, Z i j ^ 2) ≤ M)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    (a b : Fin k → ℕ) {p L : ℕ} (hp : 0 < p)
    (hL : ∑ j, (a j + b j) = L) (hLp : 2 * p - 1 ≤ L)
    (hArc : ∀ j, 0 < a j + b j) :
    ‖∑ i, normalizedTrace ((List.ofFn (fun j => Z i j *
      (resolvent A ζ ^ a j * resolvent A (star ζ) ^ b j))).prod)‖ ≤
      r ^ (k - 2) * M * (|ζ.im|⁻¹) ^ (L - (2 * p - 1)) *
        resolventEvenMoment A ζ p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  have hLpos : 0 < L := by omega
  have hM : 0 ≤ M := by
    let j : Fin k := ⟨0, by omega⟩
    exact (specNorm_nonneg (∑ i, Z i j ^ 2)).trans (hMass j)
  have h := norm_sum_normalizedTrace_resolvent_mixed_word_le_cfcAbs_trace
    hk Z hHerm hr hZ hMass hA ζ a b hL hLpos hArc
  have hmoment := hA.re_normalizedTrace_cfcAbs_resolvent_pow_le hζ hp hLp
  have hC : 0 ≤ r ^ (k - 2) * M := mul_nonneg (pow_nonneg hr _) hM
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmoment hC)

end NLAlib
