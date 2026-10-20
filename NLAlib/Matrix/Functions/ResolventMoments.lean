import NLAlib.Matrix.Functions.HermitianResolvent
import NLAlib.Matrix.Norms.SchattenEvenMoments
import NLAlib.Matrix.Norms.SchattenComparison
import NLAlib.Matrix.Basic.NormalizedTrace

/-!
# Actual normalized even resolvent moments

The actual Gram trace of the native resolvent gives normalized high moments
and their exact comparison with Schatten and spectral operator norms.

The source uses normalized trace, while `schattenNormReal` is unnormalized.
Consequently the exact dimension factors are retained. The definition and
power-sum identity and rooted norm comparisons include empty dimensions, using
the native zero normalization there. Every rooted statement retains positive
moment order.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Theorem 6.8 and Lemma 6.9.
These statements alone do not prove the spectral Hausdorff universality card.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem re_normalizedTrace_eq_div_card (B : Matrix n n ℂ) :
    (normalizedTrace B).re = B.trace.re / (Fintype.card n : ℝ) := by
  have hc : (Fintype.card n : ℂ)⁻¹ =
      (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [normalizedTrace, hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, div_eq_mul_inv, mul_comm]

/-- The actual normalized even resolvent moment. The Gram product makes the
positivity visible without choosing eigenvectors. -/
def resolventEvenMoment (A : Matrix n n ℂ) (ζ : ℂ) (p : ℕ) : ℝ :=
  (normalizedTrace (((resolvent A ζ)ᴴ * resolvent A ζ) ^ p)).re

/-- The actual even resolvent Gram moment equals the mixed native resolvent
trace at the spectral parameter and its conjugate. The identity includes
empty dimensions and spectral parameters on the real spectrum.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9. -/
theorem resolventEvenMoment_eq_re_normalizedTrace_mul_pow
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (ζ : ℂ) (p : ℕ) :
    resolventEvenMoment A ζ p =
      (normalizedTrace (resolvent A ζ ^ p * resolvent A (star ζ) ^ p)).re := by
  rw [resolventEvenMoment, hA.conjTranspose_resolvent]
  rw [(commute_resolvent A (star ζ) ζ).mul_pow,
    normalizedTrace_mul_comm]

private theorem resolventEvenMoment_eq_zero_of_isEmpty [IsEmpty n]
    (A : Matrix n n ℂ) (ζ : ℂ) (p : ℕ) : resolventEvenMoment A ζ p = 0 := by
  simp [resolventEvenMoment, normalizedTrace]

open scoped Matrix.Norms.L2Operator in
/-- The native Gram trace is exactly the unnormalized even Schatten power
divided by dimension. The empty dimension has value zero on both sides. -/
theorem resolventEvenMoment_eq_schattenNormReal_pow_div_card
    (A : Matrix n n ℂ) (ζ : ℂ) {p : ℕ} (hp : 0 < p) :
    resolventEvenMoment A ζ p =
      schattenNormReal (resolvent A ζ) (2 * p : ℕ) ^ (2 * p) /
        (Fintype.card n : ℝ) := by
  have hm := schattenNormReal_pow_even_eq_re_trace_gram (resolvent A ζ) hp
  change schattenNormReal (resolvent A ζ) (2 * p : ℕ) ^ (2 * p) =
    (((resolvent A ζ)ᴴ * resolvent A ζ) ^ p).trace.re at hm
  unfold resolventEvenMoment
  rw [re_normalizedTrace_eq_div_card, ← hm]

/-- Positive-order normalized resolvent moments are nonnegative, including
the empty dimension. No self-adjointness is required for the Gram identity. -/
theorem resolventEvenMoment_nonneg (A : Matrix n n ℂ) (ζ : ℂ)
    {p : ℕ} (hp : 0 < p) : 0 ≤ resolventEvenMoment A ζ p := by
  rw [resolventEvenMoment_eq_schattenNormReal_pow_div_card A ζ hp]
  exact div_nonneg (pow_nonneg (schattenNormReal_nonneg _ _) _) (Nat.cast_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- Positive-order moments of a nonreal Hermitian resolvent are strictly
positive in nonempty dimension. This supplies the actual positivity needed
before differentiating their real roots.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Theorem 6.8. -/
theorem _root_.Matrix.IsHermitian.resolventEvenMoment_pos [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) : 0 < NLAlib.resolventEvenMoment A ζ p := by
  have hu : ζ ∈ resolventSet ℂ A := by
    change IsUnit (algebraMap ℂ (Matrix n n ℂ) ζ - A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hA.isUnit_smul_one_sub_of_im_ne_zero hζ
  have hR : resolvent A ζ ≠ 0 := (spectrum.isUnit_resolvent.mp hu).ne_zero
  rw [resolventEvenMoment_eq_schattenNormReal_pow_div_card A ζ hp]
  apply div_pos
  · apply pow_pos
    apply lt_of_le_of_ne (schattenNormReal_nonneg _ _)
    intro hz
    exact hR ((schattenNormReal_eq_zero_iff _
      (by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hp)).mp hz.symm)
  · exact_mod_cast Fintype.card_pos

open scoped Matrix.Norms.L2Operator in
/-- The rooted normalized trace equals the Schatten norm divided by the
exact dimension factor, including the native zero-over-zero empty convention. -/
theorem resolventEvenMoment_rpow_inv_eq_schattenNormReal_div
    (A : Matrix n n ℂ) (ζ : ℂ) {p : ℕ} (hp : 0 < p) :
    resolventEvenMoment A ζ p ^ (1 / ((2 * p : ℕ) : ℝ)) =
      schattenNormReal (resolvent A ζ) (2 * p : ℕ) /
        (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) := by
  have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
  rw [resolventEvenMoment_eq_schattenNormReal_pow_div_card A ζ hp,
    Real.div_rpow (pow_nonneg (schattenNormReal_nonneg _ _) _) (Nat.cast_nonneg _),
    ← Real.rpow_natCast, one_div,
    Real.rpow_rpow_inv (schattenNormReal_nonneg _ _) hk.ne']

open scoped Matrix.Norms.L2Operator in
/-- A rooted normalized trace moment is at most the native resolvent's
spectral norm, with no dimension loss. -/
theorem resolventEvenMoment_rpow_inv_le_specNorm
    (A : Matrix n n ℂ) (ζ : ℂ) {p : ℕ} (hp : 0 < p) :
    resolventEvenMoment A ζ p ^ (1 / ((2 * p : ℕ) : ℝ)) ≤
      specNorm (resolvent A ζ) := by
  have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz : resolvent A ζ = 0 := Subsingleton.elim _ _
    simp only [resolventEvenMoment_eq_zero_of_isEmpty A ζ p, hz, specNorm_zero,
      Real.zero_rpow (one_div_ne_zero hk.ne'), le_refl]
  | inr hn =>
    have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    have hdroot : 0 < (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos hd _
    rw [resolventEvenMoment_rpow_inv_eq_schattenNormReal_div A ζ hp]
    exact (div_le_iff₀ hdroot).mpr
      (by simpa only [mul_comm] using
        schattenNormReal_le_card_rpow_mul_specNorm (resolvent A ζ) hk)

open scoped Matrix.Norms.L2Operator in
/-- Conversely the spectral norm is at most the rooted normalized moment
times the exact factor `d^(1/(2p))`. -/
theorem specNorm_resolvent_le_card_rpow_mul_resolventEvenMoment_rpow_inv
    (A : Matrix n n ℂ) (ζ : ℂ) {p : ℕ} (hp : 0 < p) :
    specNorm (resolvent A ζ) ≤
      (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        resolventEvenMoment A ζ p ^ (1 / ((2 * p : ℕ) : ℝ)) := by
  have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz : resolvent A ζ = 0 := Subsingleton.elim _ _
    simp only [resolventEvenMoment_eq_zero_of_isEmpty A ζ p, hz, specNorm_zero,
      Real.zero_rpow (one_div_ne_zero hk.ne'), mul_zero, le_refl]
  | inr hn =>
    have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    have hdroot : 0 < (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos hd _
    rw [resolventEvenMoment_rpow_inv_eq_schattenNormReal_div A ζ hp]
    calc
      _ ≤ schattenNormReal (resolvent A ζ) (2 * p : ℕ) :=
        specNorm_le_schattenNormReal (resolvent A ζ) hk
      _ = _ := by field_simp [ne_of_gt hdroot]

open scoped Matrix.Norms.L2Operator in
/-- The even operator-norm power is at most dimension times the actual
normalized trace moment. This is the pointwise estimate used by Markov. -/
theorem specNorm_resolvent_pow_le_card_mul_resolventEvenMoment
    (A : Matrix n n ℂ) (ζ : ℂ) {p : ℕ} (hp : 0 < p) :
    specNorm (resolvent A ζ) ^ (2 * p) ≤
      (Fintype.card n : ℝ) * resolventEvenMoment A ζ p := by
  have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz : resolvent A ζ = 0 := Subsingleton.elim _ _
    simp only [hz, specNorm_zero, zero_pow (by omega : 2 * p ≠ 0),
      resolventEvenMoment_eq_zero_of_isEmpty, mul_zero, le_refl]
  | inr hn =>
    have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    rw [resolventEvenMoment_eq_schattenNormReal_pow_div_card A ζ hp]
    calc
      _ ≤ schattenNormReal (resolvent A ζ) (2 * p : ℕ) ^ (2 * p) :=
        pow_le_pow_left₀ (specNorm_nonneg _)
          (specNorm_le_schattenNormReal (resolvent A ζ) hk) _
      _ = _ := by field_simp [ne_of_gt hd]

open scoped Matrix.Norms.L2Operator in
/-- A positive-order normalized trace moment is bounded by the corresponding
spectral-norm power. -/
theorem resolventEvenMoment_le_specNorm_pow
    (A : Matrix n n ℂ) (ζ : ℂ) {p : ℕ} (hp : 0 < p) :
    resolventEvenMoment A ζ p ≤ specNorm (resolvent A ζ) ^ (2 * p) := by
  have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
  cases isEmpty_or_nonempty n with
  | inl hn =>
    rw [resolventEvenMoment_eq_zero_of_isEmpty A ζ p]
    exact pow_nonneg (specNorm_nonneg _) _
  | inr hn =>
    have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    have hSp := schattenNormReal_le_card_rpow_mul_specNorm (resolvent A ζ) hk
    have hpower := pow_le_pow_left₀ (schattenNormReal_nonneg (resolvent A ζ) _) hSp (2 * p)
    have hdim : ((Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ))) ^ (2 * p) =
        (Fintype.card n : ℝ) := by
      rw [← Real.rpow_natCast, one_div, Real.rpow_inv_rpow hd.le hk.ne']
    rw [mul_pow, hdim] at hpower
    rw [resolventEvenMoment_eq_schattenNormReal_pow_div_card A ζ hp, div_le_iff₀ hd]
    simpa only [mul_comm] using hpower

/-- Hermitian nonreal resolvents give a uniform bound for every actual
normalized even moment. The bound is independent of the matrix entries. -/
theorem resolventEvenMoment_le_inv_abs_im_pow
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) :
    resolventEvenMoment A ζ p ≤ (|ζ.im|⁻¹) ^ (2 * p) :=
  (resolventEvenMoment_le_specNorm_pow A ζ hp).trans
    (pow_le_pow_left₀ (specNorm_nonneg _) (hA.specNorm_resolvent_le hζ) _)

/-- The rooted high moment has the same uniform `1/|Im ζ|` bound as the
operator norm. -/
theorem resolventEvenMoment_rpow_inv_le_inv_abs_im
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) :
    resolventEvenMoment A ζ p ^ (1 / ((2 * p : ℕ) : ℝ)) ≤ |ζ.im|⁻¹ :=
  (resolventEvenMoment_rpow_inv_le_specNorm A ζ hp).trans
    (hA.specNorm_resolvent_le hζ)

end NLAlib
