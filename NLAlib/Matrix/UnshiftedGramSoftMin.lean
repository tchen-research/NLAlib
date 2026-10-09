import NLAlib.Matrix.GramSoftMin
import NLAlib.Matrix.InversePowerLimit
import NLAlib.Matrix.SpectralMinimum
import Mathlib.Analysis.Matrix.Order

/-!
# Finite unshifted inverse-power Gram bounds

The inverse-power approximation to the minimum of a positive definite Gram
matrix satisfies the sharp hard-edge Laplacian inequality at every finite
positive power. Positive trace-product defects supply the dimension correction,
without an identity shift or any eigenvalue-separation condition.

Source: the user's finite inverse-power operator refinement.
Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq κ] in
/-- Zero regularization is the original Gram matrix. Source: the Gram
definition; atlas `wishart-lambda-min-tail` (helper). -/
@[simp] theorem regularizedGram_zero (G : Matrix ι κ ℝ) : regularizedGram 0 G = G * Gᵀ := by
  simp only [regularizedGram, zero_smul, add_zero]

omit [Fintype κ] [DecidableEq κ] in
/-- Products of positive semidefinite trace powers dominate the trace
power of their product. Source: nonnegative eigenvalue cross terms;
atlas `wishart-lambda-min-tail` (finite defect helper). -/
theorem trace_pow_le_trace_pow_mul_trace_pow {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (a b : ℕ) :
    Matrix.trace (R ^ (a + b)) ≤ Matrix.trace (R ^ a) * Matrix.trace (R ^ b) := by
  rw [trace_pow_eq_sum_eigenvalues hR.isHermitian,
    trace_pow_eq_sum_eigenvalues hR.isHermitian,
    trace_pow_eq_sum_eigenvalues hR.isHermitian, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => pow_nonneg (hR.eigenvalues_nonneg j) b)
      (Finset.mem_univ i)) (pow_nonneg (hR.eigenvalues_nonneg i) a)

private lemma sum_trace_power_reflect (S : ℕ → ℝ) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), S (n - a + 1) * S a) =
      ∑ a ∈ Finset.range (n + 1), S (a + 1) * S (n - a) := by
  have href := Finset.sum_range_reflect (fun a => S (a + 1) * S (n - a)) (n + 1)
  apply Eq.trans ?_ href
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  simp only [Nat.add_sub_cancel]
  rw [show n - (n - a) = a by omega]

omit [DecidableEq κ] in
/-- At an invertible Gram matrix, its inverse trace power contracts with
the Gram matrix by lowering the exponent by one. Source: inverse identity;
atlas `wishart-lambda-min-tail` (finite calculus helper). -/
theorem trace_inv_gram_pow_succ_mul_gram (G : Matrix ι κ ℝ)
    (hpd : (G * Gᵀ).PosDef) (a : ℕ) :
    Matrix.trace ((G * Gᵀ)⁻¹ ^ (a + 1) * (G * Gᵀ)) =
      Matrix.trace ((G * Gᵀ)⁻¹ ^ a) := by
  rw [pow_succ, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit), Matrix.mul_one]

/-- The exact finite unshifted Gram Laplacian consists of its sharp
dimension term minus two nonnegative trace-product defects. Source: the
user's finite inverse-power refinement; atlas `wishart-lambda-min-tail` (helper).
The sum over `a < n` is the source's sum over exponents `1, ..., n`. -/
theorem gramSoftMinLaplacian_unshifted_eq [Nonempty ι]
    (n : ℕ) (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) :
    let R := (G * Gᵀ)⁻¹
    let S := fun a : ℕ => Matrix.trace (R ^ a)
    let c := S n ^ (-(n : ℝ)⁻¹ - 1)
    gramSoftMinLaplacian n 0 G =
      2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) -
        4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) -
        2 * c * ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1)) := by
  dsimp only
  let R := (G * Gᵀ)⁻¹
  let S := fun a : ℕ => Matrix.trace (R ^ a)
  have hT : 0 < S n := trace_pow_pos_of_posDef hpd.inv n
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram, zero_smul, add_zero] using hpd
  have h := gramSoftMinLaplacian_eq n 0 G hreg
  dsimp only at h
  simp only [regularizedGram, zero_smul, add_zero] at h
  have htrace (a : ℕ) : Matrix.trace (R ^ (a + 1) * (G * Gᵀ)) = S a :=
    trace_inv_gram_pow_succ_mul_gram G hpd a
  change gramSoftMinLaplacian n 0 G =
    2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (G * Gᵀ)) +
      4 * ((n : ℝ) + 1) * S n ^ (-(n : ℝ)⁻¹ - 2) *
        Matrix.trace (R ^ (2 * n + 2) * (G * Gᵀ)) -
      S n ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ a ∈ Finset.range (n + 1), (2 * Matrix.trace (R ^ (n + 2) * (G * Gᵀ)) +
          S (n - a + 1) * Matrix.trace (R ^ (a + 1) * (G * Gᵀ)) +
          S (a + 1) * Matrix.trace (R ^ (n - a + 1) * (G * Gᵀ))) at h
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, htrace,
    show n + 2 = (n + 1) + 1 by omega, htrace] at h
  simp_rw [htrace] at h
  have hweight : Matrix.trace (inversePowerSoftMinWeight n (G * Gᵀ)) =
      S n ^ (-(n : ℝ)⁻¹ - 1) * S (n + 1) := by
    rw [inversePowerSoftMinWeight, Matrix.trace_smul, smul_eq_mul]
  rw [hweight] at h
  have hpower : S n ^ (-(n : ℝ)⁻¹ - 2) = S n ^ (-(n : ℝ)⁻¹ - 1) / S n := by
    rw [show -(n : ℝ)⁻¹ - 2 = (-(n : ℝ)⁻¹ - 1) - 1 by ring,
      Real.rpow_sub_one hT.ne']
  rw [hpower] at h
  simp only [Finset.sum_add_distrib] at h
  rw [sum_trace_power_reflect S n] at h
  have hSzero : S 0 = Fintype.card ι := by simp [S]
  have hsplit : (∑ a ∈ Finset.range (n + 1), S (a + 1) * S (n - a)) =
      (∑ a ∈ Finset.range n, S (a + 1) * S (n - a)) + S (n + 1) * Fintype.card ι := by
    rw [Finset.sum_range_succ, Nat.sub_self, hSzero]
  rw [hsplit] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  rw [h]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Every finite positive inverse power has the sharp hard-edge Gram
Laplacian upper bound, without an eigenvalue-separation condition.
Source: the user's finite trace-product defects; atlas
`wishart-lambda-min-tail` (helper). -/
theorem gramSoftMinLaplacian_unshifted_le [Nonempty ι] (n : ℕ) (hn : 0 < n)
    (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef)
    (hgap : 0 ≤ (Fintype.card κ : ℝ) - Fintype.card ι + 1) :
    gramSoftMinLaplacian n 0 G ≤ 2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) := by
  let R := (G * Gᵀ)⁻¹
  let S := fun a : ℕ => Matrix.trace (R ^ a)
  let c := S n ^ (-(n : ℝ)⁻¹ - 1)
  have hT : 0 < S n := trace_pow_pos_of_posDef hpd.inv n
  have hc : 0 ≤ c := Real.rpow_nonneg hT.le _
  have hmain : c * S (n + 1) ≤ 1 := by
    simpa only [c, S, R, inversePowerSoftMinWeight, Matrix.trace_smul, smul_eq_mul] using
      trace_inversePowerSoftMinWeight_le_one n hn hpd
  have hprod : S (2 * n + 1) ≤ S n * S (n + 1) := by
    simpa only [show n + (n + 1) = 2 * n + 1 by omega] using
      trace_pow_le_trace_pow_mul_trace_pow hpd.inv.posSemidef n (n + 1)
  have hbracket : 0 ≤ S (n + 1) - S (2 * n + 1) / S n := by
    have hdiv : S (2 * n + 1) / S n ≤ S (n + 1) :=
      (div_le_iff₀ hT).2 (by simpa only [mul_comm] using hprod)
    linarith
  have hsum : 0 ≤ ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1)) := by
    apply Finset.sum_nonneg
    intro a ha
    have ha' : a < n := Finset.mem_range.mp ha
    have h := trace_pow_le_trace_pow_mul_trace_pow hpd.inv.posSemidef (a + 1) (n - a)
    have he : a + 1 + (n - a) = n + 1 := by omega
    rw [he] at h
    exact sub_nonneg.mpr h
  have heq := gramSoftMinLaplacian_unshifted_eq n G hpd
  change gramSoftMinLaplacian n 0 G =
    2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) -
      4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) -
      2 * c * ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1)) at heq
  rw [heq]
  calc _ ≤ 2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) := by
        have h1 : 0 ≤ 4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) := by positivity
        have h2 : 0 ≤ 2 * c * ∑ a ∈ Finset.range n,
            (S (a + 1) * S (n - a) - S (n + 1)) := by positivity
        linarith
    _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hgap)
        simpa only [mul_one, mul_assoc] using h

omit [Fintype κ] [DecidableEq κ] in
/-- The scalar gradient coefficient is the `(n+1)`st power of the
inverse-power minimum. Source: positive trace-power algebra; atlas
`wishart-lambda-min-tail` (cutoff helper). -/
theorem inversePowerSoftMin_coefficient_eq_pow [Nonempty ι] (n : ℕ) (hn : 0 < n)
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) = inversePowerSoftMin n A ^ (n + 1) := by
  have hT : 0 < Matrix.trace (A⁻¹ ^ n) := trace_pow_pos_of_posDef hA.inv n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inversePowerSoftMin, ← Real.rpow_natCast _ (n + 1), ← Real.rpow_mul hT.le]
  congr 1
  push_cast
  field_simp
  ring

omit [DecidableEq κ] in
/-- The unshifted Gram gradient has exact Euler contraction twice the
inverse-power minimum. Source: the user's finite operator refinement;
atlas `wishart-lambda-min-tail` (helper). -/
theorem frobInner_gramSoftMinGradient_unshifted_eq [Nonempty ι]
    (n : ℕ) (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) :
    frobInner G (gramSoftMinGradient n 0 G) = 2 * inversePowerSoftMin n (G * Gᵀ) := by
  have hT : 0 < Matrix.trace ((G * Gᵀ)⁻¹ ^ n) := trace_pow_pos_of_posDef hpd.inv n
  rw [frobInner_gramSoftMinGradient_eq_trace, regularizedGram_zero,
    inversePowerSoftMinWeight, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    trace_inv_gram_pow_succ_mul_gram G hpd n]
  congr 1
  nth_rw 2 [← Real.rpow_one (Matrix.trace ((G * Gᵀ)⁻¹ ^ n))]
  rw [← Real.rpow_add hT]
  congr 1
  ring

omit [DecidableEq κ] in
/-- The unshifted Gram gradient energy has an exact inverse trace-power
formula. Source: the user's finite operator refinement; atlas
`wishart-lambda-min-tail` (helper). -/
theorem frobSq_gramSoftMinGradient_unshifted_eq (n : ℕ)
    (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) :
    let R := (G * Gᵀ)⁻¹
    let c := Matrix.trace (R ^ n) ^ (-(n : ℝ)⁻¹ - 1)
    frobSq (gramSoftMinGradient n 0 G) = 4 * c ^ 2 * Matrix.trace (R ^ (2 * n + 1)) := by
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := frobSq_gramSoftMinGradient_eq_trace n 0 G hreg
  simp only [regularizedGram_zero] at h
  rw [inversePowerSoftMinWeight, pow_two, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← pow_add,
    show n + 1 + (n + 1) = (2 * n + 1) + 1 by omega,
    trace_inv_gram_pow_succ_mul_gram G hpd] at h
  simpa only [pow_two, mul_assoc] using h

omit [DecidableEq κ] in
/-- The unshifted Gram gradient energy is at most four times its scalar
minimum approximation. Source: positive trace-product defects;
atlas `wishart-lambda-min-tail` (helper). -/
theorem frobSq_gramSoftMinGradient_unshifted_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) :
    frobSq (gramSoftMinGradient n 0 G) ≤ 4 * inversePowerSoftMin n (G * Gᵀ) := by
  let R := (G * Gᵀ)⁻¹
  let S := fun a : ℕ => Matrix.trace (R ^ a)
  let c := S n ^ (-(n : ℝ)⁻¹ - 1)
  have hT : 0 < S n := trace_pow_pos_of_posDef hpd.inv n
  have hPhi : c * S n = inversePowerSoftMin n (G * Gᵀ) := by
    dsimp only [c, inversePowerSoftMin, S, R]
    nth_rw 2 [← Real.rpow_one (Matrix.trace ((G * Gᵀ)⁻¹ ^ n))]
    rw [← Real.rpow_add hT]
    congr 1; ring
  have hmain : c * S (n + 1) ≤ 1 := by
    simpa only [c, S, R, inversePowerSoftMinWeight, Matrix.trace_smul, smul_eq_mul] using
      trace_inversePowerSoftMinWeight_le_one n hn hpd
  have hprod : S (2 * n + 1) ≤ S n * S (n + 1) := by
    simpa only [show n + (n + 1) = 2 * n + 1 by omega] using
      trace_pow_le_trace_pow_mul_trace_pow hpd.inv.posSemidef n (n + 1)
  calc frobSq (gramSoftMinGradient n 0 G) = 4 * c ^ 2 * S (2 * n + 1) :=
        frobSq_gramSoftMinGradient_unshifted_eq n G hpd
    _ ≤ 4 * c ^ 2 * (S n * S (n + 1)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 4 * inversePowerSoftMin n (G * Gᵀ) * (c * S (n + 1)) := by rw [← hPhi]; ring
    _ ≤ 4 * inversePowerSoftMin n (G * Gᵀ) := by
        have hnn : 0 ≤ inversePowerSoftMin n (G * Gᵀ) := Real.rpow_nonneg hT.le _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmain (by positivity)

omit [Fintype κ] [DecidableEq κ] in
/-- The inverse-power minimum is below the reciprocal of every inverse
eigenvalue. Source: one summand of the positive trace power;
atlas `wishart-lambda-min-tail` (cutoff helper). -/
theorem inversePowerSoftMin_le_inv_inverse_eigenvalue [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A : Matrix ι ι ℝ) (hA : A.PosDef) (i : ι) :
    inversePowerSoftMin n A ≤ (hA.inv.isHermitian.eigenvalues i)⁻¹ := by
  have hb := hA.inv.eigenvalues_pos i
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsingle : hA.inv.isHermitian.eigenvalues i ^ n ≤ Matrix.trace (A⁻¹ ^ n) := by
    rw [trace_pow_eq_sum_eigenvalues hA.inv.isHermitian]
    exact Finset.single_le_sum (fun j _ => pow_nonneg (hA.inv.eigenvalues_pos j).le n)
      (Finset.mem_univ i)
  have h := Real.rpow_le_rpow_of_nonpos (pow_pos hb n) hsingle
    (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg n)))
  rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hb.le, mul_neg,
    mul_inv_cancel₀ hn0, Real.rpow_neg_one] at h
  exact h

omit [Fintype κ] [DecidableEq κ] in
/-- The inverse spectral norm is bounded by the reciprocal inverse-power
minimum. Source: the maximal nonnegative inverse eigenvalue and a trace
summand; atlas `wishart-lambda-min-tail` (cutoff helper). -/
theorem specNorm_inv_le_inv_inversePowerSoftMin [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    specNorm A⁻¹ ≤ (inversePowerSoftMin n A)⁻¹ := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.inv.isHermitian.eigenvalues).1
  dsimp only at hi
  have hb := hA.inv.eigenvalues_pos i
  have hnorm : specNorm A⁻¹ = hA.inv.isHermitian.eigenvalues i := by
    rw [specNorm_eq_norm_eigenvalues hA.inv.isHermitian, ← hi, Real.norm_of_nonneg hb.le]
  rw [hnorm]
  have hF : 0 < inversePowerSoftMin n A := Real.rpow_pos_of_pos (trace_pow_pos_of_posDef hA.inv n) _
  have h := one_div_le_one_div_of_le hF (inversePowerSoftMin_le_inv_inverse_eigenvalue n hn A hA i)
  simpa only [one_div, inv_inv] using h

omit [DecidableEq κ] in
/-- A Gram matrix outside the positive definite domain has zero total
inverse. Source: Gram positivity and the singular inverse convention;
atlas `wishart-lambda-min-tail` (cutoff helper). -/
theorem inv_gram_eq_zero_of_not_posDef (G : Matrix ι κ ℝ)
    (hnot : ¬(G * Gᵀ).PosDef) : (G * Gᵀ)⁻¹ = 0 := by
  have hPSD : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose G
  have hnotunit : ¬IsUnit (G * Gᵀ) := fun hunit => hnot ((hPSD.posDef_iff_isUnit).2 hunit)
  have hnotdet : ¬IsUnit (G * Gᵀ).det := fun hdet =>
    hnotunit ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
  exact Matrix.nonsing_inv_apply_not_isUnit _ hnotdet

omit [DecidableEq κ] in
/-- The unshifted inverse-power minimum is zero outside the positive
definite Gram domain, using the total inverse convention. Source: singular
Gram inverse; atlas `wishart-lambda-min-tail` (cutoff helper). -/
theorem inversePowerSoftMin_gram_eq_zero_of_not_posDef (n : ℕ) (hn : 0 < n)
    (G : Matrix ι κ ℝ) (hnot : ¬(G * Gᵀ).PosDef) :
    inversePowerSoftMin n (G * Gᵀ) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inversePowerSoftMin, inv_gram_eq_zero_of_not_posDef G hnot,
    zero_pow hn.ne', Matrix.trace_zero, Real.zero_rpow (neg_ne_zero.mpr (inv_ne_zero hn0))]

/-- The unshifted inverse-power minimum is bounded by the exact squared
smallest singular value for every matrix, with zero on the singular domain.
Source: inverse eigenvalue trace comparison; atlas `wishart-lambda-min-tail` (helper). -/
theorem inversePowerSoftMin_gram_le_sigmaMin_sq [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) :
    inversePowerSoftMin n (G * Gᵀ) ≤ sigmaMin Gᵀ ^ 2 := by
  by_cases hpd : (G * Gᵀ).PosDef
  · have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hreg.inv.isHermitian.eigenvalues).1
    dsimp only at hi
    have hmax (j : ι) : hreg.inv.isHermitian.eigenvalues j ≤ hreg.inv.isHermitian.eigenvalues i := by
      have h := norm_le_pi_norm hreg.inv.isHermitian.eigenvalues j
      rw [← hi, Real.norm_of_nonneg (hreg.inv.eigenvalues_pos j).le,
        Real.norm_of_nonneg (hreg.inv.eigenvalues_pos i).le] at h
      exact h
    have hX := sigmaMin_transpose_sq_eq_inv_inverse_eigenvalue_sub 0 G hreg i hmax
    have hF := inversePowerSoftMin_le_inv_inverse_eigenvalue n hn (regularizedGram 0 G) hreg i
    rw [sub_zero] at hX
    simpa only [regularizedGram_zero] using hF.trans_eq hX.symm
  · rw [inversePowerSoftMin_gram_eq_zero_of_not_posDef n hn G hpd]
    exact sq_nonneg _

omit [DecidableEq κ] in
/-- The unshifted Gram gradient is zero outside the positive definite
Gram domain. Source: the total singular inverse convention; atlas
`wishart-lambda-min-tail` (cutoff helper). -/
theorem gramSoftMinGradient_unshifted_eq_zero_of_not_posDef (n : ℕ)
    (G : Matrix ι κ ℝ) (hnot : ¬(G * Gᵀ).PosDef) : gramSoftMinGradient n 0 G = 0 := by
  rw [gramSoftMinGradient, regularizedGram_zero, inversePowerSoftMinWeight,
    inv_gram_eq_zero_of_not_posDef G hnot, zero_pow (Nat.succ_ne_zero n),
    smul_zero, Matrix.zero_mul, smul_zero]

/-- The unshifted first Gram chain coefficient equals the corresponding
gradient entry along every coordinate line, including singular points.
Source: trace pairing and Gram positivity; atlas `wishart-lambda-min-tail` (helper). -/
theorem inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient (n : ℕ)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) (t : ℝ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = gramSoftMinGradient n 0 (G + t • E) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hD : E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ) =
      E * (G + t • E)ᵀ + (G + t • E) * Eᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  have hPSD : (regularizedGram 0 (G + t • E)).PosSemidef := by
    rw [regularizedGram_zero]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (G + t • E)
  have hP : (inversePowerSoftMinWeight n (regularizedGram 0 (G + t • E)))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram 0 (G + t • E)) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n hPSD).isHermitian).eq
  change inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = _
  rw [hD, inversePowerSoftMinFirst_eq_trace_weight_mul, trace_mul_gram_direction _ hP]
  rfl

/-- At a positive definite unshifted Gram point, the scalar function has
its actual gradient entry as coordinate derivative. Source: local inverse
calculus; atlas `wishart-lambda-min-tail` (cutoff helper). -/
theorem hasDerivAt_gramSoftMin_unshifted_single_zero [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) (i : ι) (j : κ) :
    HasDerivAt (fun x : ℝ => inversePowerSoftMin n
      ((G + x • Matrix.single i j 1) * (G + x • Matrix.single i j 1)ᵀ))
      (gramSoftMinGradient n 0 G i j) 0 := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hA := hasDerivAt_regularizedGram_add_smul 0 G E 0
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := hasDerivAt_inversePowerSoftMin_curve n hn hA
    (by simpa only [zero_smul, add_zero] using hreg.isUnit)
    (by simpa only [zero_smul, add_zero] using trace_pow_pos_of_posDef hreg.inv n)
  rw [inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient] at h
  simpa only [regularizedGram_zero, zero_smul, add_zero] using h

/-- At a positive definite unshifted Gram point, the actual gradient
entry has the explicit second Gram coordinate derivative as derivative.
Source: local inverse calculus; atlas `wishart-lambda-min-tail` (cutoff helper). -/
theorem hasDerivAt_gramSoftMinGradient_unshifted_single_zero [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (hpd : (G * Gᵀ).PosDef) (i : ι) (j : κ) :
    HasDerivAt (fun x : ℝ => gramSoftMinGradient n 0 (G + x • Matrix.single i j 1) i j)
      (gramSoftMinSecond n 0 G (Matrix.single i j 1)) 0 := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hA := hasDerivAt_regularizedGram_add_smul 0 G E 0
  have hD := hasDerivAt_regularizedGram_first G E 0
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := hasDerivAt_inversePowerSoftMinFirst_curve n hn hA hD
    (by simpa only [zero_smul, add_zero] using hreg.isUnit)
    (by simpa only [zero_smul, add_zero] using trace_pow_pos_of_posDef hreg.inv n)
  have heq : (fun t : ℝ => inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ))) =
      (fun t : ℝ => gramSoftMinGradient n 0 (G + t • E) i j) := by
    funext t
    exact inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient n G i j t
  rw [heq] at h
  simpa only [mul_zero, zero_smul, add_zero, gramSoftMinSecond] using h

omit [DecidableEq κ] in
/-- Failure of positive definiteness of a Gram matrix makes its exact
squared smallest singular value zero. Source: the inverse spectral bridge;
atlas `wishart-lambda-min-tail` (cutoff continuity helper). -/
theorem sigmaMin_transpose_sq_eq_zero_of_not_posDef (G : Matrix ι κ ℝ)
    (hnot : ¬(G * Gᵀ).PosDef) : sigmaMin Gᵀ ^ 2 = 0 := by
  have h := specNorm_inv_self_mul_transpose_eq G
  rw [inv_gram_eq_zero_of_not_posDef G hnot, specNorm_zero, one_div] at h
  exact inv_eq_zero.mp h.symm

omit [DecidableEq κ] in
/-- The total unshifted inverse-power minimum is nonnegative everywhere.
Source: Gram inverse positivity; atlas `wishart-lambda-min-tail` (helper). -/
theorem inversePowerSoftMin_gram_nonneg (n : ℕ) (G : Matrix ι κ ℝ) :
    0 ≤ inversePowerSoftMin n (G * Gᵀ) := by
  have hPSD : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose G
  exact Real.rpow_nonneg (hPSD.inv.pow n).trace_nonneg _

omit [DecidableEq κ] in
/-- The exact unshifted Euler identity holds globally, including singular
Grams where both sides vanish. Source: finite operator refinement;
atlas `wishart-lambda-min-tail` (helper). -/
theorem frobInner_gramSoftMinGradient_unshifted_eq_of_pos [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) :
    frobInner G (gramSoftMinGradient n 0 G) = 2 * inversePowerSoftMin n (G * Gᵀ) := by
  by_cases hpd : (G * Gᵀ).PosDef
  · exact frobInner_gramSoftMinGradient_unshifted_eq n G hpd
  · rw [gramSoftMinGradient_unshifted_eq_zero_of_not_posDef n G hpd,
      inversePowerSoftMin_gram_eq_zero_of_not_posDef n hn G hpd, frobInner_zero_right, mul_zero]

omit [DecidableEq κ] in
/-- The unshifted gradient energy bound holds globally, including singular
Grams where both sides vanish. Source: finite operator refinement;
atlas `wishart-lambda-min-tail` (helper). -/
theorem frobSq_gramSoftMinGradient_unshifted_le_of_pos [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) :
    frobSq (gramSoftMinGradient n 0 G) ≤ 4 * inversePowerSoftMin n (G * Gᵀ) := by
  by_cases hpd : (G * Gᵀ).PosDef
  · exact frobSq_gramSoftMinGradient_unshifted_le n hn G hpd
  · rw [gramSoftMinGradient_unshifted_eq_zero_of_not_posDef n G hpd,
      inversePowerSoftMin_gram_eq_zero_of_not_posDef n hn G hpd, frobSq_zero, mul_zero]

end NLAlib
