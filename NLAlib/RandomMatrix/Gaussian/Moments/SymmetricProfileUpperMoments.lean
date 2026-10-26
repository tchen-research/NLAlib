import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileComparison
import NLAlib.Matrix.Norms.SchattenNorms
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Sharp profile-sensitive even Gaussian Schatten moments

Rescaling the actual Gaussian profile and rounding its effective dimension
turn the normalized diagram comparison into the two-term even-moment bound.
The constant is universal and independent of the matrix dimension and moment
order. Only deterministic variance-profile power sums appear as hypotheses.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 2.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] in
private theorem symmetricGaussianMatrix_profile_smul (b G : Matrix n n ℝ) (c : ℝ) :
    symmetricGaussianMatrix (c • b) G = c • symmetricGaussianMatrix b G := by
  ext i j
  simp only [symmetricGaussianMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The actual even Gaussian Schatten moment satisfies a universal two-term
variance-profile bound. The inputs `A` and `B` bound the rooted row-variance
and row-cap power sums, respectively. No Gaussian estimate is assumed. -/
theorem integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_le
    (b : Matrix n n ℝ) (hb : b.IsSymm) (p : ℕ) (hp : 0 < p)
    (s : n → ℝ) (hcap : ∀ i j, b i j ^ 2 ≤ s i)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hd : (∑ i, (∑ j, b i j ^ 2) ^ p) ≤ A ^ (2 * p))
    (hs : (∑ i, s i ^ p) ≤ B ^ (2 * p)) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix b G) (2 * p : ℕ) ^ (2 * p)
      ∂gaussianMatrix n n) ≤ (24 * (A + Real.sqrt p * B)) ^ (2 * p) := by
  classical
  let r := ⌈(A / B) ^ 2⌉₊ + 1
  have hr : 0 < r := by omega
  have hrlo : (A / B) ^ 2 ≤ (r : ℝ) := by
    have h := Nat.le_ceil ((A / B) ^ 2)
    dsimp [r]
    push_cast
    linarith
  have hrhi : (r : ℝ) ≤ (A / B) ^ 2 + 2 := by
    have h := Nat.ceil_lt_add_one (sq_nonneg (A / B))
    dsimp [r]
    push_cast
    linarith
  let bn : Matrix n n ℝ := B⁻¹ • b
  let sn : n → ℝ := fun i => B⁻¹ ^ 2 * s i
  have hbns : bn.IsSymm := hb.smul _
  have hcapn (i j : n) : bn i j ^ 2 ≤ sn i := by
    simpa only [bn, sn, Matrix.smul_apply, smul_eq_mul, mul_pow] using
      mul_le_mul_of_nonneg_left (hcap i j) (sq_nonneg B⁻¹)
  have hrow (i : n) : (∑ j, bn i j ^ 2) = B⁻¹ ^ 2 * (∑ j, b i j ^ 2) := by
    simp only [bn, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hdn : (∑ i, (∑ j, bn i j ^ 2) ^ p) ≤ (r : ℝ) ^ p := by
    simp_rw [hrow, mul_pow, ← pow_mul, ← Finset.mul_sum]
    calc
      B⁻¹ ^ (2 * p) * (∑ i, (∑ j, b i j ^ 2) ^ p) ≤
          B⁻¹ ^ (2 * p) * A ^ (2 * p) :=
        mul_le_mul_of_nonneg_left hd (pow_nonneg (inv_nonneg.mpr hB.le) _)
      _ = ((A / B) ^ 2) ^ p := by
        simp only [div_eq_mul_inv, mul_pow, ← pow_mul]
        ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hrlo p
  have hsn : (∑ i, sn i ^ p) ≤ 1 := by
    simp only [sn, mul_pow, ← pow_mul, ← Finset.mul_sum]
    calc
      B⁻¹ ^ (2 * p) * (∑ i, s i ^ p) ≤ B⁻¹ ^ (2 * p) * B ^ (2 * p) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr hB.le) _)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hB.ne', one_pow]
  have hn := integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_le_of_power_sums
    bn hbns p r hp hr sn hcapn hdn hsn
  have hbscale : b = B • bn := by
    dsimp [bn]
    rw [smul_smul, mul_inv_cancel₀ hB.ne', one_smul]
  have hq : (0 : ℝ) < (2 * p : ℕ) := by positivity
  have hscale (G : Matrix n n ℝ) :
      schattenNormReal (symmetricGaussianMatrix b G) (2 * p : ℕ) ^ (2 * p) =
        B ^ (2 * p) *
          schattenNormReal (symmetricGaussianMatrix bn G) (2 * p : ℕ) ^ (2 * p) := by
    conv_lhs => rw [hbscale, symmetricGaussianMatrix_profile_smul]
    rw [schattenNormReal_smul _ _ hq, abs_of_pos hB, mul_pow]
  have hsqrtr : Real.sqrt r ≤ A / B + 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have hab : 0 ≤ A / B := div_nonneg hA hB.le
    nlinarith
  have hsqrtp : (1 : ℝ) ≤ Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hp : (1 : ℝ) ≤ p)
  have hconstant : B * (8 * (Real.sqrt r + Real.sqrt p)) ≤
      24 * (A + Real.sqrt p * B) := by
    have h := mul_le_mul_of_nonneg_left hsqrtr hB.le
    rw [mul_add, mul_div_cancel₀ _ hB.ne'] at h
    nlinarith [mul_le_mul_of_nonneg_right hsqrtp hB.le]
  calc
    _ = B ^ (2 * p) * ∫ G,
        schattenNormReal (symmetricGaussianMatrix bn G) (2 * p : ℕ) ^ (2 * p)
          ∂gaussianMatrix n n := by simp_rw [hscale]; exact integral_const_mul _ _
    _ ≤ B ^ (2 * p) * (8 * (Real.sqrt r + Real.sqrt p)) ^ (2 * p) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg hB.le _)
    _ = (B * (8 * (Real.sqrt r + Real.sqrt p))) ^ (2 * p) := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hconstant _

/-- The sharp two-term upper bound for every positive even Schatten moment
of the actual symmetric Gaussian profile ensemble. The profile terms are
the row-variance power sum and the row-maximum power sum. The constant `24`
is uniform in the matrix dimension and even moment order.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Theorem 1.1,
even-exponent upper half.
atlas: heterogeneous-gaussian-schatten-moments (partial) -/
theorem integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_root_le
    (b : Matrix n n ℝ) (hb : b.IsSymm) (p : ℕ) (hp : 0 < p) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix b G) (2 * p : ℕ) ^ (2 * p)
      ∂gaussianMatrix n n) ^ (((2 * p : ℕ) : ℝ)⁻¹) ≤
        24 * ((∑ i, (∑ j, b i j ^ 2) ^ p) ^ (((2 * p : ℕ) : ℝ)⁻¹) +
          Real.sqrt p * (∑ i, ‖b i‖ ^ (2 * p)) ^ (((2 * p : ℕ) : ℝ)⁻¹)) := by
  classical
  let q := 2 * p
  have hq : 0 < q := by dsimp [q]; omega
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let D : ℝ := ∑ i, (∑ j, b i j ^ 2) ^ p
  let S : ℝ := ∑ i, ‖b i‖ ^ q
  let A : ℝ := D ^ ((q : ℝ)⁻¹)
  let B : ℝ := S ^ ((q : ℝ)⁻¹)
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => pow_nonneg
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  have hA : 0 ≤ A := Real.rpow_nonneg hD _
  have hB : 0 ≤ B := Real.rpow_nonneg hS _
  have hApow : A ^ q = D := by
    rw [← Real.rpow_natCast, Real.rpow_inv_rpow hD hqr.ne']
  have hBpow : B ^ q = S := by
    rw [← Real.rpow_natCast, Real.rpow_inv_rpow hS hqr.ne']
  by_cases hBzero : B = 0
  · have hSzero : S = 0 := by simpa only [hBzero, zero_pow hq.ne'] using hBpow.symm
    have hbzero : b = 0 := by
      ext i j
      have hi : ‖b i‖ ^ q ≤ 0 := by
        calc
          _ ≤ S := Finset.single_le_sum (fun k _ => pow_nonneg (norm_nonneg (b k)) q)
            (Finset.mem_univ i)
          _ = 0 := hSzero
      have hn : ‖b i‖ = 0 := (pow_eq_zero_iff hq.ne').mp
        (le_antisymm hi (pow_nonneg (norm_nonneg _) _))
      exact congrFun (norm_eq_zero.mp hn) j
    have hz (G : Matrix n n ℝ) : symmetricGaussianMatrix b G = 0 := by
      ext i j
      simp [hbzero, symmetricGaussianMatrix]
    have hnorm (G : Matrix n n ℝ) :
        schattenNormReal (symmetricGaussianMatrix b G) q = 0 := by
      rw [hz, schattenNormReal_zero hqr]
    change (∫ G, schattenNormReal (symmetricGaussianMatrix b G) q ^ q ∂gaussianMatrix n n) ^
      ((q : ℝ)⁻¹) ≤ 24 * (A + Real.sqrt p * B)
    simp only [hnorm, zero_pow hq.ne', integral_zero,
      Real.zero_rpow (inv_ne_zero hqr.ne')]
    positivity
  have hcap (i j : n) : b i j ^ 2 ≤ ‖b i‖ ^ 2 := by
    have h := norm_le_pi_norm (b i) j
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hbound := integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_le
    b hb p hp (fun i => ‖b i‖ ^ 2) hcap A B hA (lt_of_le_of_ne hB (Ne.symm hBzero))
    (by change D ≤ A ^ q; exact hApow.ge)
    (by simpa only [← pow_mul] using hBpow.ge)
  have hM : 0 ≤ ∫ G, schattenNormReal (symmetricGaussianMatrix b G) q ^ q
      ∂gaussianMatrix n n := integral_nonneg fun G =>
    pow_nonneg (schattenNormReal_nonneg _ _) _
  have hroot := Real.rpow_le_rpow hM hbound (inv_nonneg.mpr hqr.le)
  rw [← Real.rpow_natCast, Real.rpow_rpow_inv (by positivity) hqr.ne'] at hroot
  exact hroot

/-- The native extended-exponent Schatten formulation of the sharp profile
upper moment estimate, for every positive even exponent. Its profile and
root exponents agree exactly with the all-real-exponent moment statement.
atlas: heterogeneous-gaussian-schatten-moments (partial) -/
theorem integral_schattenNorm_symmetricGaussianMatrix_rpow_root_le_even
    (b : Matrix n n ℝ) (hb : b.IsSymm) (p : ℕ) (hp : 0 < p) :
    (∫ G, schattenNorm (symmetricGaussianMatrix b G)
        (ENNReal.ofReal ((2 * p : ℕ) : ℝ)) ^ (((2 * p : ℕ) : ℝ))
      ∂gaussianMatrix n n) ^ (((2 * p : ℕ) : ℝ)⁻¹) ≤
        24 * ((∑ i, (∑ j, b i j ^ 2) ^ ((((2 * p : ℕ) : ℝ)) / 2)) ^
            (((2 * p : ℕ) : ℝ)⁻¹) +
          Real.sqrt ((2 * p : ℕ) : ℝ) *
            (∑ i, ‖b i‖ ^ (((2 * p : ℕ) : ℝ))) ^ (((2 * p : ℕ) : ℝ)⁻¹)) := by
  have hq : (0 : ℝ) ≤ (2 * p : ℕ) := Nat.cast_nonneg _
  have hhalf : (((2 * p : ℕ) : ℝ)) / 2 = p := by push_cast; ring
  simp only [schattenNorm_ofReal _ hq, hhalf, Real.rpow_natCast]
  apply (integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_root_le b hb p hp).trans
  gcongr
  exact_mod_cast (by omega : p ≤ 2 * p)

end NLAlib
