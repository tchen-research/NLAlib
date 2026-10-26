import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileUpperMoments
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileLowerMoments

/-!
# Gaussian operator means on finite coordinate supports

Choosing an even Schatten exponent at least the binary logarithm of the
coordinate support gives a dimension-free bound on the mean operator norm.
This is the block-mean estimate in Latała--van Handel--Youssef (2018), Section 3.2.
All expectations use the actual symmetric Gaussian matrix law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

private theorem sum_pow_le_card_mul_pow_of_support
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (f : ι → ℝ)
    {a : ℝ} (hf : ∀ i, 0 ≤ f i) (ha : ∀ i ∈ S, f i ≤ a)
    (hzero : ∀ i ∉ S, f i = 0) {q : ℕ} (hq : 0 < q) :
    (∑ i, f i ^ q) ≤ S.card * a ^ q := by
  classical
  calc
    _ = ∑ i ∈ S, f i ^ q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [hzero i hi, zero_pow (Nat.ne_of_gt hq)]
    _ ≤ ∑ _i ∈ S, a ^ q := Finset.sum_le_sum fun i hi =>
      pow_le_pow_left₀ (hf i) (ha i hi) _
    _ = _ := by simp

/-- A symmetric Gaussian profile supported on at most `2^(2p)` rows, with
row energy at most `a` and entry magnitude at most `m`, has expected spectral
norm at most `48 (a + sqrt p * m)`. There is no ambient-dimension factor. -/
theorem integral_specNorm_symmetricGaussianMatrix_le_of_support_card
    {n : ℕ} (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm) (S : Finset (Fin n))
    (p : ℕ) (hp : 0 < p) (hcard : S.card ≤ 2 ^ (2 * p))
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hrow : ∀ i, ∑ j, b i j ^ 2 ≤ a ^ 2)
    (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2)
    (hzero : ∀ i ∉ S, ∀ j, b i j = 0) :
    (∫ G, specNorm (symmetricGaussianMatrix b G) ∂gaussianMatrix (Fin n) (Fin n)) ≤
      48 * (a + Real.sqrt p * m) := by
  classical
  by_cases hm0 : m = 0
  · have hb0 : b = 0 := by
      ext i j
      change b i j = 0
      have h := hcap i j
      rw [hm0] at h
      nlinarith [sq_nonneg (b i j)]
    subst b
    simp only [symmetricGaussianMatrix, Matrix.zero_apply, zero_mul]
    have hz : (Matrix.of fun _ _ : Fin n => (0 : ℝ)) = 0 := rfl
    rw [hz]
    simp only [specNorm_zero, integral_zero, hm0, mul_zero, add_zero]
    positivity
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  let s : Fin n → ℝ := fun i => if i ∈ S then m ^ 2 else 0
  have hs0 (i : Fin n) : 0 ≤ s i := by dsimp [s]; split_ifs <;> positivity
  have hcap' (i j : Fin n) : b i j ^ 2 ≤ s i := by
    dsimp [s]
    split_ifs with hi
    · exact hcap i j
    · rw [hzero i hi j]; simp
  have hD : (∑ i, (∑ j, b i j ^ 2) ^ p) ≤ (2 * a) ^ (2 * p) := by
    have h := sum_pow_le_card_mul_pow_of_support S (fun i => ∑ j, b i j ^ 2)
      (fun i => Finset.sum_nonneg fun j _ => sq_nonneg _) (fun i _ => hrow i)
      (fun i hi => by simp [hzero i hi]) hp
    apply h.trans
    rw [← pow_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg ha _)
  have hS : (∑ i, s i ^ p) ≤ (2 * m) ^ (2 * p) := by
    have h := sum_pow_le_card_mul_pow_of_support S s (a := m ^ 2) hs0
      (fun i hi => by simp [s, hi]) (fun i hi => by simp [s, hi]) hp
    apply h.trans
    rw [← pow_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hm _)
  have hraw := integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_le b hb p hp
    s hcap' (2 * a) (2 * m) (by positivity) (by positivity) hD hS
  let q : ℝ := (2 * p : ℕ)
  have hq : 2 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 2 ≤ 2 * p)
  have hq0 : 0 < q := by linarith
  let f : Matrix (Fin n) (Fin n) ℝ → ℝ := fun G => schattenNormReal (symmetricGaussianMatrix b G) q
  have hf := memLp_schattenNormReal_symmetricGaussianMatrix b hq
  have hfint : Integrable f (gaussianMatrix (Fin n) (Fin n)) :=
    hf.integrable (ENNReal.one_le_ofReal.mpr (by linarith))
  have hbound : (∫ G, f G ^ q ∂gaussianMatrix (Fin n) (Fin n)) ≤
      (48 * (a + Real.sqrt p * m)) ^ q := by
    have hconst : 24 * (2 * a + Real.sqrt p * (2 * m)) =
        48 * (a + Real.sqrt p * m) := by ring
    simpa only [f, q, Real.rpow_natCast, hconst] using hraw
  have hmean := integral_rpow_root_le_of_integral_rpow_le hf.aestronglyMeasurable
    (fun G => schattenNormReal_nonneg _ _) (by norm_num : (0 : ℝ) < 1)
    (by linarith : (1 : ℝ) ≤ q) (by positivity : 0 ≤ 48 * (a + Real.sqrt p * m))
    (integrable_schattenNormReal_symmetricGaussianMatrix_rpow b hq) hbound
  have hspec : Integrable (fun G => specNorm (symmetricGaussianMatrix b G))
      (gaussianMatrix (Fin n) (Fin n)) := by
    apply hfint.mono' _
      (Filter.Eventually.of_forall fun G => by
        rw [Real.norm_of_nonneg (specNorm_nonneg _)]
        exact specNorm_le_schattenNormReal _ hq0)
    have hc : Continuous (specNorm : Matrix (Fin n) (Fin n) ℝ → ℝ) :=
      continuous_of_abs_sub_le_mul_frobNorm specNorm 1 fun X Y => by
        simpa only [one_mul] using abs_specNorm_sub_specNorm_le_frobNorm X Y
    exact (hc.measurable.comp (measurable_symmetricGaussianMatrix b)).aestronglyMeasurable
  apply (integral_mono hspec hfint (fun G => specNorm_le_schattenNormReal _ hq0)).trans
  simpa only [Real.rpow_one, inv_one] using hmean

end NLAlib
