import NLAlib.RandomMatrix.Gaussian.Basic.RowMixedNorm
import NLAlib.Probability.Gaussian.Moments.LowerMoments

/-!
# Row-cap lower moments of the actual Gaussian mixed norm

Select a maximum coefficient in each row. No independence between the
selected entries is needed: the mixed-norm power dominates their power sum,
and every individual coordinate has the actual scalar Gaussian law.
Source: Latała--van Handel--Youssef (2018), Section 3.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem integrable_abs_entry_rpow (b : Matrix ι ι ℝ) {p : ℝ} (hp : 0 ≤ p) (i j : ι) :
    Integrable (fun G => |symmetricGaussianMatrix b G i j| ^ p) (gaussianMatrix ι ι) := by
  have h := (memLp_symmetricGaussianMatrix_entry b i j (ENNReal.ofReal p)
    ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simpa only [ENNReal.toReal_ofReal hp, Real.norm_eq_abs] using h

private theorem integral_abs_entry_rpow (b : Matrix ι ι ℝ) (hb : b.IsSymm)
    (hb0 : ∀ i j, 0 ≤ b i j) {p : ℝ} (hp : 0 ≤ p) (i j : ι) :
    (∫ G, |symmetricGaussianMatrix b G i j| ^ p ∂gaussianMatrix ι ι) =
      b i j ^ p * (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1) := by
  simp_rw [symmetricGaussianMatrix_apply_of_isSymm b hb, abs_mul,
    abs_of_nonneg (hb0 i j), Real.mul_rpow (hb0 i j) (abs_nonneg _)]
  rw [integral_const_mul]
  congr 1
  exact integral_comp_gaussianMatrix_entry_eq (max i j) (min i j)
    (fun z : ℝ => |z| ^ p) (continuous_abs.rpow_const (fun _ => Or.inr hp)).measurable

/-- The scalar absolute Gaussian moment times the row-cap power sum is
bounded by the actual mixed-row-norm moment, at every real exponent at least two. -/
theorem integral_abs_rpow_gaussianReal_mul_sum_rowMax_le_integral_rowMixedNorm_rpow
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1) * (∑ i, ‖b i‖ ^ p) ≤
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p
        ∂gaussianMatrix ι ι := by
  classical
  have hp0 : 0 < p := by linarith
  have hpE : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  cases isEmpty_or_nonempty ι with
  | inl h =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
      exact integral_nonneg fun G => Real.rpow_nonneg (rowMixedNorm_nonneg _ _) _
  | inr h =>
      have hmax (i : ι) : ∃ j, b i j = ‖b i‖ := by
        obtain ⟨j, hj⟩ := (IsGreatest.pi_norm (b i)).1
        exact ⟨j, (Real.norm_of_nonneg (hb0 i j)) ▸ hj⟩
      choose f hf using hmax
      have hInt := (memLp_rowMixedNorm_symmetricGaussianMatrix b hpE (Real.toNNReal p)).integrable_norm_rpow'
      have hInt' : Integrable (fun G => rowMixedNorm (symmetricGaussianMatrix b G)
          (ENNReal.ofReal p) ^ p) (gaussianMatrix ι ι) := by
        simpa only [ENNReal.coe_toNNReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hp0.le,
          Real.coe_toNNReal p hp0.le,
          Real.norm_of_nonneg (rowMixedNorm_nonneg _ _)] using hInt
      have hselected : Integrable (fun G => ∑ i, |symmetricGaussianMatrix b G i (f i)| ^ p)
          (gaussianMatrix ι ι) := integrable_finsetSum _ fun i _ => integrable_abs_entry_rpow b hp0.le i _
      calc
        _ = ∫ G, ∑ i, |symmetricGaussianMatrix b G i (f i)| ^ p ∂gaussianMatrix ι ι := by
          rw [integral_finsetSum _ fun i _ => integrable_abs_entry_rpow b hp0.le i _]
          simp_rw [integral_abs_entry_rpow b hb hb0 hp0.le, hf]
          rw [← Finset.sum_mul, mul_comm]
        _ ≤ _ := integral_mono hselected hInt' (fun G => by
          rw [rowMixedNorm_ofReal_rpow _ hp0]
          apply Finset.sum_le_sum
          intro i _
          have hentry : |symmetricGaussianMatrix b G i (f i)| ^ 2 ≤
              rowSq (symmetricGaussianMatrix b G) i :=
            Finset.single_le_sum (fun j _ => sq_nonneg ‖symmetricGaussianMatrix b G i j‖)
              (Finset.mem_univ (f i))
          have hid : |symmetricGaussianMatrix b G i (f i)| ^ p =
              (|symmetricGaussianMatrix b G i (f i)| ^ 2) ^ (p / 2) := by
            rw [← Real.rpow_natCast_mul (abs_nonneg _) 2 (p / 2)]
            congr 1
            ring
          rw [hid]
          exact Real.rpow_le_rpow (sq_nonneg _) hentry (by linarith))

/-- The actual Gaussian mixed-row moment dominates `sqrt p` times its
row-cap profile, with the universal constant four. -/
theorem sqrt_mul_rowMax_profile_root_le_four_mul_integral_rowMixedNorm_rpow_root
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹ ≤
      4 * (∫ G, rowMixedNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p
        ∂gaussianMatrix ι ι) ^ p⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hscalarNN : 0 ≤ ∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1 :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hmaxNN : 0 ≤ ∑ i, ‖b i‖ ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hroot := Real.rpow_le_rpow (mul_nonneg hscalarNN hmaxNN)
    (integral_abs_rpow_gaussianReal_mul_sum_rowMax_le_integral_rowMixedNorm_rpow b hb hb0 hp)
    (inv_nonneg.mpr hp0.le)
  rw [Real.mul_rpow hscalarNN hmaxNN] at hroot
  have hmul := mul_le_mul_of_nonneg_right (sqrt_div_four_le_integral_abs_rpow_root_gaussianReal hp)
    (Real.rpow_nonneg hmaxNN p⁻¹)
  nlinarith [hmul.trans hroot]

end NLAlib
