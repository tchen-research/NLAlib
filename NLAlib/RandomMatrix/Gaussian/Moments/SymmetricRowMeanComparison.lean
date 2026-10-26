import NLAlib.RandomMatrix.Gaussian.Moments.ProfileHeadTailUpper
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricRowCapLower
import NLAlib.RandomMatrix.Gaussian.Basic.HeadTailSplit
import NLAlib.RandomMatrix.Gaussian.Basic.RowMixedNormReindex
import NLAlib.RandomMatrix.Gaussian.Spectral.SymmetricRowOperatorComparison

/-!
# Expected Gaussian Schatten norms versus mixed row norms

An exponentially sized head is controlled by the operator endpoint. The
principal tail has a small entry scale, so its row-cap moment is controlled
by the actual mixed-row mean and Gaussian concentration. This proves the
expectation comparison for every native exponent at least two, including
infinity, without dimension dependence.
Source: Latała--van Handel--Youssef (2018), Corollary 1.4 and Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

/-- An explicit universal constant for the full Gaussian Schatten-row
expectation comparison. -/
def gaussianRowMeanComparisonConstant : ℝ :=
  32 * gaussianRowOperatorComparisonConstant +
    512 * (gaussianAbsoluteLowerConstant⁻¹ + 4 + 32 / gaussianMaximumLowerConstant)

/-- The universal mean-comparison constant is at least one. -/
theorem one_le_gaussianRowMeanComparisonConstant : 1 ≤ gaussianRowMeanComparisonConstant := by
  unfold gaussianRowMeanComparisonConstant
  have hA := gaussianRowOperatorComparisonConstant_pos
  have hκ := gaussianAbsoluteLowerConstant_pos
  have hc := gaussianMaximumLowerConstant_pos
  have hi : 0 ≤ gaussianAbsoluteLowerConstant⁻¹ := by positivity
  have hd : 0 ≤ 32 / gaussianMaximumLowerConstant := by positivity
  linarith

/-- The full mean constant also covers the operator endpoint. -/
theorem gaussianRowOperatorComparisonConstant_le_mean :
    gaussianRowOperatorComparisonConstant ≤ gaussianRowMeanComparisonConstant := by
  unfold gaussianRowMeanComparisonConstant
  have hA := gaussianRowOperatorComparisonConstant_pos
  have hκ := gaussianAbsoluteLowerConstant_pos
  have hc := gaussianMaximumLowerConstant_pos
  have hi : 0 ≤ gaussianAbsoluteLowerConstant⁻¹ := by positivity
  have hd : 0 ≤ 32 / gaussianMaximumLowerConstant := by positivity
  linarith

private theorem integral_rowMixedNorm_top_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Matrix ι ι ℝ)
    {p : ℝ≥0∞} (hp : 2 ≤ p) :
    (∫ G, rowMixedNorm (symmetricGaussianMatrix A G) ⊤ ∂gaussianMatrix ι ι) ≤
      ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) p ∂gaussianMatrix ι ι :=
  integral_mono (integrable_rowMixedNorm_symmetricGaussianMatrix A (by simp))
    (integrable_rowMixedNorm_symmetricGaussianMatrix A hp)
    (fun G => rowMixedNorm_top_le _ (le_trans (by norm_num) hp))

private theorem finite_sorted_mean_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j)
    (hanti : Antitone (fun i => ‖A i‖)) {b p : ℝ} (hp : 2 ≤ p)
    (hb : 0 ≤ b) (hweight : ∀ i, ‖A i‖ * Real.sqrt (Real.log (i.val + 1)) ≤ b)
    (hblog : b ≤ (2 / gaussianMaximumLowerConstant) *
      ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) (ENNReal.ofReal p)
        ∂gaussianMatrix (Fin n) (Fin n)) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
      gaussianRowMeanComparisonConstant *
        ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) (ENNReal.ofReal p)
          ∂gaussianMatrix (Fin n) (Fin n) := by
  have hp0 : 0 < p := by linarith
  have hpE : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  let R := ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) (ENNReal.ofReal p)
    ∂gaussianMatrix (Fin n) (Fin n)
  have hR : 0 ≤ R := integral_nonneg fun G => rowMixedNorm_nonneg _ _
  let r := ⌈Real.exp p⌉₊
  let T := principalTailPart A r
  let m := principalTailEntryBound A r
  have hT : T.IsSymm := isSymm_principalTailPart A hA r
  have hT0 (i j : Fin n) : 0 ≤ T i j := by
    dsimp [T, principalTailPart]
    split_ifs
    · exact hA0 i j
    · exact le_rfl
  have hm : 0 ≤ m := principalTailEntryBound_nonneg A r
  have hcap (i j : Fin n) : T i j ^ 2 ≤ m ^ 2 :=
    principalTailPart_sq_le_entryBound_sq A hanti r i j
  have hsmall : Real.sqrt p * m ≤ b :=
    sqrt_mul_principalTailEntryBound_ceil_exp_le A hb hweight
  have htailMean : (∫ G, rowMixedNorm (symmetricGaussianMatrix T G) (ENNReal.ofReal p)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ R :=
    integral_rowMixedNorm_symmetricGaussianMatrix_principalTailPart_le A r hpE
  have htailRoot := integral_rowMixedNorm_symmetricGaussianMatrix_rpow_root_le_integral_add
    T hm hcap hpE hp
  have htailCaps := sqrt_mul_rowMax_profile_root_le_four_mul_integral_rowMixedNorm_rpow_root
    T hT hT0 hp
  have hcaps : Real.sqrt p * (∑ i, ‖T i‖ ^ p) ^ p⁻¹ ≤
      (4 + 32 / gaussianMaximumLowerConstant) * R := by
    change b ≤ (2 / gaussianMaximumLowerConstant) * R at hblog
    calc
      _ ≤ 4 * R + 16 * b := by nlinarith
      _ ≤ 4 * R + 16 * ((2 / gaussianMaximumLowerConstant) * R) := by
        nlinarith
      _ = _ := by ring
  have henergy := gaussianAbsoluteLowerConstant_mul_rowMixedNorm_le_integral A hA
    (p := ENNReal.ofReal p) (le_trans (by norm_num) hpE)
  have henergy' : (∑ i, (∑ j, A i j ^ 2) ^ (p / 2)) ^ p⁻¹ ≤
      gaussianAbsoluteLowerConstant⁻¹ * R := by
    have hformula := rowMixedNorm_ofReal_eq_sum_rowSq A hp0
    simp only [rowSq, Real.norm_eq_abs, sq_abs, one_div] at hformula
    rw [hformula] at henergy
    have hdiv : (∑ i, (∑ j, A i j ^ 2) ^ (p / 2)) ^ p⁻¹ ≤
        R / gaussianAbsoluteLowerConstant :=
      (le_div_iff₀ gaussianAbsoluteLowerConstant_pos).mpr (by
        simpa only [mul_comm] using henergy)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hop : (∫ G, specNorm (symmetricGaussianMatrix A G)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ gaussianRowOperatorComparisonConstant * R := by
    apply (integral_specNorm_symmetricGaussianMatrix_le_integral_rowMixedNorm_top A hA hA0).trans
    exact mul_le_mul_of_nonneg_left (integral_rowMixedNorm_top_le A hpE)
      gaussianRowOperatorComparisonConstant_pos.le
  have hhead : 2 * (2 * r : ℝ) ^ (1 / p) *
      (∫ G, specNorm (symmetricGaussianMatrix A G)
        ∂gaussianMatrix (Fin n) (Fin n)) ≤
      32 * gaussianRowOperatorComparisonConstant * R := by
    have hfactor := Real.two_mul_two_mul_ceil_exp_rpow_le hp
    have hnonneg : 0 ≤ ∫ G, specNorm (symmetricGaussianMatrix A G)
        ∂gaussianMatrix (Fin n) (Fin n) := integral_nonneg fun G => specNorm_nonneg _
    calc
      _ ≤ 32 * (∫ G, specNorm (symmetricGaussianMatrix A G)
          ∂gaussianMatrix (Fin n) (Fin n)) := mul_le_mul_of_nonneg_right hfactor hnonneg
      _ ≤ _ := by nlinarith
  have hmain := integral_schattenNormReal_symmetricGaussianMatrix_le_head_tail_moments A hA hA0 r hp
  change (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p
    ∂gaussianMatrix (Fin n) (Fin n)) ≤ gaussianRowMeanComparisonConstant * R
  dsimp only [gaussianRowMeanComparisonConstant]
  change (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p
    ∂gaussianMatrix (Fin n) (Fin n)) ≤ _ at hmain
  dsimp only [T] at hcaps
  nlinarith

/-- At every real exponent at least two, the actual expected Gaussian
Schatten norm is bounded by a universal constant times the actual expected
mixed Euclidean-row norm. No dimension factor or auxiliary estimate is assumed. -/
theorem integral_schattenNormReal_symmetricGaussianMatrix_le_integral_rowMixedNorm
    {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Matrix ι ι ℝ)
    (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j) {p : ℝ} (hp : 2 ≤ p) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p ∂gaussianMatrix ι ι) ≤
      gaussianRowMeanComparisonConstant *
        ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) (ENNReal.ofReal p)
          ∂gaussianMatrix ι ι := by
  classical
  have hp0 : 0 < p := by linarith
  have hpE : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := le_trans (by norm_num) hpE
  let e := sortingEquiv (fun i => ‖A i‖)
  let S := A.submatrix e e
  have hS : S.IsSymm := hA.submatrix e
  have hS0 (i j : Fin (Fintype.card ι)) : 0 ≤ S i j := hA0 (e i) (e j)
  have hrow (i : Fin (Fintype.card ι)) : ‖S i‖ = ‖A (e i)‖ :=
    e.surjective.pi_norm_comp (A (e i))
  have hanti : Antitone (fun i => ‖S i‖) := by
    simpa only [hrow, e, sortedVector, Function.comp_def] using
      sortedVector_antitone (fun i => ‖A i‖)
  have hweight (i : Fin (Fintype.card ι)) :
      ‖S i‖ * Real.sqrt (Real.log (i.val + 1)) ≤ profileLogRowMaximum A := by
    rw [hrow]
    have h := norm_le_pi_norm
      (fun l : Fin (Fintype.card ι) => ‖A (e l)‖ * Real.sqrt (Real.log (l.val + 1))) i
    simpa only [profileLogRowMaximum, e, Real.norm_of_nonneg (by positivity :
      0 ≤ ‖A (e i)‖ * Real.sqrt (Real.log (i.val + 1)))] using h
  have hmean := integral_rowMixedNorm_symmetricGaussianMatrix_submatrix e A hA hp1
  have hblog : profileLogRowMaximum A ≤ (2 / gaussianMaximumLowerConstant) *
      ∫ G, rowMixedNorm (symmetricGaussianMatrix S G) (ENNReal.ofReal p)
        ∂gaussianMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) := by
    rw [show (∫ G, rowMixedNorm (symmetricGaussianMatrix S G) (ENNReal.ofReal p)
      ∂gaussianMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι))) =
        ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) (ENNReal.ofReal p)
          ∂gaussianMatrix ι ι from hmean]
    exact (profileLogRowMaximum_le_integral_rowMixedNorm_top A hA hA0).trans
      (mul_le_mul_of_nonneg_left (integral_rowMixedNorm_top_le A hpE)
        (div_nonneg (by norm_num) gaussianMaximumLowerConstant_pos.le))
  have hbound := finite_sorted_mean_bound S hS hS0 hanti hp
    (profileLogRowMaximum_nonneg A) hweight hblog
  have hsch := integral_schattenNorm_symmetricGaussianMatrix_submatrix e A hA
    (p := ENNReal.ofReal p) hp1
  simp only [schattenNorm_ofReal _ hp0.le] at hsch
  rw [hsch, hmean] at hbound
  exact hbound

/-- The full native Gaussian Schatten-row mean comparison holds uniformly
for all exponents at least two, including infinity and empty dimensions. -/
theorem integral_schattenNorm_symmetricGaussianMatrix_le_integral_rowMixedNorm
    {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Matrix ι ι ℝ)
    (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    (∫ G, schattenNorm (symmetricGaussianMatrix A G) p ∂gaussianMatrix ι ι) ≤
      gaussianRowMeanComparisonConstant *
        ∫ G, rowMixedNorm (symmetricGaussianMatrix A G) p ∂gaussianMatrix ι ι := by
  by_cases hpt : p = ⊤
  · subst p
    simp only [schattenNorm_top]
    apply (integral_specNorm_symmetricGaussianMatrix_le_integral_rowMixedNorm_top A hA hA0).trans
    exact mul_le_mul_of_nonneg_right gaussianRowOperatorComparisonConstant_le_mean
      (integral_nonneg fun G => rowMixedNorm_nonneg _ _)
  · have hpr : (2 : ℝ) ≤ p.toReal := by
      simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hpt hp
    have h := integral_schattenNormReal_symmetricGaussianMatrix_le_integral_rowMixedNorm A hA hA0 hpr
    rw [ENNReal.ofReal_toReal hpt] at h
    simpa only [schattenNorm_eq_of_ne_top _ hpt] using h

end NLAlib
