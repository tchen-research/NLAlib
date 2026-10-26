import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricRowEnergyLower
import NLAlib.Probability.Gaussian.Moments.MaximumLower
import NLAlib.ForMathlib.Combinatorics.CanonicalPairSelection

/-!
# Independent selected Gaussian entries and the maximum row norm

Distinct canonical lower-triangular coordinates are genuinely independent
standard Gaussian samples. Their square-root logarithmic maximum is
therefore a lower bound for the maximum Euclidean row length whenever
their deterministic coefficients have a common lower bound.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A finite set of distinct canonical Gaussian entries with coefficients
at least `m` forces the actual maximum row norm to have its logarithmic
Gaussian lower scale. -/
theorem gaussianMaximumLowerConstant_mul_selected_sqrt_log_le_integral_rowMixedNorm
    (b : Matrix ι ι ℝ) (S : Finset (ι × ι)) (m : ℝ) (hm : 0 ≤ m)
    (hS : ∀ e ∈ S, e.2 ≤ e.1 ∧ m ≤ |b e.1 e.2|) :
    gaussianMaximumLowerConstant * m * Real.sqrt (Real.log ((S.card : ℝ) + 1)) ≤
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι := by
  classical
  let e := (Fintype.equivFin S).symm
  let ρ : Fin (Fintype.card S) → ι × ι := fun k => (e k).1
  let V : Matrix ι ι ℝ → Fin (Fintype.card S) → ℝ := fun G k => G (ρ k).1 (ρ k).2
  have hρ : Function.Injective ρ := Subtype.val_injective.comp e.injective
  have hV : HasLaw V (gaussianVector (Fin (Fintype.card S))) (gaussianMatrix ι ι) := by
    apply hasLaw_gaussianVector_of_iIndepFun
    · intro k
      exact (measurePreserving_gaussianMatrix_entry (ρ k).1 (ρ k).2).hasLaw
    · exact iIndepFun.precomp hρ iIndepFun_gaussianMatrix_entry
  have hVi : MemLp V 2 (gaussianMatrix ι ι) := by
    apply memLp_pi_iff.mpr
    intro k
    exact memLp_gaussianMatrix_entry (ρ k).1 (ρ k).2 2 (by simp)
  have hRi : Integrable (fun G => rowMixedNorm (symmetricGaussianMatrix b G) ⊤)
      (gaussianMatrix ι ι) := by
    simpa only [rowMixedNorm_top_eq_pi_norm] using integrable_pi_norm_sqrt_rowSq_symmetricGaussianMatrix b
  have hpoint (G : Matrix ι ι ℝ) : m * ‖V G‖ ≤ rowMixedNorm (symmetricGaussianMatrix b G) ⊤ := by
    have hnorm : ‖fun k => m * V G k‖ ≤ rowMixedNorm (symmetricGaussianMatrix b G) ⊤ := by
      apply (pi_norm_le_iff_of_nonneg (rowMixedNorm_nonneg _ _)).mpr
      intro k
      obtain ⟨hcan, hcap⟩ := hS (ρ k) (e k).2
      have hx : symmetricGaussianMatrix b G (ρ k).1 (ρ k).2 =
          b (ρ k).1 (ρ k).2 * G (ρ k).1 (ρ k).2 := by
        simp only [symmetricGaussianMatrix, Matrix.of_apply, max_eq_left hcan, min_eq_right hcan]
      have hentry : |symmetricGaussianMatrix b G (ρ k).1 (ρ k).2| ≤
          Real.sqrt (rowSq (symmetricGaussianMatrix b G) (ρ k).1) := by
        have h := Real.sqrt_le_sqrt (Finset.single_le_sum
          (f := fun j => ‖symmetricGaussianMatrix b G (ρ k).1 j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ (ρ k).2))
        simpa only [rowSq, Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs] using h
      have hrow : Real.sqrt (rowSq (symmetricGaussianMatrix b G) (ρ k).1) ≤
          rowMixedNorm (symmetricGaussianMatrix b G) ⊤ := by
        rw [rowMixedNorm_top_eq_pi_norm]
        simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
          norm_le_pi_norm (fun i => Real.sqrt (rowSq (symmetricGaussianMatrix b G) i)) (ρ k).1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
      have hmul := mul_le_mul_of_nonneg_right hcap (abs_nonneg (V G k))
      have hcap' : |b (ρ k).1 (ρ k).2| * |V G k| =
          |symmetricGaussianMatrix b G (ρ k).1 (ρ k).2| := by rw [hx, abs_mul]
      rw [hcap'] at hmul
      exact hmul.trans (hentry.trans hrow)
    have hscale : ‖fun k => m * V G k‖ = m * ‖V G‖ := by
      have heq : (fun k => m * V G k) = m • V G := by funext k; rfl
      rw [heq, norm_smul, Real.norm_of_nonneg hm]
    rwa [hscale] at hnorm
  have hmean := integral_mono ((hVi.norm.integrable (by norm_num)).const_mul m) hRi hpoint
  rw [integral_const_mul] at hmean
  have hlaw := hV.integral_comp (show AEStronglyMeasurable
    (fun g : Fin (Fintype.card S) → ℝ => ‖g‖) (gaussianVector (Fin (Fintype.card S))) from by fun_prop)
  change (∫ G, ‖V G‖ ∂gaussianMatrix ι ι) = _ at hlaw
  rw [hlaw] at hmean
  have hlow := gaussianMaximumLowerConstant_mul_sqrt_log_le_integral_norm_gaussianVector (Fintype.card S)
  simp only [Fintype.card_coe] at hlow hmean
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hlow)]

omit [LinearOrder ι] in
private theorem exists_entry_eq_pi_norm_row (b : Matrix ι ι ℝ)
    (hb0 : ∀ i j, 0 ≤ b i j) (i : ι) : ∃ j, b i j = ‖b i‖ := by
  classical
  let : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j => |b i j|)
  have hnorm : ‖b i‖ ≤ |b i j| := by
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro k
    rw [Real.norm_eq_abs, hj]
    exact le_ciSup (Set.finite_range (fun l : ι => |b i l|)).bddAbove k
  have hrev : |b i j| ≤ ‖b i‖ := norm_le_pi_norm (b i) j
  exact ⟨j, by rw [abs_of_nonneg (hb0 i j)] at hnorm hrev; linarith⟩

/-- Each prefix of the decreasing row maxima has the expected independent
Gaussian lower scale in the actual maximum row norm. Symmetric duplicates
cost only the factor two proved by canonical-coordinate counting. -/
theorem gaussianMaximumLowerConstant_mul_sorted_row_sqrt_log_le_integral
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    (k : Fin (Fintype.card ι)) :
    gaussianMaximumLowerConstant *
        (‖b (sortingEquiv (fun i => ‖b i‖) k)‖ * Real.sqrt (Real.log (k.val + 1))) ≤
      2 * ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι := by
  classical
  choose j hj using exists_entry_eq_pi_norm_row b hb0
  let e := sortingEquiv (fun i => ‖b i‖)
  let rows := (Finset.Iic k).image e
  let S := rows.image (fun i => (max i (j i), min i (j i)))
  let m := ‖b (e k)‖
  have hrows : rows.card = k.val + 1 := by
    rw [Finset.card_image_of_injective _ e.injective, Fin.card_Iic]
  have hcard : k.val + 1 ≤ 2 * S.card := by
    rw [← hrows]
    exact Finset.card_le_two_mul_card_image_canonicalPair rows j
  have hS : ∀ q ∈ S, q.2 ≤ q.1 ∧ m ≤ |b q.1 q.2| := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨min_le_max, ?_⟩
    have hmin : m ≤ b i (j i) := by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      rw [hj]
      exact sortedVector_antitone (fun i => ‖b i‖) (Finset.mem_Iic.mp hl)
    have hcoef : b (max i (j i)) (min i (j i)) = b i (j i) := by
      by_cases hij : j i ≤ i
      · rw [max_eq_left hij, min_eq_right hij]
      · have hij' : i ≤ j i := le_of_not_ge hij
        rw [max_eq_right hij', min_eq_left hij', hb.apply i (j i)]
    rw [hcoef, abs_of_nonneg (hb0 i (j i))]
    exact hmin
  have hlower := gaussianMaximumLowerConstant_mul_selected_sqrt_log_le_integral_rowMixedNorm
    b S m (norm_nonneg _) hS
  have hcardR : (k.val : ℝ) + 1 ≤ 2 * (S.card : ℝ) := by exact_mod_cast hcard
  have hlog : Real.log (k.val + 1 : ℝ) ≤ 2 * Real.log ((S.card : ℝ) + 1) := by
    have harg : (k.val : ℝ) + 1 ≤ ((S.card : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (S.card : ℝ)]
    have h := Real.log_le_log (by positivity : 0 < (k.val : ℝ) + 1) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hroot : Real.sqrt (Real.log (k.val + 1 : ℝ)) ≤
      2 * Real.sqrt (Real.log ((S.card : ℝ) + 1)) := by
    have hk0 : 0 ≤ Real.log (k.val + 1 : ℝ) := Real.log_nonneg (by
      have hk : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _; linarith)
    have hs0 : 0 ≤ Real.log ((S.card : ℝ) + 1) := Real.log_nonneg (by
      have hs : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _; linarith)
    nlinarith [Real.sq_sqrt hk0, Real.sq_sqrt hs0,
      Real.sqrt_nonneg (Real.log (k.val + 1 : ℝ)), Real.sqrt_nonneg (Real.log ((S.card : ℝ) + 1))]
  have hc0 : 0 ≤ gaussianMaximumLowerConstant * m :=
    mul_nonneg gaussianMaximumLowerConstant_pos.le (norm_nonneg _)
  change gaussianMaximumLowerConstant * (m * Real.sqrt (Real.log (k.val + 1))) ≤ _
  nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hroot)]

/-- The sorted logarithmic row-maximum envelope is uniformly dominated
by the expected actual maximum Euclidean row norm. -/
theorem gaussianMaximumLowerConstant_mul_profileLogRowMaximum_le_integral
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j) :
    gaussianMaximumLowerConstant * profileLogRowMaximum b ≤
      2 * ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι := by
  have hE : 0 ≤ ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι :=
    integral_nonneg fun G => rowMixedNorm_nonneg _ _
  have hnorm : profileLogRowMaximum b ≤
      (2 * ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) ⊤ ∂gaussianMatrix ι ι) /
        gaussianMaximumLowerConstant := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (by linarith) gaussianMaximumLowerConstant_pos.le)).mpr
    intro k
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
    have h := gaussianMaximumLowerConstant_mul_sorted_row_sqrt_log_le_integral b hb hb0 k
    apply (le_div_iff₀ gaussianMaximumLowerConstant_pos).mpr
    nlinarith
  have h := (le_div_iff₀ gaussianMaximumLowerConstant_pos).mp hnorm
  nlinarith

end NLAlib
