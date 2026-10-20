import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeGridScale
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeSpectralProbability

/-! # Actual Gaussian/free spectral comparison at a fixed admissible height -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]

open scoped Matrix.Norms.L2Operator in
/-- The actual two-sided spectral distance has a fixed-confidence bound
whenever a positive radius dominates the literal weak, variance and cubic
moment budgets. All numerical resolvent and mesh inequalities are discharged.
Source: arXiv:2406.11453v2, Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_hausdorffDist_gaussian_wordNative_gt_fixed_height
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hmass : 0 < bilinearSquareMass A Finset.univ)
    {q : ℕ} (hq : 0 < q) (hlog : Real.log (Fintype.card d : ℝ) ≤ q)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hweak : Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q ≤ Δ)
    (hvariance : Real.sqrt (specNorm (coefficientVariance A))/(Fintype.card d : ℝ)^2 ≤ Δ)
    (hbudget : (q : ℝ)^3*(specNorm (coefficientVariance A)*specNorm (coefficientCovariance A)) ≤ Δ^4) :
    (gaussianVector ι).real {x : ι → ℝ | (20000000000000000 : ℝ)*Δ < Metric.hausdorffDist
      (spectrum ℝ (A₀+∑ i,x i•A i)) (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A))} ≤
      1/(16*(q : ℝ)) + 27*(Fintype.card d : ℝ)^2*Real.exp (-(q : ℝ)) := by
  classical
  let η : ℝ := 10000000000*Δ
  have hη : 0 < η := by dsimp only [η]; positivity
  let B : ℝ := (((2*(2*q)+1)*(2*(2*q)+2)^2 : ℕ) : ℝ)*
    (specNorm (coefficientVariance A)*specNorm (coefficientCovariance A))*η⁻¹^5
  let δ : ℝ := 1000000*(B+6*Δ/η^2)
  let s := Real.sqrt (bilinearSquareMass A Finset.univ)
  let c : ℝ := bilinearSquareMass A Finset.univ*η⁻¹^4
  let t : ℝ := 2*Real.sqrt (c*q)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hV : 0 ≤ specNorm (coefficientVariance A) := specNorm_nonneg _
  have hW : 0 ≤ specNorm (coefficientCovariance A) := specNorm_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hqroot : 1 ≤ Real.sqrt (q : ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by simpa using hq1)
  have hscale : Real.sqrt (specNorm (coefficientVariance A)) ≤
      2*(Fintype.card d : ℝ)*(s*Real.sqrt q) := by
    have hσ := sqrt_variance_le_card_mul_sqrt_bilinearSquareMass A hA
    have hh := mul_le_mul_of_nonneg_left hqroot
      (mul_nonneg (Nat.cast_nonneg (Fintype.card d)) hs)
    dsimp only [s] at *
    nlinarith only [hσ,hh,mul_nonneg (Nat.cast_nonneg (Fintype.card d)) hs]
  have hfwd := gaussian_free_forward_error_le (d := Fintype.card d) hq hlog hB hΔ.le (η := η)
  have hrev := gaussian_free_reverse_error_le (d := Fintype.card d) hq hs
    (Real.sqrt_nonneg (specNorm (coefficientVariance A))) hB hη hweak hvariance
  dsimp only at hrev
  rw [Real.sq_sqrt (bilinearSquareMass_nonneg _ _)] at hrev
  have hgrid := gaussian_free_grid_error_budget_le hq hV hW hΔ hweak hbudget
  dsimp only at hgrid
  have hp := measureReal_hausdorffDist_gaussian_wordNative_gt_le_grid_error A₀ hA₀ A hA
    hmass hq hlog hη ht hscale
    (gaussian_free_markov_factor_le hq hlog) gaussian_free_ultracontractive_factor_le
    hfwd hrev (by simpa only [B, η, mul_assoc] using hgrid)
  have he : 2*(1000000 : ℝ)*η = 20000000000000000*Δ := by dsimp only [η]; ring
  rw [he] at hp
  have htail := gaussian_free_fluctuation_tail_eq hq (Real.sqrt_pos.mpr hmass) hη
  dsimp only at htail
  rw [Real.sq_sqrt (bilinearSquareMass_nonneg _ _)] at htail
  have htail' : Real.exp (-t^2/(2*c))=Real.exp (-2*(q : ℝ)) := by
    dsimp only [t,c]
    linarith only [htail]
  change _ ≤ _ at hp
  change _ ≤ _
  have h4 := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) q] :
    (-4*(q : ℝ)) ≤ -(q : ℝ))
  have h2 := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) q] :
    (-2*(q : ℝ)) ≤ -(q : ℝ))
  have h4m := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 9*(Fintype.card d : ℝ)^2)
  have h2m := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 18*(Fintype.card d : ℝ)^2)
  change _ ≤ 1/(16*(q : ℝ)) + (9*(Fintype.card d)^2 : ℕ)*Real.exp (-4*q : ℝ) +
    (18*(Fintype.card d)^2 : ℕ)*Real.exp (-t^2/(2*c)) at hp
  rw [htail'] at hp
  push_cast at hp
  linarith only [hp,h4m,h2m]

end NLAlib
