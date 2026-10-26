import NLAlib.Matrix.Functions.SymmetricProfilePowerFactors
import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Hadamard

/-!
# Entire symmetric coefficient families with profile endpoint bounds

The explicit symmetric power factors are lifted to an entire complex
matrix family. Its center is the original complex symmetric profile,
its left Frobenius power sum is at most four, and its right row and
weighted entry power sums are at most one. A uniform spectral bound on
the full closed strip is supplied as part of the construction.

Source: the coefficient-side interpolation in Latała--van Handel--Youssef,
arXiv:1711.00807v2, §2.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- A normalized complex symmetric profile has an actual entire symmetric
interpolation family with exact center and controlled endpoint profile
power sums. The left squared norm bound is four, and both right profile
bounds are one. Boundedness on the whole closed strip is constructed,
including vanishing coefficients and empty matrix spaces. -/
theorem exists_entire_symmetric_profile_family
    {n : Type*} [Fintype n] [DecidableEq n]
    {p q θ c : ℝ} (hp : 2 ≤ p) (hq : 0 < q) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hc : 0 < c) (hexp : 1 / p = (1 - θ) / 2 + θ / q)
    (b : Matrix n n ℂ) (hb : b.IsSymm)
    (hrow : (∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2)) ≤ 1)
    (hentry : c ^ (θ * p) * (∑ i, ∑ j, ‖b i j‖ ^ p) ≤ 1) :
    ∃ (F : ℂ → Matrix n n ℂ) (B : ℝ),
      Differentiable ℂ F ∧ (∀ z, (F z).IsSymm) ∧ F (θ : ℂ) = b ∧ 0 ≤ B ∧
      (∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (F z) ≤ B) ∧
      (∀ t : ℝ, (∑ i, ∑ j, ‖F ((t : ℂ) * Complex.I) i j‖ ^ 2) ≤ 4) ∧
      (∀ t : ℝ, (∑ i, (∑ j, ‖F (1 + (t : ℂ) * Complex.I) i j‖ ^ 2) ^ (q / 2)) ≤ 1) ∧
      (∀ t : ℝ, c ^ q * (∑ i, ∑ j, ‖F (1 + (t : ℂ) * Complex.I) i j‖ ^ q) ≤ 1) := by
  classical
  let a : Matrix n n ℝ := fun i j => ‖b i j‖
  have ha : a.IsSymm := by
    ext i j
    change ‖b j i‖ = ‖b i j‖
    rw [hb.apply i j]
  obtain ⟨U, V, hU, hV, hUsym, hVsym, hfactor, hleft, hright, hrightEntry⟩ :=
    exists_symmetric_profile_power_factors hp hq hθ hc hexp a ha (fun i j => norm_nonneg _) hrow hentry
  let phase : Matrix n n ℂ := fun i j => if b i j = 0 then 0 else b i j / (‖b i j‖ : ℂ)
  have hphase (i j : n) : ‖phase i j‖ ≤ 1 := by
    by_cases hz : b i j = 0
    · simp [phase, hz]
    · simp [phase, hz]
  let F : ℂ → Matrix n n ℂ := fun z i j =>
    phase i j * powerInterpolationCoefficient (U i j) (V i j) z
  let L : (n × n → ℂ) →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun x i j => x (i, j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hF : Differentiable ℂ F := by
    have hh : Differentiable ℂ (fun z => fun ij : n × n =>
        phase ij.1 ij.2 * powerInterpolationCoefficient (U ij.1 ij.2) (V ij.1 ij.2) z) := by
      apply differentiable_pi.mpr
      intro ij
      exact differentiable_const _ |>.mul (differentiable_powerInterpolationCoefficient _ _)
    exact L.toContinuousLinearMap.differentiable.comp hh
  have hentrybound (i j : n) (z : ℂ) (C : ℝ)
      (hh : ‖powerInterpolationCoefficient (U i j) (V i j) z‖ ≤ C) :
      ‖F z i j‖ ≤ C := by
    dsimp [F]
    rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right (hphase i j) (norm_nonneg _)).trans_eq (one_mul _)).trans hh
  have hFleft (i j : n) (t : ℝ) : ‖F ((t : ℂ) * Complex.I) i j‖ ≤ U i j :=
    hentrybound i j _ _ (norm_powerInterpolationCoefficient_boundaries (hU i j) (hV i j) t).1
  have hFright (i j : n) (t : ℝ) : ‖F (1 + (t : ℂ) * Complex.I) i j‖ ≤ V i j :=
    hentrybound i j _ _ (norm_powerInterpolationCoefficient_boundaries (hU i j) (hV i j) t).2
  let B : ℝ := Real.sqrt (∑ i, ∑ j, max (U i j) (V i j) ^ 2)
  refine ⟨F, B, hF, ?_, ?_, Real.sqrt_nonneg _, ?_, ?_, ?_, ?_⟩
  · intro z
    ext i j
    change phase j i * powerInterpolationCoefficient (U j i) (V j i) z =
      phase i j * powerInterpolationCoefficient (U i j) (V i j) z
    rw [hUsym.apply i j, hVsym.apply i j]
    simp only [phase, hb.apply i j]
  · ext i j
    change phase i j * powerInterpolationCoefficient (U i j) (V i j) (θ : ℂ) = b i j
    rw [powerInterpolationCoefficient_real (hU i j) (hV i j) hθ, ← hfactor i j]
    by_cases hz : b i j = 0
    · simp [phase, a, hz]
    · dsimp [phase, a]
      rw [if_neg hz]
      exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
  · intro z hz
    apply (specNorm_le_frobNorm (F z)).trans
    change Real.sqrt (frobSq (F z)) ≤ _
    rw [frobSq_eq_sum_norm_sq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hentrybound i j z _ (norm_powerInterpolationCoefficient_le_max (hU i j) (hV i j) hz)) 2
  · intro t
    apply le_trans _ hleft
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hFleft i j t) 2
  · intro t
    apply le_trans _ hright
    apply Finset.sum_le_sum
    intro i _
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => sq_nonneg _) _ (by positivity)
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hFright i j t) 2
  · intro t
    apply le_trans _ hrightEntry
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc.le _)
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      Real.rpow_le_rpow (norm_nonneg _) (hFright i j t) hq.le

end NLAlib
