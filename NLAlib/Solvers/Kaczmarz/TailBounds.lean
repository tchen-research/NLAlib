/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Kaczmarz.TailAverage
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sharp tail-averaged Kaczmarz bounds

Both advertised estimates hold for the actual iid row-sampling law, with arbitrary
rank and inconsistent right-hand side. The initial iterate is in the row space, and
the reference solution is the actual minimum-norm least-squares solution `A⁺b`.
Source: Epperly–Goldshlager–Webber, arXiv:2411.19877v3, Theorems 2–3.
Atlas: `tail-averaged-kaczmarz`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology
namespace NLAlib.Kaczmarz
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
private theorem moorePenroseInverse_mulVec_mem_range_transpose
    (A : Matrix m n ℝ) (b : m → ℝ) :
    moorePenroseInverse A *ᵥ b ∈ LinearMap.range Aᵀ.mulVecLin := by
  refine ⟨(moorePenroseInverse A)ᵀ *ᵥ (moorePenroseInverse A *ᵥ b), ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have hs : (moorePenroseInverse A * A)ᵀ = moorePenroseInverse A * A :=
    (moorePenroseInverse_mul_isHermitian A).eq
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hs, moorePenroseInverse_mul_moorePenroseInverse]

open scoped Matrix.Norms.L2Operator in
/-- **Both sharp tail-averaging bounds.** With `N` averaged iterates following `burn` updates,
the transient and noise terms have the exact factors `q^burn`, `2κ_F²-1`, and `1/N`.
The product measure is the actual independent burn-in and continuation row law, not a law
of independent iterates. The conclusion includes rank-deficient and inconsistent systems.
atlas: tail-averaged-kaczmarz (partial) -/
theorem integral_norm_tailAverage_sub_moorePenroseInverse_mulVec_sq_le
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ)
    (x : n → ℝ) (hx : x ∈ LinearMap.range Aᵀ.mulVecLin)
    (burn N : ℕ) (hN : 0 < N) :
    let xs := moorePenroseInverse A *ᵥ b
    let κ := frobConditionNumber A
    let q := 1 - 1 / κ ^ 2
    let V := specNorm (moorePenroseInverse A) ^ 2 *
      ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2
    let E := ‖WithLp.toLp 2 (x - xs)‖ ^ 2
    let M := ∫ ω, ‖WithLp.toLp 2 (tailAverage A b x burn N ω - xs)‖ ^ 2
      ∂((kaczmarzRowPathPMF A hA burn).toMeasure.prod
        (kaczmarzRowPathPMF A hA N).toMeasure)
    M ≤ q ^ burn * E + (2 * κ ^ 2 - 1) * V / N ∧
      M ≤ (2 * κ ^ 2 - 1) / N * (κ ^ 2 * q ^ burn / N * E + V) := by
  dsimp only
  simp only [norm_toLp_sq_eq_dotProduct_self]
  let xs := moorePenroseInverse A *ᵥ b
  let κ := frobConditionNumber A
  let q := 1 - 1 / κ ^ 2
  let V := specNorm (moorePenroseInverse A) ^ 2 * ((b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs))
  let E := (x - xs) ⬝ᵥ (x - xs)
  let C := 2 * κ ^ 2 - 1
  have hM : 0 < specNorm (moorePenroseInverse A) := by
    rw [specNorm_eq_norm]
    exact norm_pos_iff.mpr ((moorePenroseInverse_eq_zero_iff A).not.mpr hA)
  have hF : 0 < frobSq A := lt_of_le_of_ne (frobSq_nonneg A)
    (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hκ : 0 < κ ^ 2 := by
    dsimp [κ, frobConditionNumber]
    rw [mul_pow, frobNorm_sq]
    exact mul_pos hF (sq_pos_of_pos hM)
  have hκne : κ ≠ 0 := fun h => by simp [h] at hκ
  have hr : 1 - (specNorm (moorePenroseInverse A))⁻¹ ^ 2 / frobSq A = q := by
    dsimp [q, κ, frobConditionNumber]
    rw [mul_pow, frobNorm_sq]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]
  have hs := fun v (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) =>
    inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le A hv
  have hq0 : 0 ≤ q := hr ▸ rate_nonneg_of_lower_bound_on_range A _ hs
  have hq1 : q < 1 := by dsimp [q]; linarith [one_div_pos.mpr hκ]
  have hC : (1 + q) / (1 - q) = C := by
    dsimp [q, C]
    field_simp [hκne]
    ring
  have hV : ((b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs)) /
      (specNorm (moorePenroseInverse A))⁻¹ ^ 2 = V := by
    dsimp [V]
    rw [inv_pow, div_inv_eq_mul, mul_comm]
  have he : x - xs ∈ LinearMap.range Aᵀ.mulVecLin :=
    Submodule.sub_mem _ hx (moorePenroseInverse_mulVec_mem_range_transpose A b)
  have hsNorm : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      (specNorm (moorePenroseInverse A))⁻¹ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤
        ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2 := by
    simpa only [norm_toLp_sq_eq_dotProduct_self] using hs
  have hb := integral_norm_tailAverage_sub_sq_le A hA b xs
    (isLeastSquaresSolution_moorePenroseInverse_mulVec A b) (inv_pos.mpr hM) hsNorm
    x he burn N hN
  dsimp only at hb
  simp only [norm_toLp_sq_eq_dotProduct_self] at hb
  rw [hr, hC, hV] at hb
  have hE : 0 ≤ E := dotProduct_self_nonneg _
  have hqE : 0 ≤ q ^ burn * E := mul_nonneg (pow_nonneg hq0 burn) hE
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hw1 : tailInitialWeight q N / (N : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hNpos)]
    exact tailInitialWeight_le_sq hq0 hq1.le N
  have hw2 : tailInitialWeight q N ≤ C * κ ^ 2 := by
    have hw := tailInitialWeight_le_div hq0 hq1 N
    rw [hC] at hw
    have hd : C / (1 - q) = C * κ ^ 2 := by
      have hden : 1 - q = 1 / κ ^ 2 := by dsimp [q]; ring
      simp only [hden, one_div, div_inv_eq_mul]
    rwa [hd] at hw
  constructor
  · refine hb.trans ?_
    change (tailInitialWeight q N / (N : ℝ) ^ 2) * q ^ burn * E + C * V / N ≤
      q ^ burn * E + C * V / N
    have ht := mul_le_mul_of_nonneg_right hw1 hqE
    nlinarith only [ht]
  · refine hb.trans ?_
    have ht := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hw2 (sq_nonneg (N : ℝ))) hqE
    calc
      _ ≤ (C * κ ^ 2 / (N : ℝ) ^ 2) * (q ^ burn * E) + C * V / N := by
        nlinarith only [ht]
      _ = C / N * (κ ^ 2 * q ^ burn / N * E + V) := by
        field_simp

/-- **Mean-square convergence of tail-averaged Kaczmarz.** For any fixed burn-in, increasing
the number of averaged iterates gives the minimum-norm least-squares solution in mean square,
under the actual iid row law and without a full-rank assumption.
atlas: tail-averaged-kaczmarz (partial) -/
theorem tendsto_integral_norm_tailAverage_sub_moorePenroseInverse_mulVec_sq
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ)
    (x : n → ℝ) (hx : x ∈ LinearMap.range Aᵀ.mulVecLin) (burn : ℕ) :
    Tendsto (fun N : ℕ =>
      ∫ ω, ‖WithLp.toLp 2 (tailAverage A b x burn N ω - moorePenroseInverse A *ᵥ b)‖ ^ 2
        ∂((kaczmarzRowPathPMF A hA burn).toMeasure.prod
          (kaczmarzRowPathPMF A hA N).toMeasure)) atTop (𝓝 0) := by
  let xs := moorePenroseInverse A *ᵥ b
  let K := frobConditionNumber A ^ 2
  let q := 1 - 1 / K
  let V := specNorm (moorePenroseInverse A) ^ 2 *
    ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2
  let E := ‖WithLp.toLp 2 (x - xs)‖ ^ 2
  let C := 2 * K - 1
  have hden : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ho : Tendsto (fun N : ℕ => C / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hi : Tendsto (fun N : ℕ => K * q ^ burn / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlimit : Tendsto (fun N : ℕ => C / N * (K * q ^ burn / N * E + V))
      atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using ho.mul ((hi.mul_const E).add_const V)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N =>
    integral_nonneg fun ω => sq_nonneg _)) _ hlimit
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun N hN => ?_⟩
  exact (integral_norm_tailAverage_sub_moorePenroseInverse_mulVec_sq_le
    A hA b x hx burn N hN).2

end NLAlib.Kaczmarz
