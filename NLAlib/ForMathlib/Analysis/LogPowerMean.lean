import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

/-!
# Power ratios from logarithmic overlap

Finite concave-power Jensen bounds a power-method Rayleigh ratio by the
logarithm of its leading-coordinate overlap. Source: manuscript `rt:power`.
-/

noncomputable section
namespace NLAlib

/-- A nonnegative spectral power ratio with one eigenvalue equal to one has error
at most the logarithmic inverse leading overlap divided by `2q+1`.
Source: manuscript `rt:power`; finite scalar power-mean Jensen. The statement
includes `q=0` and needs no gap or upper bound on the other spectral values. -/
theorem one_sub_sum_pow_div_sum_pow_le_log_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d g : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (i₀ : ι) (h₀ : d i₀ = 1) (hg : g i₀ ≠ 0) (q : ℕ) :
    1 - (∑ i, g i ^ 2 * d i ^ (2 * q + 1)) / (∑ i, g i ^ 2 * d i ^ (2 * q)) ≤
      Real.log ((∑ i, g i ^ 2) / (g i₀ ^ 2)) / ((2 * q + 1 : ℕ) : ℝ) := by
  let G := ∑ i, g i ^ 2
  let M := fun s : ℕ => ∑ i, g i ^ 2 * d i ^ s
  let r := 2 * q + 1
  have hg2 : 0 < g i₀ ^ 2 := sq_pos_of_ne_zero hg
  have hG : 0 < G := hg2.trans_le
    (Finset.single_le_sum (fun i _ => sq_nonneg (g i)) (Finset.mem_univ i₀))
  have hMlow : ∀ s, g i₀ ^ 2 ≤ M s := by
    intro s
    have h := Finset.single_le_sum (f := fun i => g i ^ 2 * d i ^ s)
      (fun i _ => mul_nonneg (sq_nonneg _) (pow_nonneg (hd i) s)) (Finset.mem_univ i₀)
    simpa only [h₀, one_pow, mul_one] using h
  have hMp : ∀ s, 0 < M s := fun s => hg2.trans_le (hMlow s)
  have hr : (0 : ℝ) < r := by
    exact_mod_cast (by dsimp [r]; omega : 0 < r)
  let α := ((2 * q : ℕ) : ℝ) / r
  let β := ((r : ℕ) : ℝ)⁻¹
  let w := fun i => g i ^ 2 / G
  have hα0 : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hr.le
  have hα1 : α ≤ 1 := by
    apply (div_le_one hr).mpr
    exact_mod_cast (by dsimp [r]; omega : 2 * q ≤ r)
  have hαβ : α + β = 1 := by
    dsimp only [α, β, r]
    push_cast
    field_simp
  have hw : ∑ i, w i = 1 := by
    dsimp only [w]
    rw [← Finset.sum_div, div_self hG.ne']
  have hpow : ∀ i, (d i ^ r) ^ α = d i ^ (2 * q) := by
    intro i
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hd i)]
    have he : (r : ℝ) * α = ((2 * q : ℕ) : ℝ) := by
      dsimp only [α]
      rw [mul_comm, div_mul_cancel₀ _ hr.ne']
    rw [he, Real.rpow_natCast]
  have hJ := (Real.concaveOn_rpow hα0 hα1).le_map_sum (t := Finset.univ)
    (w := w) (p := fun i => d i ^ r)
    (fun i _ => div_nonneg (sq_nonneg _) hG.le) hw
    (fun i _ => pow_nonneg (hd i) r)
  simp only [smul_eq_mul, hpow, w, div_mul_eq_mul_div, ← Finset.sum_div] at hJ
  let a := M r / G
  let b := M (2 * q) / G
  have ha : 0 < a := div_pos (hMp r) hG
  have hb : 0 < b := div_pos (hMp (2 * q)) hG
  have hJ' : b ≤ a ^ α := hJ
  have hlow : a ^ β ≤ a / b := by
    apply (le_div_iff₀ hb).mpr
    calc a ^ β * b ≤ a ^ β * a ^ α :=
        mul_le_mul_of_nonneg_left hJ' (Real.rpow_nonneg ha.le _)
      _ = a := by
        rw [← Real.rpow_add ha, show β + α = 1 by linarith, Real.rpow_one]
  have hlead : g i₀ ^ 2 / G ≤ a := div_le_div_of_nonneg_right (hMlow r) hG.le
  have hroot : (g i₀ ^ 2 / G) ^ β ≤ a ^ β :=
    Real.rpow_le_rpow (div_nonneg hg2.le hG.le) hlead (inv_nonneg.mpr hr.le)
  have hrootEq : (g i₀ ^ 2 / G) ^ β = Real.exp (-Real.log (G / g i₀ ^ 2) / r) := by
    rw [Real.rpow_def_of_pos (div_pos hg2 hG), Real.log_div hg2.ne' hG.ne',
      Real.log_div hG.ne' hg2.ne']
    congr 1
    dsimp only [β]
    ring
  have hratio : a / b = M r / M (2 * q) := by
    dsimp only [a, b]
    field_simp
  rw [hrootEq] at hroot
  have hExp : Real.exp (-Real.log (G / g i₀ ^ 2) / r) ≤ M r / M (2 * q) := by
    rw [← hratio]
    exact hroot.trans hlow
  have hscalar := Real.add_one_le_exp (-Real.log (G / g i₀ ^ 2) / r)
  rw [neg_div] at hExp hscalar
  change 1 - M r / M (2 * q) ≤ Real.log (G / g i₀ ^ 2) / r
  linarith

end NLAlib
