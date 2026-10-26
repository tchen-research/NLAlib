import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite weighted Hölder inequalities

The finite generalized Hölder inequality is expressed using nonnegative real
weights and natural powers. The proof normalizes each moment and applies
weighted arithmetic-geometric means pointwise. The conjugate-real-exponent
version also remains available for trace inequalities. No independence is needed.
-/

noncomputable section

open scoped BigOperators

namespace Real

/-- Generalized finite Hölder: if each nonnegative function has `N`-th
moment at most `C i ^ N`, then a product with natural exponents summing to
`N` has integral at most the corresponding product of powers of `C`.
The weight may be any nonnegative finite measure and need not sum to one. -/
theorem sum_mul_prod_pow_le_prod_pow
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (ρ : Ω → ℝ) (hρ : ∀ ω, 0 ≤ ρ ω)
    (f : ι → Ω → ℝ) (hf : ∀ i ω, 0 ≤ f i ω)
    (e : ι → ℕ) (N : ℕ) (hN : 0 < N) (he : ∑ i, e i = N)
    (C : ι → ℝ) (hC : ∀ i, 0 < C i)
    (hmoment : ∀ i, (∑ ω, ρ ω * f i ω ^ N) ≤ C i ^ N) :
    (∑ ω, ρ ω * ∏ i, f i ω ^ e i) ≤ ∏ i, C i ^ e i := by
  classical
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let a : ι → ℝ := fun i => (e i : ℝ) / N
  let g : ι → Ω → ℝ := fun i ω => f i ω / C i
  have ha (i : ι) : 0 ≤ a i := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hasum : ∑ i, a i = 1 := by
    simp only [a, ← Finset.sum_div, ← Nat.cast_sum, he, div_self hNR.ne']
  have hg (i : ι) (ω : Ω) : 0 ≤ g i ω := div_nonneg (hf i ω) (hC i).le
  have hnorm (i : ι) : (∑ ω, ρ ω * g i ω ^ N) ≤ 1 := by
    have hcN : 0 < C i ^ N := pow_pos (hC i) N
    calc
      (∑ ω, ρ ω * g i ω ^ N) = (∑ ω, ρ ω * f i ω ^ N) / C i ^ N := by
        simp only [g, div_pow, mul_div_assoc, Finset.sum_div]
      _ ≤ 1 := (div_le_one hcN).mpr (hmoment i)
  have hpoint (ω : Ω) :
      (∏ i, g i ω ^ e i) ≤ ∑ i, a i * g i ω ^ N := by
    have hh := Real.geom_mean_le_arith_mean_weighted Finset.univ a
      (fun i => g i ω ^ N) (fun i _ => ha i) hasum
      (fun i _ => pow_nonneg (hg i ω) N)
    convert hh using 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast (g i ω) (e i), ← Real.rpow_natCast (g i ω) N,
      ← Real.rpow_mul (hg i ω)]
    congr 1
    dsimp [a]
    field_simp
  have hnormprod : (∑ ω, ρ ω * ∏ i, g i ω ^ e i) ≤ 1 := by
    calc
      (∑ ω, ρ ω * ∏ i, g i ω ^ e i) ≤
          ∑ ω, ρ ω * ∑ i, a i * g i ω ^ N :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω) (hρ ω)
      _ = ∑ i, a i * ∑ ω, ρ ω * g i ω ^ N := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hnorm i) (ha i)
      _ = 1 := hasum
  have hfactor (i : ι) (ω : Ω) : f i ω = C i * g i ω := by
    dsimp [g]
    exact (mul_div_cancel₀ _ (hC i).ne').symm
  calc
    (∑ ω, ρ ω * ∏ i, f i ω ^ e i) =
        (∏ i, C i ^ e i) * ∑ ω, ρ ω * ∏ i, g i ω ^ e i := by
      simp_rw [hfactor, mul_pow, Finset.prod_mul_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ (∏ i, C i ^ e i) * 1 := mul_le_mul_of_nonneg_left hnormprod
      (Finset.prod_nonneg fun i _ => pow_nonneg (hC i).le _)
    _ = _ := mul_one _

end Real

namespace NLAlib

/-- Finite weighted Hölder, with arbitrary nonnegative weights. -/
theorem sum_mul_mul_le_rpow_sum_mul_rpow {ι : Type*} (s : Finset ι)
    (w f g : ι → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, w i * f i * g i) ≤
      (∑ i ∈ s, w i * f i ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * g i ^ q) ^ (1 / q) := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hsum : 1 / p + 1 / q = 1 := by simpa only [one_div] using hpq.inv_add_inv_eq_one
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := fun i => w i ^ (1 / p) * f i)
    (g := fun i => w i ^ (1 / q) * g i)
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hf i hi))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hg i hi))
  have hleft (i : ι) (hi : i ∈ s) :
      (w i ^ (1 / p) * f i) * (w i ^ (1 / q) * g i) = w i * f i * g i := by
    calc
      _ = (w i ^ (1 / p) * w i ^ (1 / q)) * f i * g i := by ring
      _ = _ := by rw [← Real.rpow_add' (hw i hi) (by positivity), hsum, Real.rpow_one]
  have hpow (i : ι) (hi : i ∈ s) (r : ℝ) (hr : 0 < r) (a : ℝ) (ha : 0 ≤ a) :
      (w i ^ (1 / r) * a) ^ r = w i * a ^ r := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i hi) _) ha,
      ← Real.rpow_mul (hw i hi), one_div_mul_cancel hr.ne', Real.rpow_one]
  simpa only [Finset.sum_congr rfl hleft,
    Finset.sum_congr rfl (fun i hi => hpow i hi p hp (f i) (hf i hi)),
    Finset.sum_congr rfl (fun i hi => hpow i hi q hq (g i) (hg i hi))] using h

end NLAlib
