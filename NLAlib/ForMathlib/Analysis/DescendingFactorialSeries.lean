import NLAlib.ForMathlib.Analysis.FiniteProductBounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Descending-factorial series

Finite telescoping bounds give absolute summability of bounded-variation
Chebyshev coefficient envelopes.
-/
noncomputable section
open Finset
namespace NLAlib

/-- An inverse descending factorial is the difference of two adjacent inverse
shorter descending factorials, divided by their order. Source: focused BV reroute,
exact tail telescope. -/
theorem inv_cast_descFactorial_eq_sub {ν k : ℕ} (hν : 0 < ν) (hk : ν < k) :
    (k.descFactorial (ν + 1) : ℝ)⁻¹ =
      (((k - 1).descFactorial ν : ℝ)⁻¹ - (k.descFactorial ν : ℝ)⁻¹) / ν := by
  have hν0 : (ν : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hν
  have hA : ((k - 1).descFactorial ν : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hB : (k.descFactorial ν : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hC : (k.descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hleft : (k.descFactorial (ν + 1) : ℝ) = k * ((k - 1).descFactorial ν : ℝ) := by
    have h := Nat.succ_descFactorial_succ (k - 1) ν
    rw [show k - 1 + 1 = k by omega] at h
    exact_mod_cast h
  have hright : (k.descFactorial (ν + 1) : ℝ) = ((k : ℝ) - ν) * (k.descFactorial ν : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
  field_simp [hA, hB, hC, hν0]
  linear_combination -(k.descFactorial ν : ℝ) * hleft + ((k - 1).descFactorial ν : ℝ) * hright

/-- A finite descending-factorial tail has an exact positive remainder.
Source: focused BV reroute, exact tail telescope. -/
theorem sum_inv_cast_descFactorial_tail {ν n : ℕ} (hν : 0 < ν) (hn : ν ≤ n) (m : ℕ) :
    (∑ j ∈ range m, ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹) =
      (((n.descFactorial ν : ℝ)⁻¹ - ((n + m).descFactorial ν : ℝ)⁻¹) / ν) := by
  have hterm (j : ℕ) : ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹ =
      (((n + j).descFactorial ν : ℝ)⁻¹ - ((n + (j + 1)).descFactorial ν : ℝ)⁻¹) / ν := by
    rw [inv_cast_descFactorial_eq_sub hν (by omega), show n + 1 + j - 1 = n + j by omega,
      show n + 1 + j = n + (j + 1) by omega]
  simp_rw [hterm]
  rw [← sum_div, sum_range_sub']
  simp

/-- The inverse descending-factorial tail is summable, with bound
`1/(ν n(n−1)⋯(n−ν+1))`. Source: focused BV reroute, exact tail telescope. -/
theorem summable_inv_cast_descFactorial_tail {ν n : ℕ} (hν : 0 < ν) (hn : ν ≤ n) :
    Summable (fun j => ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹) := by
  apply summable_of_sum_range_le (c := (n.descFactorial ν : ℝ)⁻¹ / ν)
    (fun j => by positivity)
  intro m
  rw [sum_inv_cast_descFactorial_tail hν hn]
  exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (Nat.cast_nonneg ν)

/-- The summed inverse descending-factorial tail has the same explicit bound as
its finite partial sums. Source: focused BV reroute, exact tail telescope. -/
theorem tsum_inv_cast_descFactorial_tail_le {ν n : ℕ} (hν : 0 < ν) (hn : ν ≤ n) :
    (∑' j, ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹) ≤ (n.descFactorial ν : ℝ)⁻¹ / ν := by
  apply (summable_inv_cast_descFactorial_tail hν hn).tsum_le_of_sum_range_le
  intro m
  rw [sum_inv_cast_descFactorial_tail hν hn]
  exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (Nat.cast_nonneg ν)

/-- Inverse descending factorials are discretely convex above all their poles.
Source: finite midpoint form of the focused BV quadrature tail estimate. -/
theorem two_mul_inv_cast_descFactorial_le_adjacent {ν k : ℕ} (hk : ν + 1 < k) :
    2 * (k.descFactorial (ν + 1) : ℝ)⁻¹ ≤
      ((k - 1).descFactorial (ν + 1) : ℝ)⁻¹ + ((k + 1).descFactorial (ν + 1) : ℝ)⁻¹ := by
  have hA0 : ((k - 1).descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hB0 : (k.descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hC0 : ((k + 1).descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (ν : ℝ) + 1 < k := by exact_mod_cast hk
  have hkν : (0 : ℝ) < k - ν - 1 := by linarith
  have hknu : (0 : ℝ) < k - ν := by linarith
  have hkp : (0 : ℝ) < k + 1 := by positivity
  have hA : ((k - 1).descFactorial (ν + 1) : ℝ) =
      ((k : ℝ) - ν - 1) * ((k - 1).descFactorial ν : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega),
      Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hB : (k.descFactorial (ν + 1) : ℝ) = k * ((k - 1).descFactorial ν : ℝ) := by
    have h := Nat.succ_descFactorial_succ (k - 1) ν
    rw [show k - 1 + 1 = k by omega] at h
    exact_mod_cast h
  have hC : ((k + 1).descFactorial (ν + 1) : ℝ) =
      (k + 1 : ℝ) * (k.descFactorial ν : ℝ) := by exact_mod_cast Nat.succ_descFactorial_succ k ν
  have hB' : (k.descFactorial (ν + 1) : ℝ) = ((k : ℝ) - ν) * (k.descFactorial ν : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
  have hleft : (k : ℝ) * ((k - 1).descFactorial (ν + 1) : ℝ) =
      ((k : ℝ) - ν - 1) * (k.descFactorial (ν + 1) : ℝ) := by rw [hA, hB]; ring
  have hright : ((k : ℝ) - ν) * ((k + 1).descFactorial (ν + 1) : ℝ) =
      (k + 1 : ℝ) * (k.descFactorial (ν + 1) : ℝ) := by rw [hC, hB']; ring
  have hAinv : ((k - 1).descFactorial (ν + 1) : ℝ)⁻¹ =
      (k : ℝ) / (k - ν - 1) * (k.descFactorial (ν + 1) : ℝ)⁻¹ := by
    field_simp [hA0, hB0, ne_of_gt hkν]
    linear_combination -hleft
  have hCinv : ((k + 1).descFactorial (ν + 1) : ℝ)⁻¹ =
      ((k : ℝ) - ν) / (k + 1) * (k.descFactorial (ν + 1) : ℝ)⁻¹ := by
    field_simp [hC0, hB0, ne_of_gt hkp]
    linear_combination -hright
  have hrat : (2 : ℝ) ≤ (k : ℝ) / (k - ν - 1) + ((k : ℝ) - ν) / (k + 1) := by
    have hid : (k : ℝ) / (k - ν - 1) + ((k : ℝ) - ν) / (k + 1) - 2 =
        ((ν : ℝ) + 1) * (ν + 2) / ((k - ν - 1) * (k + 1)) := by
      field_simp [ne_of_gt hkν, ne_of_gt hkp]
      ring
    have hnon : 0 ≤ ((ν : ℝ) + 1) * (ν + 2) / ((k - ν - 1) * (k + 1)) := by positivity
    rw [← hid] at hnon
    linarith
  rw [hAinv, hCinv, ← add_mul]
  exact mul_le_mul_of_nonneg_right hrat (by positivity)

/-- The positive-index even tail of an inverse descending-factorial envelope gains
one half of the full tail bound. Source: focused BV quadrature reroute; discrete
convexity gives the midpoint comparison without an improper integral.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem tsum_even_inv_cast_descFactorial_tail_le {ν s : ℕ} (hν : 0 < ν) (hs : ν < s) :
    (∑' k : ℕ, if s < k ∧ Even k then (k.descFactorial (ν + 1) : ℝ)⁻¹ else 0) ≤
      1 / (2 * (ν : ℝ) * ((s : ℝ) - ν) ^ ν) := by
  let m := 2 * (s / 2 + 1)
  let r := m - 1
  let g := fun k : ℕ => (k.descFactorial (ν + 1) : ℝ)⁻¹
  have hm : s < m := by dsimp [m]; omega
  have hr : s ≤ r := by dsimp [r]; omega
  have hss : Summable (fun j => g (r + j)) := by
    have h := summable_inv_cast_descFactorial_tail hν (show ν ≤ r - 1 by omega)
    simpa only [show r - 1 + 1 = r by omega] using h
  have hA : Summable (fun j => g (r + (2 * j + 1))) := by
    convert hss.comp_injective (show Function.Injective (fun j : ℕ => 2 * j + 1) by intro a b h; dsimp only at h; omega) using 1 <;> rfl
  have hB : Summable (fun j => g (r + 2 * j)) := by
    convert hss.comp_injective (show Function.Injective (fun j : ℕ => 2 * j) by intro a b h; dsimp only at h; omega) using 1 <;> rfl
  have hBs : Summable (fun j => g (r + 2 * (j + 1))) := by
    convert hB.comp_injective Nat.succ_injective using 1 <;> rfl
  have hmid (j : ℕ) : 2 * g (r + (2 * j + 1)) ≤ g (r + 2 * j) + g (r + 2 * (j + 1)) := by
    have h := two_mul_inv_cast_descFactorial_le_adjacent (show ν + 1 < r + (2 * j + 1) by omega)
    simpa only [show r + (2 * j + 1) - 1 = r + 2 * j by omega,
      show r + (2 * j + 1) + 1 = r + 2 * (j + 1) by omega] using h
  have hab : (∑' j, g (r + (2 * j + 1))) ≤ ∑' j, g (r + 2 * j) := by
    have h := (hA.mul_left 2).tsum_le_tsum hmid (hB.add hBs)
    rw [tsum_mul_left, hB.tsum_add hBs] at h
    have hz := hB.tsum_eq_zero_add
    have hg0 : 0 ≤ g r := by dsimp [g]; positivity
    simp only [mul_zero, add_zero] at hz
    linarith
  have htotal : (∑' j, g (r + j)) =
      (∑' j, g (r + 2 * j)) + ∑' j, g (r + (2 * j + 1)) := by
    have he := (Nat.divModEquiv 2).symm.tsum_eq (fun j => g (r + j))
    have hp : Summable (fun p : ℕ × Fin 2 => g (r + (Nat.divModEquiv 2).symm p)) := by
      convert hss.comp_injective (Nat.divModEquiv 2).symm.injective using 1 <;> rfl
    rw [← he, hp.tsum_prod]
    simp only [Nat.divModEquiv_symm_apply, tsum_fintype, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
      add_zero, Nat.mul_comm _ 2]
    exact hB.tsum_add hA
  let f := fun k : ℕ => if s < k ∧ Even k then g k else 0
  have hinj : Function.Injective (fun j : ℕ => 2 * j + m) := by intro i j h; dsimp only at h; omega
  have hsup : Function.support f ⊆ Set.range (fun j : ℕ => 2 * j + m) := by
    intro k hk
    have hcond : s < k ∧ Even k := by
      by_contra h
      change f k ≠ 0 at hk
      simp [f, h] at hk
    have hke := Nat.even_iff.mp hcond.2
    refine ⟨k / 2 - (s / 2 + 1), ?_⟩
    dsimp [m]
    omega
  have heven : (∑' k, f k) = ∑' j, g (r + (2 * j + 1)) := by
    rw [← hinj.tsum_eq hsup]
    apply tsum_congr
    intro j
    have hjEven : Even (2 * j + m) := by dsimp [m]; rw [Nat.even_iff]; omega
    rw [show f (2 * j + m) = g (2 * j + m) by dsimp [f]; rw [if_pos ⟨by omega, hjEven⟩]]
    congr 1
    dsimp [r]
    omega
  have hfull : (∑' j, g (r + j)) ≤ ( (r - 1).descFactorial ν : ℝ)⁻¹ / ν := by
    simpa only [show r - 1 + 1 = r by omega] using
      tsum_inv_cast_descFactorial_tail_le hν (show ν ≤ r - 1 by omega)
  have hden : ((s : ℝ) - ν) ^ ν ≤ ((r - 1).descFactorial ν : ℝ) := by
    have h := Nat.pow_sub_le_descFactorial (r - 1) ν
    rw [show r - 1 + 1 = r by omega] at h
    have hle : (s - ν) ^ ν ≤ (r - ν) ^ ν := Nat.pow_le_pow_left (Nat.sub_le_sub_right hr ν) ν
    have hR : (((s - ν) ^ ν : ℕ) : ℝ) ≤ ((r - 1).descFactorial ν : ℝ) := by exact_mod_cast hle.trans h
    simpa only [Nat.cast_pow, Nat.cast_sub hs.le] using hR
  have hpower : 0 < ((s : ℝ) - ν) ^ ν := by
    have hsr : (ν : ℝ) < s := by exact_mod_cast hs
    positivity
  have hshort : ((r - 1).descFactorial ν : ℝ)⁻¹ / ν ≤ 1 / ((ν : ℝ) * ((s : ℝ) - ν) ^ ν) := by
    have hνR : (0 : ℝ) < ν := by exact_mod_cast hν
    have h := inv_anti₀ hpower hden
    have hd := div_le_div_of_nonneg_right h hνR.le
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, mul_comm, mul_one] using hd
  change (∑' k, f k) ≤ _
  rw [heven]
  have h := hfull.trans hshort
  rw [htotal] at h
  have hhalf : 2 * (∑' j, g (r + (2 * j + 1))) ≤ 1 / ((ν : ℝ) * ((s : ℝ) - ν) ^ ν) := by linarith
  have hd : (0 : ℝ) < (ν : ℝ) * ((s : ℝ) - ν) ^ ν := by
    have hνR : (0 : ℝ) < ν := by exact_mod_cast hν
    positivity
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ν : ℝ) * ((s : ℝ) - ν) ^ ν)).mpr
  have hmul := (le_div_iff₀ hd).mp hhalf
  nlinarith

/-- Inverse descending factorials of order at least two are summable; their finitely
many zero-denominator terms are totalized to zero. Source: exact tail telescope. -/
theorem summable_inv_cast_descFactorial {ν : ℕ} (hν : 0 < ν) :
    Summable (fun k : ℕ => (k.descFactorial (ν + 1) : ℝ)⁻¹) := by
  rw [← summable_nat_add_iff (ν + 1)]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    summable_inv_cast_descFactorial_tail hν (le_refl ν)

/-- A descending-factorial coefficient envelope bounds its absolute even tail with
the sharp half-tail factor. Source: discrete midpoint and exact tail telescope in
focused BV quadrature reroute. -/
theorem tsum_even_abs_tail_le_of_descFactorial {c : ℕ → ℝ}
    (hcS : Summable (fun k => |c k|)) {ν s : ℕ} (hν : 0 < ν) (hs : ν < s)
    {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ k, ν + 1 ≤ k → |c k| ≤ A * (k.descFactorial (ν + 1) : ℝ)⁻¹) :
    (∑' k : ℕ, if s < k ∧ Even k then |c k| else 0) ≤
      A / (2 * (ν : ℝ) * ((s : ℝ) - ν) ^ ν) := by
  have ht : Summable (fun k => if s < k ∧ Even k then |c k| else 0) :=
    hcS.of_nonneg_of_le (by intro k; split_ifs <;> positivity) (by intro k; split_ifs <;> simp)
  have hg : Summable (fun k => if s < k ∧ Even k then (k.descFactorial (ν + 1) : ℝ)⁻¹ else 0) :=
    (summable_inv_cast_descFactorial hν).of_nonneg_of_le
      (by intro k; split_ifs <;> positivity) (by intro k; split_ifs; rfl; positivity)
  calc
    _ ≤ ∑' k, A * (if s < k ∧ Even k then (k.descFactorial (ν + 1) : ℝ)⁻¹ else 0) := by
      apply ht.tsum_le_tsum _ (hg.mul_left A)
      intro k
      split_ifs with h
      · exact hc k (by omega)
      · simp
    _ = A * (∑' k, if s < k ∧ Even k then (k.descFactorial (ν + 1) : ℝ)⁻¹ else 0) := by rw [tsum_mul_left]
    _ ≤ A * (1 / (2 * (ν : ℝ) * ((s : ℝ) - ν) ^ ν)) :=
      mul_le_mul_of_nonneg_left (tsum_even_inv_cast_descFactorial_tail_le hν hs) hA
    _ = _ := by ring

end NLAlib
