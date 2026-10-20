import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import NLAlib.Matrix.Functions.FrameBarrierIteration

/-!
# Deterministic rank-one sparsification: scalar and natural-budget parameters

This file develops the scalar budget side of deterministic rank-one
sparsification (Batson--Spielman--Srivastava, *Twice-Ramanujan Sparsifiers*
(2008), Theorem 3.1 and Section 3.2,
[arXiv:0808.0163](https://arxiv.org/abs/0808.0163)): the real sparsification factor, its continuity, the
integer-budget spectral sandwich obtained from the square-budget
frame theorem, and the natural budget sequence with ratio tending to the
target real budget.

The natural sequence is the elementary statement-preserving route for the
real parameter `d`: in dimension `N`, we take `q m = ⌊d·N·(m+R)⌋` for a
large shift `R`; the floor inequality `q m < (m+R)·(⌊d·N⌋+1)` gives the
strict upper support bound used in the block amplification/compactness step.
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix BigOperators MatrixOrder
open Filter

namespace NLAlib

/-- The scalar sparsification factor `(d + 1 + 2√d) / (d + 1 - 2√d)`
of Batson--Spielman--Srivastava (2008), Theorem 3.1.  It is the total
real function used as the Loewner upper constant in the integer-budget
sparsification theorem; its analytical facts below are restricted to
`d > 1` (where the denominator is positive). -/
def rankOneSparsificationFactor (d : ℝ) : ℝ :=
  (d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)

/-- For `d ≥ 0`, the sparsification factor is the square of
`(√d + 1) / (√d - 1)`.  No division cancellation is used, so the
totalized `d = 1` case is included correctly. -/
theorem rankOneSparsificationFactor_eq_sq_div_sq {d : ℝ} (hd : 0 ≤ d) :
    rankOneSparsificationFactor d =
      (Real.sqrt d + 1) ^ 2 / (Real.sqrt d - 1) ^ 2 := by
  unfold rankOneSparsificationFactor
  have hnum : d + 1 + 2 * Real.sqrt d = (Real.sqrt d + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hd]
  have hden : d + 1 - 2 * Real.sqrt d = (Real.sqrt d - 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hd]
  rw [hnum, hden]

/-- `rankOneSparsificationFactor` is continuous at every `d > 1`
(the denominator `d + 1 - 2√d = (√d - 1)²` is strictly positive there). -/
theorem continuousAt_rankOneSparsificationFactor {d : ℝ} (hd : 1 < d) :
    ContinuousAt rankOneSparsificationFactor d := by
  have hsqrt_gt : 1 < Real.sqrt d := by
    simpa using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hd
  have hden_eq : d + 1 - 2 * Real.sqrt d = (Real.sqrt d - 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ d by linarith)]
  have hden_pos : 0 < d + 1 - 2 * Real.sqrt d := by
    rw [hden_eq]
    exact sq_pos_of_pos (sub_pos.mpr hsqrt_gt)
  have hid : ContinuousAt (fun x : ℝ => x) d := continuousAt_id
  have hc1 : ContinuousAt (fun x : ℝ => (1 : ℝ)) d := continuousAt_const
  have hc2 : ContinuousAt (fun x : ℝ => (2 : ℝ)) d := continuousAt_const
  have hsqrt : ContinuousAt (fun x : ℝ => Real.sqrt x) d :=
    Real.continuous_sqrt.continuousAt
  have hnum1 : ContinuousAt (fun x : ℝ => x + 1) d := ContinuousAt.add hid hc1
  have hnum2 : ContinuousAt (fun x : ℝ => 2 * Real.sqrt x) d :=
    ContinuousAt.mul hc2 hsqrt
  have hden1 : ContinuousAt (fun x : ℝ => x + 1) d := ContinuousAt.add hid hc1
  have hden2 : ContinuousAt (fun x : ℝ => 2 * Real.sqrt x) d :=
    ContinuousAt.mul hc2 hsqrt
  have hn_cont : ContinuousAt (fun x : ℝ => x + 1 + 2 * Real.sqrt x) d :=
    ContinuousAt.add hnum1 hnum2
  have hd_cont : ContinuousAt (fun x : ℝ => x + 1 - 2 * Real.sqrt x) d :=
    ContinuousAt.sub hden1 hden2
  unfold rankOneSparsificationFactor
  exact ContinuousAt.div hn_cont hd_cont hden_pos.ne'

namespace RankOneBarrier

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- **Integer-budget spectral sandwich.**  Let `v : I → n → ℝ` be a real
isotropic frame (`∑ i, v_i v_iᵀ = 1`) and let `q` be a natural number with
`N = Fintype.card n < q`.  Then there are nonnegative weights `s` with
support at most `q` such that the weighted Gram matrix satisfies the
Loewner sandwich

`1 ≤ ∑ i, s i • v_i v_iᵀ ≤ rankOneSparsificationFactor (q / N) • 1`.

With `a = √(q / N) > 1` we have `a² = q / N` and `q = N·a²`, so the
result is the square-budget theorem
`exists_nonneg_weights_spectral_sandwich_of_sq_budget` applied to
`a`, with its upper constant `((a+1)²/(a-1)²)` identified with the factor
via `rankOneSparsificationFactor_eq_sq_div_sq`.

Source: BSS 2008, Theorem 3.1 and Section 3.2. -/
theorem exists_nonneg_weights_spectral_sandwich_of_card_lt_budget [Nonempty n]
    (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (q : ℕ) (hq : Fintype.card n < q) :
    ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧
      (Function.support s).ncard ≤ q ∧
      ((1 : Matrix n n ℝ) ≤ ∑ i, s i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, s i • Matrix.vecMulVec (v i) (v i) ≤
        rankOneSparsificationFactor ((q : ℝ) / (Fintype.card n : ℝ)) •
          (1 : Matrix n n ℝ)) := by
  classical
  let N : ℝ := Fintype.card n
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty n›)
  have hq_nat : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_nat
  have hqN_pos : 0 < (q : ℝ) / N := div_pos hq_pos hNpos
  let a : ℝ := Real.sqrt ((q : ℝ) / N)
  have ha1 : 1 < a := by
    dsimp [a]
    have hlt : 1 < (q : ℝ) / N := by
      rw [one_lt_div hNpos]
      dsimp [N]
      exact_mod_cast hq
    simpa using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hlt
  have hq' : (q : ℝ) = N * a ^ 2 := by
    dsimp [a]
    rw [Real.sq_sqrt (le_of_lt hqN_pos)]
    rw [mul_comm, div_mul_cancel₀ (q : ℝ) hNpos.ne']
  obtain ⟨s, hs_nonneg, hs_card, hs_lower, hs_upper⟩ :=
    exists_nonneg_weights_spectral_sandwich_of_sq_budget (I := I) (n := n)
      v hframe a ha1 q hq'
  have hfac : rankOneSparsificationFactor ((q : ℝ) / N) =
      (a + 1) ^ 2 / (a - 1) ^ 2 := by
    have hf := rankOneSparsificationFactor_eq_sq_div_sq (d := (q : ℝ) / N)
      (hd := le_of_lt hqN_pos)
    simpa [a] using hf
  refine ⟨s, hs_nonneg, hs_card, hs_lower, ?_⟩
  rw [hfac]
  exact hs_upper

end RankOneBarrier

/-- **Natural-budget ratio sequence.**  For `N > 0` and a real target
budget `d > 1`, there are sequences `r`, `q : ℕ → ℕ` with
`q m = ⌊d·N·(r m)⌋` such that for every `m`:

* `0 < r m`,
* `N * r m < q m` (the budget strictly exceeds the amplified dimension),
* `q m < r m * (⌊d·N⌋ + 1)` (strict upper support bound, used for the
  pigeonhole step in block amplification/compactness), and
* `(q m : ℝ) / ((N : ℝ) * (r m : ℝ)) → d` as `m → ∞`.

The floor identity is exposed verbatim.  The convergence follows by
squeezing `d - 1/(N·r m) < q m/(N·r m) ≤ d`, where the error
`1/(N·r m)` tends to zero.  This is the elementary statement-preserving
route that turns the real parameter `d` into a natural budget sequence. -/
theorem exists_nat_budget_ratio_tendsto (N : ℕ) (hN : 0 < N) (d : ℝ)
    (hd : 1 < d) :
    ∃ r q : ℕ → ℕ,
      (∀ m,
        0 < r m ∧
        q m = Nat.floor (d * (N : ℝ) * (r m : ℝ)) ∧
        N * r m < q m ∧
        q m < r m * (Nat.floor (d * (N : ℝ)) + 1)) ∧
      Tendsto (fun m => (q m : ℝ) / ((N : ℝ) * (r m : ℝ))) atTop (nhds d) := by
  classical
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / ((N : ℝ) * (d - 1)))
  have hNd_pos : 0 < (N : ℝ) * (d - 1) :=
    mul_pos (by exact_mod_cast hN) (sub_pos.mpr hd)
  have hR_pos : 0 < (R : ℝ) :=
    lt_trans (div_pos (by norm_num) hNd_pos) hR
  have hR_nat : 0 < R := by
    exact_mod_cast hR_pos
  have hR_mul : 1 < (N : ℝ) * (d - 1) * (R : ℝ) := by
    have hdiv := (div_lt_iff₀ hNd_pos).mp hR
    nlinarith [hdiv]
  let r : ℕ → ℕ := fun m => m + R
  let q : ℕ → ℕ := fun m => Nat.floor (d * (N : ℝ) * (r m : ℝ))
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hr_pos : ∀ m, 0 < r m := by
    intro m
    dsimp [r]
    exact Nat.lt_of_lt_of_le hR_nat (Nat.le_add_left R m)
  have hr_pos_real : ∀ m, 0 < (r m : ℝ) := by
    intro m
    exact_mod_cast hr_pos m
  have hden_pos : ∀ m, 0 < (N : ℝ) * (r m : ℝ) :=
    fun m => mul_pos hN_pos (hr_pos_real m)
  have hden_ne : ∀ m, (N : ℝ) * (r m : ℝ) ≠ 0 :=
    fun m => ne_of_gt (hden_pos m)
  have hsub : ∀ m, (N : ℝ) * (r m : ℝ) < d * (N : ℝ) * (r m : ℝ) - 1 := by
    intro m
    have hprod_mul : 1 < (N : ℝ) * (d - 1) * (r m : ℝ) := by
      have hrr : (R : ℝ) ≤ (r m : ℝ) := by
        dsimp [r]
        exact_mod_cast (Nat.le_add_left R m)
      have hmul : (N : ℝ) * (d - 1) * (R : ℝ) ≤
          (N : ℝ) * (d - 1) * (r m : ℝ) :=
        mul_le_mul_of_nonneg_left hrr (le_of_lt hNd_pos)
      exact lt_of_lt_of_le hR_mul hmul
    have hprod_eq : (N : ℝ) * (d - 1) * (r m : ℝ) =
        d * (N : ℝ) * (r m : ℝ) - (N : ℝ) * (r m : ℝ) := by
      ring
    rw [hprod_eq] at hprod_mul
    linarith
  have hq_gt : ∀ m, d * (N : ℝ) * (r m : ℝ) - 1 < (q m : ℝ) := by
    intro m
    simpa [q] using (Nat.sub_one_lt_floor (d * (N : ℝ) * (r m : ℝ)))
  have hstep : ∀ m, (d - 1 / ((N : ℝ) * (r m : ℝ))) * ((N : ℝ) * (r m : ℝ)) =
      d * (N : ℝ) * (r m : ℝ) - 1 := by
    intro m
    rw [sub_mul, one_div_mul_cancel (hden_ne m)]
    ring
  have hlow : ∀ m, d - 1 / ((N : ℝ) * (r m : ℝ)) <
      (q m : ℝ) / ((N : ℝ) * (r m : ℝ)) := by
    intro m
    rw [lt_div_iff₀ (hden_pos m)]
    rw [hstep m]
    exact hq_gt m
  have hup : ∀ m, (q m : ℝ) / ((N : ℝ) * (r m : ℝ)) ≤ d := by
    intro m
    rw [div_le_iff₀ (hden_pos m)]
    have hd_pos : 0 < d := lt_trans (by norm_num) hd
    have hnonneg : 0 ≤ d * (N : ℝ) * (r m : ℝ) := by
      positivity
    have hfloor_le : (q m : ℝ) ≤ d * (N : ℝ) * (r m : ℝ) := by
      simpa [q] using (Nat.floor_le hnonneg)
    simpa [mul_assoc] using hfloor_le
  refine ⟨r, q, ?_, ?_⟩
  · intro m
    refine ⟨hr_pos m, rfl, ?_, ?_⟩
    · have hreal : (N : ℝ) * (r m : ℝ) < (q m : ℝ) :=
        lt_trans (hsub m) (hq_gt m)
      exact_mod_cast hreal
    · have hk : d * (N : ℝ) < (Nat.floor (d * (N : ℝ)) : ℝ) + 1 := by
        exact Nat.lt_floor_add_one (d * (N : ℝ))
      have hk_mul : d * (N : ℝ) * (r m : ℝ) <
          (r m : ℝ) * ((Nat.floor (d * (N : ℝ)) : ℝ) + 1) := by
        have hkm := mul_lt_mul_of_pos_right hk (hr_pos_real m)
        simpa [mul_comm, mul_assoc] using hkm
      have hd_pos : 0 < d := lt_trans (by norm_num) hd
      have hnonneg : 0 ≤ d * (N : ℝ) * (r m : ℝ) := by
        positivity
      have hfloor_le : (q m : ℝ) ≤ d * (N : ℝ) * (r m : ℝ) := by
        simpa [q] using (Nat.floor_le hnonneg)
      have hquot : (q m : ℝ) <
          (r m : ℝ) * ((Nat.floor (d * (N : ℝ)) : ℝ) + 1) :=
        lt_of_le_of_lt hfloor_le hk_mul
      exact_mod_cast hquot
  · have hZ : Tendsto (fun m : ℕ => 1 / ((N : ℝ) * (r m : ℝ))) atTop (nhds 0) := by
      have hcomp : Tendsto (fun m : ℕ => (1 / (N : ℝ)) / ((m + R : ℕ) : ℝ)) atTop (nhds 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat (1 / (N : ℝ))).comp
          (Filter.tendsto_add_atTop_nat R)
      simpa only [r, div_div] using hcomp
    have hL : Tendsto (fun m : ℕ => d - 1 / ((N : ℝ) * (r m : ℝ))) atTop
        (nhds d) := by
      have hc : Tendsto (fun m : ℕ => d) atTop (nhds d) := tendsto_const_nhds
      have := hc.sub hZ
      simpa only [sub_zero] using this
    have hU : Tendsto (fun m : ℕ => d) atTop (nhds d) := tendsto_const_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
    · filter_upwards with m
      exact le_of_lt (hlow m)
    · filter_upwards with m
      exact hup m

end NLAlib
