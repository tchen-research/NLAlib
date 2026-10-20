import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Order
import NLAlib.Matrix.Functions.RankOneBarrierUpdate

/-!
# Finite rank-one barrier iteration

This file proves a genuine finite iteration of the rank-one barrier step of
Batson--Spielman--Srivastava, *Twice-Ramanujan Sparsifiers* (2008), Section 3.2
([arXiv:0808.0163](https://arxiv.org/abs/0808.0163)).

For a real isotropic frame `v i` in `ℝ^n` (`∑ i, v_i v_iᵀ = 1`), scalar
barrier parameters `u0 > 0`, `l0 < 0`, shifts `δU, δL > 0`, and
reciprocal-potential budgets `epsU`, `epsL`, the theorem
`exists_weights_barriers_of_potential_bounds` shows that for every finite
horizon `k` there are nonnegative weights `s i` with at most `k` supporting
indices such that the weighted Gram matrix
`A = ∑ i, s i • v_i v_iᵀ` satisfies, for `u = u0 + k*δU` and
`l = l0 + k*δL`,

* `u•1 - A ≻ 0` and `tr((u•1 - A)⁻¹) ≤ epsU`, and
* `A - l•1 ≻ 0` and `tr((A - l•1)⁻¹) ≤ epsL`.

The proof is an ordinary induction on `k`: at each step the strict lower
potential cap and the reciprocal-potential compatibility are derived from the
invariants at the previous step, `exists_updates_of_frame` produces one
rank-one update, and the new weights are `s j + (if j = i then t else 0)`.
Repeated indices are permitted and combine their coefficients; no index is
assumed fresh.

The specialization `exists_nonneg_weights_spectral_sandwich_of_sq_budget`
instantiates the exact BSS constants for an
integer budget `q` with `(q : ℝ) = N*a²` (`N = Fintype.card n`): after
normalizing the returned weights by `1/lq` with `lq = N*a*(a-1)`, the
Loewner sandwich

`1 ≤ ∑ i, sFinal i • v_i v_iᵀ ≤ ((a+1)²/(a-1)²) • 1`

holds with support at most `q`.

The extension to every real `d > 1` with support at most `⌊d*N⌋` requires
a separate block amplification and compactness argument. This file proves
the finite iteration and its exact integer-budget specialization.
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix BigOperators MatrixOrder

namespace NLAlib
namespace RankOneBarrier

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- The inverse of a nonzero scalar multiple of the identity is the inverse
scalar multiple of the identity. -/
private theorem inv_smul_one_of_ne_zero (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : Matrix n n ℝ))⁻¹ = c⁻¹ • (1 : Matrix n n ℝ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
  rw [inv_mul_cancel₀ hc, one_smul]

/-- Trace of the inverse of a nonzero scalar multiple of the identity:
`tr((c•1)⁻¹) = N / c`. -/
private theorem trace_inv_smul_one (c : ℝ) (hc : c ≠ 0) :
    ((c • (1 : Matrix n n ℝ))⁻¹).trace = (Fintype.card n : ℝ) / c := by
  rw [inv_smul_one_of_ne_zero c hc, Matrix.trace_smul, Matrix.trace_one]
  rw [div_eq_mul_inv]
  ring

/-- **Finite rank-one barrier iteration.**  For a real isotropic frame
`v : I → n → ℝ` (`∑ i, v_i v_iᵀ = 1`) and scalar barrier parameters with
`u0 > 0`, `l0 < 0`, `δU, δL > 0`, satisfying the initial budget
`N/u0 ≤ epsU`, `N/(-l0) ≤ epsL`, the strict lower potential cap
`δL*epsL < 1`, and the reciprocal-potential compatibility
`1/δU + epsU ≤ 1/δL - epsL`, there are, for every finite horizon `k`,
nonnegative weights `s` with `(Function.support s).ncard ≤ k` such that with
`A = ∑ i, s i • v_i v_iᵀ`, `u = u0 + k*δU`, `l = l0 + k*δL`,

* `u•1 - A ≻ 0` and `tr((u•1 - A)⁻¹) ≤ epsU`, and
* `A - l•1 ≻ 0` and `tr((A - l•1)⁻¹) ≤ epsL`.

Source: BSS 2008, Section 3.2 finite iteration. -/
theorem exists_weights_barriers_of_potential_bounds [Nonempty n]
    (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (u0 l0 deltaU deltaL epsU epsL : ℝ)
    (hu0 : 0 < u0) (hl0 : l0 < 0)
    (hδU : 0 < deltaU) (hδL : 0 < deltaL)
    (hU0 : (Fintype.card n : ℝ) / u0 ≤ epsU)
    (hL0 : (Fintype.card n : ℝ) / (-l0) ≤ epsL)
    (hcap0 : deltaL * epsL < 1)
    (hpot0 : 1 / deltaU + epsU ≤ 1 / deltaL - epsL) :
    ∀ k : ℕ, ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧
      (Function.support s).ncard ≤ k ∧
      (let A := ∑ i, s i • Matrix.vecMulVec (v i) (v i)
       let u := u0 + (k : ℝ) * deltaU
       let l := l0 + (k : ℝ) * deltaL
       (u • (1 : Matrix n n ℝ) - A).PosDef ∧
       ((u • (1 : Matrix n n ℝ) - A)⁻¹).trace ≤ epsU ∧
       (A - l • (1 : Matrix n n ℝ)).PosDef ∧
       ((A - l • (1 : Matrix n n ℝ))⁻¹).trace ≤ epsL) := by
  classical
  intro k
  induction k with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro i
        simp
      · have hsup : Function.support (fun _ : I => (0 : ℝ)) = ∅ := by
          ext i
          simp
        rw [hsup]
        simp
      · have hUpos0 : (u0 • (1 : Matrix n n ℝ)).PosDef := by
          simpa using (Matrix.PosDef.smul Matrix.PosDef.one hu0)
        have hUtr0 : ((u0 • (1 : Matrix n n ℝ))⁻¹).trace ≤ epsU := by
          rw [trace_inv_smul_one u0 hu0.ne.symm]
          exact hU0
        have hLpos0 : (-(l0 • (1 : Matrix n n ℝ))).PosDef := by
          rw [← neg_smul]
          exact (Matrix.PosDef.smul Matrix.PosDef.one (neg_pos.mpr hl0))
        have hLtr0 : ((-(l0 • (1 : Matrix n n ℝ)))⁻¹).trace ≤ epsL := by
          have htr : ((-l0 • (1 : Matrix n n ℝ))⁻¹).trace =
              (Fintype.card n : ℝ) / (-l0) :=
            trace_inv_smul_one (-l0) (neg_ne_zero.mpr (ne_of_lt hl0))
          rw [← neg_smul]
          rwa [htr]
        dsimp
        constructor
        · simpa using hUpos0
        · constructor
          · simpa using hUtr0
          · constructor
            · simpa using hLpos0
            · simpa using hLtr0
  | succ k ih =>
      obtain ⟨s, hs_nonneg, hs_card, hs_barriers⟩ := ih
      let A : Matrix n n ℝ := ∑ i, s i • Matrix.vecMulVec (v i) (v i)
      let u : ℝ := u0 + (k : ℝ) * deltaU
      let l : ℝ := l0 + (k : ℝ) * deltaL
      have hUpos : (u • (1 : Matrix n n ℝ) - A).PosDef := by
        simpa [A, u] using hs_barriers.1
      have hUtr : ((u • (1 : Matrix n n ℝ) - A)⁻¹).trace ≤ epsU := by
        simpa [A, u] using hs_barriers.2.1
      have hLpos : (A - l • (1 : Matrix n n ℝ)).PosDef := by
        simpa [A, l] using hs_barriers.2.2.1
      have hLtr : ((A - l • (1 : Matrix n n ℝ))⁻¹).trace ≤ epsL := by
        simpa [A, l] using hs_barriers.2.2.2
      let MU : Matrix n n ℝ := u • (1 : Matrix n n ℝ) - A
      let ML : Matrix n n ℝ := A - l • (1 : Matrix n n ℝ)
      have hMU : MU.PosDef := by simpa [MU] using hUpos
      have hML : ML.PosDef := by simpa [ML] using hLpos
      have hcap : deltaL * ML⁻¹.trace < 1 := by
        have hle : deltaL * ML⁻¹.trace ≤ deltaL * epsL := by
          exact mul_le_mul_of_nonneg_left (by simpa [ML] using hLtr) hδL.le
        exact lt_of_le_of_lt hle hcap0
      have hUtrMU : MU⁻¹.trace ≤ epsU := by simpa [MU] using hUtr
      have hLtrML : ML⁻¹.trace ≤ epsL := by simpa [ML] using hLtr
      have hpot : 1 / deltaU + MU⁻¹.trace ≤ 1 / deltaL - ML⁻¹.trace := by
        calc
          1 / deltaU + MU⁻¹.trace ≤ 1 / deltaU + epsU := by
            simpa [add_comm] using (add_le_add_left hUtrMU (1 / deltaU))
          _ ≤ 1 / deltaL - epsL := hpot0
          _ ≤ 1 / deltaL - ML⁻¹.trace := by
            exact sub_le_sub_left hLtrML (1 / deltaL)
      obtain ⟨i, hvi, t, ht, hUpos1, hUtr1, hLpos1, hLtr1⟩ :=
        exists_updates_of_frame (I := I) (n := n) v hframe MU hMU ML hML
          deltaU deltaL hδU hδL hcap hpot
      let s' : I → ℝ := fun j => s j + if j = i then t else 0
      let A' : Matrix n n ℝ := ∑ j, s' j • Matrix.vecMulVec (v j) (v j)
      let u' : ℝ := u0 + (k + 1 : ℕ) * deltaU
      let l' : ℝ := l0 + (k + 1 : ℕ) * deltaL
      have hs'_nonneg : ∀ j, 0 ≤ s' j := by
        intro j
        by_cases hji : j = i
        · subst j
          dsimp [s']
          simp [add_nonneg (hs_nonneg i) ht.le]
        · dsimp [s']
          rw [if_neg hji]
          simpa using hs_nonneg j
      have hsupport : Function.support s' ⊆ insert i (Function.support s) := by
        intro j hj
        by_cases hji : j = i
        · left
          exact hji
        · right
          have hs0 : s' j = s j := by
            dsimp [s']
            rw [if_neg hji, add_zero]
          change s' j ≠ 0 at hj
          rw [hs0] at hj
          exact hj
      have hcard : (Function.support s').ncard ≤ k + 1 := by
        calc
          (Function.support s').ncard ≤ (insert i (Function.support s)).ncard := by
            exact Set.ncard_mono hsupport
          _ ≤ (Function.support s).ncard + 1 := by
            exact Set.ncard_insert_le i (Function.support s)
          _ ≤ k + 1 := by
            exact Nat.add_le_add_right hs_card 1
      have hstep : ∑ j, (if j = i then t else 0) • Matrix.vecMulVec (v j) (v j) =
          t • Matrix.vecMulVec (v i) (v i) := by
        classical
        calc
          ∑ j, (if j = i then t else 0) • Matrix.vecMulVec (v j) (v j)
              = ∑ j, (if j = i then t • Matrix.vecMulVec (v j) (v j) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                by_cases hji : j = i
                · simp [hji]
                · simp [hji]
          _ = t • Matrix.vecMulVec (v i) (v i) := by
                rw [Finset.sum_ite_eq' (Finset.univ : Finset I) i
                  (fun j => t • Matrix.vecMulVec (v j) (v j))]
                simp
      have hA' : A' = A + t • Matrix.vecMulVec (v i) (v i) := by
        dsimp [A', s']
        calc
          ∑ j, (s j + (if j = i then t else 0)) • Matrix.vecMulVec (v j) (v j)
              = ∑ j, (s j • Matrix.vecMulVec (v j) (v j) +
                  (if j = i then t else 0) • Matrix.vecMulVec (v j) (v j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [add_smul]
          _ = ∑ j, s j • Matrix.vecMulVec (v j) (v j) +
              ∑ j, (if j = i then t else 0) • Matrix.vecMulVec (v j) (v j) := by
                rw [Finset.sum_add_distrib]
          _ = A + t • Matrix.vecMulVec (v i) (v i) := by
                rw [hstep]
      have hu' : u' = u + deltaU := by
        dsimp [u', u]
        push_cast
        ring
      have hl' : l' = l + deltaL := by
        dsimp [l', l]
        push_cast
        ring
      have hUnew : u' • (1 : Matrix n n ℝ) - A' =
          MU + deltaU • (1 : Matrix n n ℝ) - t • Matrix.vecMulVec (v i) (v i) := by
        rw [hA', hu', add_smul]
        dsimp [MU]
        abel
      have hLnew : A' - l' • (1 : Matrix n n ℝ) =
          ML - deltaL • (1 : Matrix n n ℝ) + t • Matrix.vecMulVec (v i) (v i) := by
        rw [hA', hl', add_smul]
        dsimp [ML]
        abel
      have hUpos' : (u' • (1 : Matrix n n ℝ) - A').PosDef := by
        rw [hUnew]
        exact hUpos1
      have hUtr' : ((u' • (1 : Matrix n n ℝ) - A')⁻¹).trace ≤ epsU := by
        rw [hUnew]
        exact le_trans hUtr1 hUtr
      have hLpos' : (A' - l' • (1 : Matrix n n ℝ)).PosDef := by
        rw [hLnew]
        exact hLpos1
      have hLtr' : ((A' - l' • (1 : Matrix n n ℝ))⁻¹).trace ≤ epsL := by
        rw [hLnew]
        exact le_trans hLtr1 hLtr
      refine ⟨s', hs'_nonneg, hcard, ?_⟩
      change (u' • (1 : Matrix n n ℝ) - A').PosDef ∧
        ((u' • (1 : Matrix n n ℝ) - A')⁻¹).trace ≤ epsU ∧
        (A' - l' • (1 : Matrix n n ℝ)).PosDef ∧
        ((A' - l' • (1 : Matrix n n ℝ))⁻¹).trace ≤ epsL
      exact ⟨hUpos', hUtr', hLpos', hLtr'⟩

/-- **Integer-budget spectral sandwich.**  Let `v : I → n → ℝ` be a real
isotropic frame (`∑ i, v_i v_iᵀ = 1`) with `N = Fintype.card n`, let `a > 1`
be real, and let `q` be a natural number with `(q : ℝ) = N*a²`.

Then there are nonnegative weights `sFinal` with support at most `q` such that
the normalized weighted Gram matrix satisfies the Loewner sandwich

`1 ≤ ∑ i, sFinal i • v_i v_iᵀ ≤ ((a+1)²/(a-1)²) • 1`.

This is the exact quantitative specialization of the finite iteration with the BSS 2008
constants (Section 3.2): `δL = 1`, `epsL = 1/a`, `l0 = -(N*a)`,
`δU = (a+1)/(a-1)`, `epsU = (a-1)/(a*(a+1))`, `u0 = N*a*(a+1)/(a-1)`.
After `q` steps the lower barrier is `lq = N*a*(a-1) > 0`, the upper barrier is
`uq = N*a*(a+1)²/(a-1)`, and `uq/lq = (a+1)²/(a-1)²`; scaling the returned
weights by `1/lq` converts the strict positivity of the barrier differences
into the semi-definite Loewner inequalities. -/
theorem exists_nonneg_weights_spectral_sandwich_of_sq_budget [Nonempty n]
    (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (a : ℝ) (ha1 : 1 < a) (q : ℕ)
    (hq : (q : ℝ) = (Fintype.card n : ℝ) * a ^ 2) :
    ∃ sFinal : I → ℝ,
      (∀ i, 0 ≤ sFinal i) ∧
      (Function.support sFinal).ncard ≤ q ∧
      ((1 : Matrix n n ℝ) ≤
        ∑ i, sFinal i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, sFinal i • Matrix.vecMulVec (v i) (v i) ≤
        ((a + 1) ^ 2 / (a - 1) ^ 2) • (1 : Matrix n n ℝ)) := by
  classical
  let N : ℝ := Fintype.card n
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty n›)
  have ha_pos : 0 < a := lt_trans (by norm_num) ha1
  have ha_sub_pos : 0 < a - 1 := sub_pos.mpr ha1
  have ha_add_pos : 0 < a + 1 := by linarith
  have ha_ne0 : a ≠ 0 := ne_of_gt ha_pos
  let deltaL : ℝ := 1
  let epsL : ℝ := 1 / a
  let l0 : ℝ := -(N * a)
  let deltaU : ℝ := (a + 1) / (a - 1)
  let epsU : ℝ := (a - 1) / (a * (a + 1))
  let u0 : ℝ := N * a * (a + 1) / (a - 1)
  have hu0 : 0 < u0 := by
    dsimp [u0]
    exact div_pos (mul_pos (mul_pos hNpos ha_pos) ha_add_pos) ha_sub_pos
  have hl0 : l0 < 0 := by
    dsimp [l0]
    rw [neg_lt_zero]
    exact mul_pos hNpos ha_pos
  have hδL : 0 < deltaL := by
    dsimp [deltaL]
    norm_num
  have hδU : 0 < deltaU := by
    dsimp [deltaU]
    exact div_pos ha_add_pos ha_sub_pos
  have hU0e : N / u0 = epsU := by
    dsimp [u0, epsU]
    field_simp [hNpos.ne', ha_ne0, ha_add_pos.ne', ha_sub_pos.ne']
  have hL0e : N / (-l0) = epsL := by
    dsimp [l0, epsL]
    field_simp [hNpos.ne', ha_ne0]
  have hcap0 : deltaL * epsL < 1 := by
    dsimp [deltaL, epsL]
    rw [one_mul]
    exact (div_lt_one ha_pos).mpr ha1
  have hpot0e : 1 / deltaU + epsU = 1 / deltaL - epsL := by
    dsimp [deltaU, epsU, deltaL, epsL]
    field_simp [ha_ne0, ha_add_pos.ne', ha_sub_pos.ne']
  obtain ⟨s, hs_nonneg, hs_card, hs_barriers⟩ :=
    exists_weights_barriers_of_potential_bounds (I := I) (n := n) v hframe
      u0 l0 deltaU deltaL epsU epsL hu0 hl0 hδU hδL
      (le_of_eq hU0e) (le_of_eq hL0e) hcap0 (le_of_eq hpot0e) q
  let A : Matrix n n ℝ := ∑ i, s i • Matrix.vecMulVec (v i) (v i)
  let u : ℝ := u0 + (q : ℝ) * deltaU
  let l : ℝ := l0 + (q : ℝ) * deltaL
  have hu_pos : (u • (1 : Matrix n n ℝ) - A).PosDef := by
    simpa [A, u] using hs_barriers.1
  have hl_pos : (A - l • (1 : Matrix n n ℝ)).PosDef := by
    simpa [A, l] using hs_barriers.2.2.1
  have hlq : l = N * a * (a - 1) := by
    dsimp [l, l0, deltaL, N]
    rw [hq]
    ring
  have huq : u = N * a * (a + 1) ^ 2 / (a - 1) := by
    dsimp [u, u0, deltaU, N]
    rw [hq]
    field_simp [ha_sub_pos.ne', ha_add_pos.ne', ha_ne0, hNpos.ne']
    ring_nf
  have hlq_pos : 0 < l := by
    rw [hlq]
    exact mul_pos (mul_pos hNpos ha_pos) ha_sub_pos
  have hl_psd : (A - l • (1 : Matrix n n ℝ)).PosSemidef := hl_pos.posSemidef
  have hu_psd : (u • (1 : Matrix n n ℝ) - A).PosSemidef := hu_pos.posSemidef
  have hsc_l : (1 / l) • (A - l • (1 : Matrix n n ℝ)) =
      (1 / l) • A - (1 : Matrix n n ℝ) := by
    rw [smul_sub, smul_smul]
    rw [one_div_mul_cancel (ne_of_gt hlq_pos), one_smul]
  have hl_scaled : ((1 / l) • A - (1 : Matrix n n ℝ)).PosSemidef := by
    rw [← hsc_l]
    exact Matrix.PosSemidef.smul hl_psd (le_of_lt (div_pos zero_lt_one hlq_pos))
  have hLower : (1 : Matrix n n ℝ) ≤ (1 / l) • A := by
    rw [Matrix.le_iff]
    simpa using hl_scaled
  have hsc_u : (1 / l) • (u • (1 : Matrix n n ℝ) - A) =
      (u / l) • (1 : Matrix n n ℝ) - (1 / l) • A := by
    rw [smul_sub]
    congr 1
    rw [smul_smul]
    ring
  have hu_scaled : ((u / l) • (1 : Matrix n n ℝ) - (1 / l) • A).PosSemidef := by
    rw [← hsc_u]
    exact Matrix.PosSemidef.smul hu_psd (le_of_lt (div_pos zero_lt_one hlq_pos))
  have hratio : u / l = (a + 1) ^ 2 / (a - 1) ^ 2 := by
    rw [huq, hlq]
    field_simp [ha_sub_pos.ne', ha_add_pos.ne', ha_ne0, hNpos.ne']
  have hUpper : (1 / l) • A ≤
      ((a + 1) ^ 2 / (a - 1) ^ 2) • (1 : Matrix n n ℝ) := by
    rw [Matrix.le_iff]
    simpa [hratio] using hu_scaled
  let sFinal : I → ℝ := fun i => (1 / l) * s i
  have hsFinal_nonneg : ∀ i, 0 ≤ sFinal i := by
    intro i
    dsimp [sFinal]
    exact mul_nonneg (le_of_lt (div_pos zero_lt_one hlq_pos)) (hs_nonneg i)
  have hsupp : Function.support sFinal ⊆ Function.support s := by
    intro i hi
    change (1 / l) * s i ≠ 0 at hi
    exact fun hzero => hi (by rw [hzero, mul_zero])
  have hcardFinal : (Function.support sFinal).ncard ≤ q := by
    exact le_trans (Set.ncard_mono hsupp) hs_card
  have hASum : ∑ i, sFinal i • Matrix.vecMulVec (v i) (v i) =
      (1 / l) • A := by
    dsimp [sFinal, A]
    simp [Finset.smul_sum, smul_smul]
  have hLowerFinal : (1 : Matrix n n ℝ) ≤
      ∑ i, sFinal i • Matrix.vecMulVec (v i) (v i) := by
    rw [hASum]
    exact hLower
  have hUpperFinal : ∑ i, sFinal i • Matrix.vecMulVec (v i) (v i) ≤
      ((a + 1) ^ 2 / (a - 1) ^ 2) • (1 : Matrix n n ℝ) := by
    rw [hASum]
    exact hUpper
  exact ⟨sFinal, hsFinal_nonneg, hcardFinal, hLowerFinal, hUpperFinal⟩

end RankOneBarrier
end NLAlib
