/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Krylov.Processes.Lanczos
/-!
# The three-term Lanczos recursion as an algorithm

The Lanczos *decomposition* is the predicate-level object `LanczosDecomp` (`NLAlib.Krylov.Processes.Arnoldi`,
`NLAlib.Krylov.Processes.Lanczos`) with canonical witness `arnoldiDecomp` / `arnoldiBasis`; this file adds
the *algorithm*, the three-term recursion of Trefethen–Bau Alg. 36.1, as a total recursion on a
state `(q_{j−1}, q_j, β_j)` (`docs/ALGORITHM_CONVENTIONS.md` §1, `docs/KRYLOV_DEFINITIONS.md` §3.6):

```
q_0 = b/‖b‖,  β_0 = 0,  q_{−1} = 0,
α_j = q_jᵀ A q_j,  w_j = A q_j − α_j q_j − β_j q_{j−1},  β_{j+1} = ‖w_j‖,  q_{j+1} = w_j / β_{j+1}.
```

Indexing is 0-based and matches `LanczosDecomp.alpha/beta`: `A q_j = β_j q_{j−1} + α_j q_j +
β_{j+1} q_{j+1}`. Lean's `x / 0 = 0` keeps the recursion total: at breakdown `w = 0`, so
`β = 0` and `q = 0`, and every later vector and coefficient is `0` — exactly the zero columns of
`arnoldiBasis` past the grade.

## Main declarations

* `LanczosState`, `lanczosStep`, `lanczosInit`, `lanczosState`, and the outputs
  `lanczosRecurrence A b j = q_j`, `lanczosAlpha A b j = α_j`, `lanczosBeta A b j = β_j`.
* Hypothesis-free (proved): the three-term relation `lanczosBeta_add_two_smul`
  (`β_{j+2} q_{j+2} = A q_{j+1} − α_{j+1} q_{j+1} − β_{j+1} q_j`) and its `j = 0` form.
* The realisation theorem `lanczosRecurrence_eq_arnoldiBasis`: for symmetric `A`,
  `q_j = arnoldiBasis A b j` for every `j` (positive-`β` sign convention, verified below).
* Consequences (proved from it): `lanczosBeta_succ_eq_dotProduct`, `lanczosBeta_pos`,
  `lanczosBeta_eq_zero_of_krylovGrade_le` (`β` vanishes exactly from the grade on),
  `lanczosAlpha_eq_alpha`, `lanczosBeta_eq_beta` (the coefficients are those of the canonical
  `LanczosDecomp`), `isGradedKrylovBasis_lanczosRecurrence`.

Source: Lanczos (1950); Trefethen–Bau (1997) [`tb97`], Alg. 36.1; Saad (2011) [`saad11`],
Alg. 6.15; Golub–Meurant (2010) [`gm10`], §4.1. Atlas: `lanczos-recurrence-algorithm`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-- The state of the Lanczos recursion at step `j`: the previous vector `q_{j−1}` (`0` for
`j = 0`), the current vector `q_j`, and the coefficient `β_j` linking them (`β_0 = 0`).
Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
structure LanczosState (n : Type*) where
  /-- The previous Lanczos vector `q_{j−1}`. -/
  prev : n → ℝ
  /-- The current Lanczos vector `q_j`. -/
  cur : n → ℝ
  /-- The coefficient `β_j = ‖w_{j−1}‖` (`= q_jᵀ A q_{j−1}` in exact arithmetic for symmetric
  `A`, `lanczosBeta_succ_eq_dotProduct`). -/
  beta : ℝ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One Lanczos step: `w = A q_j − α_j q_j − β_j q_{j−1}` with `α_j = q_jᵀ A q_j`, then
`β_{j+1} = ‖w‖` and `q_{j+1} = β_{j+1}⁻¹ w` (`0` at breakdown, since `0⁻¹ = 0`).
Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1; Saad (2011) [`saad11`], Alg. 6.15.
Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosStep (A : Matrix n n ℝ) (s : LanczosState n) : LanczosState n :=
  let w := A *ᵥ s.cur - (s.cur ⬝ᵥ (A *ᵥ s.cur)) • s.cur - s.beta • s.prev
  ⟨s.cur, ‖WithLp.toLp 2 w‖⁻¹ • w, ‖WithLp.toLp 2 w‖⟩

/-- The initial state `(0, b/‖b‖, 0)` (`q_0 = 0` when `b = 0`). Source: Trefethen–Bau (1997)
[`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosInit (b : n → ℝ) : LanczosState n :=
  ⟨0, ‖WithLp.toLp 2 b‖⁻¹ • b, 0⟩

/-- The state after `j` Lanczos steps, as `Nat.iterate`. Source: Trefethen–Bau (1997)
[`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosState (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : LanczosState n :=
  (lanczosStep A)^[j] (lanczosInit b)

/-- The **Lanczos vectors** `q_j` of the three-term recursion (0-based). For symmetric `A` they
are the Arnoldi vectors (`lanczosRecurrence_eq_arnoldiBasis`). Source: Trefethen–Bau (1997)
[`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosRecurrence (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : n → ℝ :=
  (lanczosState A b j).cur

/-- The recursion's diagonal coefficient `α_j = q_jᵀ A q_j`. Source: Trefethen–Bau (1997)
[`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosAlpha (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : ℝ :=
  lanczosRecurrence A b j ⬝ᵥ (A *ᵥ lanczosRecurrence A b j)

/-- The recursion's off-diagonal coefficient `β_j = ‖w_{j−1}‖` (`β_0 = 0`), the same indexing
as `LanczosDecomp.beta`. Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1.
Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosBeta (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : ℝ :=
  (lanczosState A b j).beta

omit [DecidableEq n] in
/-- The recursion starts at `lanczosInit b`. Atlas: `lanczos-recurrence-algorithm`. -/
@[simp] theorem lanczosState_zero (A : Matrix n n ℝ) (b : n → ℝ) :
    lanczosState A b 0 = lanczosInit b := rfl

omit [DecidableEq n] in
/-- One more step of the recursion. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosState_succ (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    lanczosState A b (j + 1) = lanczosStep A (lanczosState A b j) :=
  Function.iterate_succ_apply' _ _ _

omit [DecidableEq n] in
/-- `q_0 = b/‖b‖`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosRecurrence_zero (A : Matrix n n ℝ) (b : n → ℝ) :
    lanczosRecurrence A b 0 = ‖WithLp.toLp 2 b‖⁻¹ • b := rfl

omit [DecidableEq n] in
/-- `β_0 = 0`. Atlas: `lanczos-recurrence-algorithm`. -/
@[simp] theorem lanczosBeta_zero (A : Matrix n n ℝ) (b : n → ℝ) : lanczosBeta A b 0 = 0 := rfl

omit [DecidableEq n] in
/-- The state at step `j + 1` remembers `q_j`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosState_succ_prev (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    (lanczosState A b (j + 1)).prev = lanczosRecurrence A b j := by
  rw [lanczosState_succ]; rfl

omit [DecidableEq n] in
/-- `β_j = ‖w_{j−1}‖ ≥ 0`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosBeta_nonneg (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : 0 ≤ lanczosBeta A b j := by
  cases j with
  | zero => exact le_rfl
  | succ j => rw [lanczosBeta, lanczosState_succ]; exact norm_nonneg _

omit [DecidableEq n] in
/-- `‖w‖ • (‖w‖⁻¹ • w) = w`, including `w = 0`. -/
private lemma sqrt_smul_inv_smul (w : n → ℝ) : √(w ⬝ᵥ w) • ((√(w ⬝ᵥ w))⁻¹ • w) = w := by
  by_cases h : √(w ⬝ᵥ w) = 0
  · have hw : w ⬝ᵥ w = 0 := by
      have := Real.sqrt_eq_zero'.1 h
      exact le_antisymm this (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    rw [dotProduct_self_eq_zero.1 hw]; simp
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

omit [DecidableEq n] in
/-- `‖w‖⁻¹ wᵀ w = ‖w‖`. -/
private lemma inv_sqrt_mul_self (w : n → ℝ) : (√(w ⬝ᵥ w))⁻¹ * (w ⬝ᵥ w) = √(w ⬝ᵥ w) := by
  have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set s := √(w ⬝ᵥ w) with hs
  have hw : w ⬝ᵥ w = s * s := (Real.mul_self_sqrt h0).symm
  rw [hw]
  by_cases h : s = 0
  · rw [h, mul_zero, mul_zero]
  · field_simp

omit [DecidableEq n] in
/-- **First step of the recursion**: `β_1 q_1 = A q_0 − α_0 q_0`. No hypothesis on `A`.
Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosBeta_one_smul (A : Matrix n n ℝ) (b : n → ℝ) :
    lanczosBeta A b 1 • lanczosRecurrence A b 1 =
      A *ᵥ lanczosRecurrence A b 0 - lanczosAlpha A b 0 • lanczosRecurrence A b 0 := by
  simp only [lanczosBeta, lanczosRecurrence, lanczosAlpha, lanczosState_succ, lanczosStep,
    norm_toLp_eq_sqrt_dotProduct_self]
  rw [sqrt_smul_inv_smul]
  simp [lanczosInit]

omit [DecidableEq n] in
/-- **The three-term relation of the recursion**: `β_{j+2} q_{j+2} = A q_{j+1} − α_{j+1} q_{j+1}
− β_{j+1} q_j`, i.e. `A q_{j+1} = β_{j+1} q_j + α_{j+1} q_{j+1} + β_{j+2} q_{j+2}`. No hypothesis on
`A` (it is how the recursion is built). Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1 and
eq. (36.3). Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosBeta_add_two_smul (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    lanczosBeta A b (j + 2) • lanczosRecurrence A b (j + 2) =
      A *ᵥ lanczosRecurrence A b (j + 1) - lanczosAlpha A b (j + 1) • lanczosRecurrence A b (j + 1)
        - lanczosBeta A b (j + 1) • lanczosRecurrence A b j := by
  have hp := lanczosState_succ_prev A b j
  simp only [lanczosBeta, lanczosRecurrence, lanczosAlpha] at hp ⊢
  rw [lanczosState_succ A b (j + 1)]
  simp only [lanczosStep, norm_toLp_eq_sqrt_dotProduct_self]
  rw [sqrt_smul_inv_smul, hp]

omit [DecidableEq n] in
/-- The recursion's `β_{j+1}` is `q_{j+1}ᵀ w_j`, with `w_j = A q_j − α_j q_j − β_j q_{j−1}`
(`q_{−1} = 0`). No hypothesis on `A`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosBeta_succ_eq (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    lanczosBeta A b (j + 1) = lanczosRecurrence A b (j + 1) ⬝ᵥ
      (A *ᵥ lanczosRecurrence A b j - lanczosAlpha A b j • lanczosRecurrence A b j -
        lanczosBeta A b j • (lanczosState A b j).prev) := by
  simp only [lanczosBeta, lanczosRecurrence, lanczosAlpha, lanczosState_succ A b j, lanczosStep,
    norm_toLp_eq_sqrt_dotProduct_self]
  rw [smul_dotProduct, smul_eq_mul, inv_sqrt_mul_self]

/-! ### Realisation: the recursion is the Arnoldi process (symmetric `A`) -/

/-
The canonical-state and normalization argument below is adapted from
NLA-lib/NLAlib, NLAlib/Krylov/Processes/LanczosRecurrence.lean, commit
6a845a2ec27f37c1a98118c107a06a13ce45273d (Apache-2.0).
The backend uses the direct coefficient `qᵀ A q`, so the proof works with its
existing canonical decomposition rather than changing the recursion to Paige's form.
-/

open LanczosDecomp

/-- At the grade the last three-term relation closes; after the grade it is zero. -/
private theorem lanczosDecomp_mulVec_vec_eq {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}
    (D : LanczosDecomp A b q) (hA : A.IsHermitian) (hq : krylovGrade A b ≤ q) (j : ℕ) :
    A *ᵥ D.vec j =
      D.beta j • D.vec (j - 1) + D.alpha j • D.vec j +
        D.beta (j + 1) • D.vec (j + 1) := by
  by_cases hj : j < q
  · by_cases hj' : j + 1 < q
    · exact D.mulVec_vec_eq hA hj'
    have hlast : j + 1 = q := by omega
    have hmemA : A *ᵥ D.vec j ∈ krylovSpace A b q := by
      rw [krylovSpace_eq_of_krylovGrade_le A b hq]
      exact mulVec_mem_krylovSpace_krylovGrade A b
        (krylovSpace_le_krylovSpace_krylovGrade A b q (D.vec_mem j))
    have hmemR : D.beta j • D.vec (j - 1) + D.alpha j • D.vec j +
        D.beta (j + 1) • D.vec (j + 1) ∈ krylovSpace A b q :=
      Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (D.vec_mem _))
        (Submodule.smul_mem _ _ (D.vec_mem _))) (Submodule.smul_mem _ _ (D.vec_mem _))
    have hS : (ArnoldiDecomp.H D).IsSymm := D.isSymm_T hA
    refine D.eq_of_forall_col_dotProduct_eq hmemA hmemR fun i => ?_
    rw [D.vec_of_lt hj, ← ArnoldiDecomp.H_apply]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,
      ← D.vec_of_lt hj, LanczosDecomp.col_dotProduct_vec,
      LanczosDecomp.alpha, LanczosDecomp.beta, dif_pos hj,
      dif_neg (show ¬(0 < j + 1 ∧ j + 1 < q) by omega), zero_mul, add_zero]
    rcases eq_or_ne (i : ℕ) j with hi | hi
    · have hif : i = ⟨j, hj⟩ := Fin.ext hi
      rw [hif]
      simp only [if_true, mul_one]
      by_cases hj0 : 0 < j
      · simp only [dif_pos (show 0 < j ∧ j < q from ⟨hj0, hj⟩), show j ≠ j - 1 by omega, if_false, mul_zero,
          zero_add]
      · simp only [dif_neg (show ¬(0 < j ∧ j < q) by omega), zero_mul, zero_add]
    · simp only [if_neg hi, mul_zero, add_zero]
      by_cases hprev : (i : ℕ) = j - 1
      · have hj0 : 0 < j := by have := i.isLt; omega
        have hif : i = ⟨j - 1, by omega⟩ := Fin.ext hprev
        rw [hif]
        simp only [dif_pos (show 0 < j ∧ j < q from ⟨hj0, hj⟩), if_true, mul_one]
        exact (hS.apply _ _).symm
      · rw [if_neg hprev, mul_zero]
        rw [← hS.apply i ⟨j, hj⟩]
        exact D.H_apply_eq_zero_of_add_one_lt (i := ⟨j, hj⟩) (j := i)
          (show (i : ℕ) + 1 < j by have := i.isLt; omega)
  · simp [LanczosDecomp.vec, LanczosDecomp.alpha, LanczosDecomp.beta, hj,
      show ¬j + 1 < q by omega]

private def lanczosCanonicalPrev {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}
    (D : LanczosDecomp A b q) : ℕ → n → ℝ
  | 0 => 0
  | j + 1 => D.vec j

private def lanczosCanonicalState (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : LanczosState n :=
  let D : LanczosDecomp A b (krylovGrade A b) :=
    arnoldiDecomp A b (krylovGrade A b) le_rfl
  ⟨lanczosCanonicalPrev D j, D.vec j, D.beta j⟩

private theorem lanczosCanonicalState_cur (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    (lanczosCanonicalState A b j).cur = arnoldiBasis A b j := by
  by_cases hj : j < krylovGrade A b
  · simp only [lanczosCanonicalState, LanczosDecomp.vec_of_lt _ hj,
      arnoldiDecomp_Q, arnoldiMatrix_col]
  · simp [lanczosCanonicalState, LanczosDecomp.vec, hj,
      arnoldiBasis_eq_zero_of_krylovGrade_le A b (not_lt.mp hj)]

omit [DecidableEq n] in
/-- Normalizing a nonnegative multiple of a canonical unit or zero vector. -/
private theorem lanczos_norm_smul_and_inv_smul {c : ℝ} (hc : 0 ≤ c) {v : n → ℝ}
    (h0 : c = 0 → v = 0) (h1 : c ≠ 0 → ‖WithLp.toLp 2 v‖ = 1) :
    ‖WithLp.toLp 2 (c • v)‖ = c ∧ ‖WithLp.toLp 2 (c • v)‖⁻¹ • (c • v) = v := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [h0 rfl]
    simp
  · have hn : ‖WithLp.toLp 2 (c • v)‖ = c := by
      rw [WithLp.toLp_smul, norm_smul, h1 hc0, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hc]
    refine ⟨hn, ?_⟩
    rw [hn, smul_smul, inv_mul_cancel₀ hc0, one_smul]

private theorem lanczosStep_lanczosCanonicalState {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (b : n → ℝ) (j : ℕ) :
    lanczosStep A (lanczosCanonicalState A b j) = lanczosCanonicalState A b (j + 1) := by
  let D : LanczosDecomp A b (krylovGrade A b) :=
    arnoldiDecomp A b (krylovGrade A b) le_rfl
  have halpha : D.vec j ⬝ᵥ (A *ᵥ D.vec j) = D.alpha j := by
    by_cases hj : j < krylovGrade A b
    · rw [D.vec_of_lt hj, LanczosDecomp.alpha, dif_pos hj, LanczosDecomp.T, ArnoldiDecomp.H_apply]
    · simp [LanczosDecomp.vec, LanczosDecomp.alpha, hj]
  have hw : A *ᵥ (lanczosCanonicalState A b j).cur -
      ((lanczosCanonicalState A b j).cur ⬝ᵥ (A *ᵥ (lanczosCanonicalState A b j).cur)) •
        (lanczosCanonicalState A b j).cur -
      (lanczosCanonicalState A b j).beta • (lanczosCanonicalState A b j).prev =
        D.beta (j + 1) • D.vec (j + 1) := by
    change A *ᵥ D.vec j - (D.vec j ⬝ᵥ (A *ᵥ D.vec j)) • D.vec j -
      D.beta j • lanczosCanonicalPrev D j = _
    rw [halpha, lanczosDecomp_mulVec_vec_eq D hA le_rfl]
    cases j with
    | zero => simp [lanczosCanonicalPrev, LanczosDecomp.beta]
    | succ j => simp only [lanczosCanonicalPrev, Nat.add_sub_cancel]; abel
  have hc : 0 ≤ D.beta (j + 1) := by
    by_cases hj : j + 1 < krylovGrade A b
    · exact (LanczosDecomp.beta_arnoldiDecomp_pos A b le_rfl (by omega) hj).le
    · simp [LanczosDecomp.beta, hj]
  have hc0 : D.beta (j + 1) = 0 → D.vec (j + 1) = 0 := by
    intro h
    by_cases hj : j + 1 < krylovGrade A b
    · exact False.elim ((LanczosDecomp.beta_arnoldiDecomp_pos A b le_rfl
        (by omega) hj).ne' h)
    · simp [LanczosDecomp.vec, hj]
  have hc1 : D.beta (j + 1) ≠ 0 → ‖WithLp.toLp 2 (D.vec (j + 1))‖ = 1 := by
    intro h
    have hj : j + 1 < krylovGrade A b := by
      by_contra hj
      exact h (by simp [LanczosDecomp.beta, hj])
    rw [norm_toLp_eq_sqrt_dotProduct_self, D.vec_of_lt hj,
      D.hasOrthonormalCols.col_dotProduct_col, if_pos rfl, Real.sqrt_one]
  obtain ⟨hn, hv⟩ := lanczos_norm_smul_and_inv_smul hc hc0 hc1
  unfold lanczosStep
  rw [hw]
  dsimp only
  rw [hv, hn]
  rfl

private theorem lanczosState_eq_lanczosCanonicalState {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (b : n → ℝ) (j : ℕ) :
    lanczosState A b j = lanczosCanonicalState A b j := by
  induction j with
  | zero =>
    have hcur : (lanczosCanonicalState A b 0).cur = ‖WithLp.toLp 2 b‖⁻¹ • b := by
      rw [lanczosCanonicalState_cur, arnoldiBasis, InnerProductSpace.gramSchmidtNormed]
      have hg : InnerProductSpace.gramSchmidt ℝ (krylovSeq A b) 0 =
          WithLp.toLp 2 b := by
        simpa only [Nat.bot_eq_zero, krylovSeq, pow_zero, Matrix.one_mulVec] using
          (InnerProductSpace.gramSchmidt_bot ℝ (krylovSeq A b))
      rw [hg]
      simp [WithLp.ofLp_smul]
    change lanczosInit b = lanczosCanonicalState A b 0
    cases h : lanczosCanonicalState A b 0 with
    | mk p c beta =>
      have hp : p = 0 := by simpa [lanczosCanonicalState, lanczosCanonicalPrev] using congrArg LanczosState.prev h.symm
      have hb : beta = 0 := by
        simpa [lanczosCanonicalState, LanczosDecomp.beta] using congrArg LanczosState.beta h.symm
      simp only [h] at hcur
      simp [lanczosInit, hp, hb, hcur]
  | succ j ih =>
    rw [lanczosState_succ, ih, lanczosStep_lanczosCanonicalState hA]

/-- **The three-term recursion is the Arnoldi process**: for symmetric `A`, the actual
Trefethen–Bau recursion equals the positively normalized canonical Arnoldi basis for every step,
including breakdown and every later zero vector. The canonical-state proof is adapted from
NLA-lib/NLAlib commit `6a845a2ec27f37c1a98118c107a06a13ce45273d` (Apache-2.0), preserving this
library's direct Rayleigh coefficient `qᵀ A q`.
Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1; Saad (2011) [`saad11`], Alg. 6.15;
Golub–Meurant (2010) [`gm10`], Thm 4.2. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosRecurrence_eq_arnoldiBasis {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ)
    (j : ℕ) : lanczosRecurrence A b j = arnoldiBasis A b j := by
  rw [lanczosRecurrence, lanczosState_eq_lanczosCanonicalState hA,
    lanczosCanonicalState_cur]


/-- **The recursion's `β` is the subdiagonal of the Arnoldi matrix**: for symmetric `A` and every
`j`, `β_{j+1} = q_{j+1}ᵀ A q_j` with `q = arnoldiBasis A b`. Proof: `lanczosBeta_succ_eq`,
`lanczosRecurrence_eq_arnoldiBasis` and orthogonality (`arnoldiBasis_dotProduct_of_ne`).
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36. Atlas: `lanczos-recurrence-algorithm`
(partial). -/
theorem lanczosBeta_succ_eq_dotProduct {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ)
    (j : ℕ) : lanczosBeta A b (j + 1) = arnoldiBasis A b (j + 1) ⬝ᵥ (A *ᵥ arnoldiBasis A b j) := by
  have hprev : arnoldiBasis A b (j + 1) ⬝ᵥ (lanczosState A b j).prev = 0 := by
    cases j with
    | zero => simp [lanczosInit]
    | succ j =>
      rw [lanczosState_succ_prev, lanczosRecurrence_eq_arnoldiBasis hA]
      exact arnoldiBasis_dotProduct_of_ne A b (by omega)
  rw [lanczosBeta_succ_eq, lanczosRecurrence_eq_arnoldiBasis hA,
    lanczosRecurrence_eq_arnoldiBasis hA, dotProduct_sub, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, hprev, arnoldiBasis_dotProduct_of_ne A b (by omega)]
  simp

/-- **`β` is positive below the grade**: for symmetric `A`, `0 < β_j` for `0 < j < ν(A, b)`.
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Golub–Meurant (2010) [`gm10`], Alg. 4.1.
Proof: `lanczosBeta_succ_eq_dotProduct` and `arnoldiDecomp_H_subdiag_pos`.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosBeta_pos {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {j : ℕ} (h0 : 0 < j)
    (hj : j < krylovGrade A b) : 0 < lanczosBeta A b j := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [lanczosBeta_succ_eq_dotProduct hA]
  have h := arnoldiDecomp_H_subdiag_pos A b (q := j + 2) (by omega) (j := j) (by omega)
  rwa [ArnoldiDecomp.H_apply] at h

/-- **`β` vanishes from the grade on**: for symmetric `A`, `β_j = 0` for `j ≥ ν(A, b)`; with
`lanczosBeta_pos`, the recursion breaks down (`β = 0`) exactly at the grade.
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Saad (2003) [`saad03`], Prop. 6.6.
Proof: `lanczosBeta_succ_eq_dotProduct` and `arnoldiBasis_eq_zero_of_krylovGrade_le`.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosBeta_eq_zero_of_krylovGrade_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ)
    {j : ℕ} (hj : krylovGrade A b ≤ j) : lanczosBeta A b j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [lanczosBeta_succ_eq_dotProduct hA, arnoldiBasis_eq_zero_of_krylovGrade_le A b hj,
      zero_dotProduct]

/-- **Breakdown characterisation**: for symmetric `A` and `j > 0`, `β_j = 0 ↔ ν(A, b) ≤ j`.
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Saad (2003) [`saad03`], Prop. 6.6.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosBeta_eq_zero_iff {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {j : ℕ}
    (h0 : 0 < j) : lanczosBeta A b j = 0 ↔ krylovGrade A b ≤ j := by
  refine ⟨fun h => ?_, lanczosBeta_eq_zero_of_krylovGrade_le hA b⟩
  by_contra hlt
  exact (lanczosBeta_pos hA b h0 (not_le.1 hlt)).ne' h

/-- The recursion's vectors vanish from the grade on: `q_j = 0` for `j ≥ ν(A, b)` (symmetric `A`).
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosRecurrence_eq_zero_of_krylovGrade_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : n → ℝ) {j : ℕ} (hj : krylovGrade A b ≤ j) : lanczosRecurrence A b j = 0 := by
  rw [lanczosRecurrence_eq_arnoldiBasis hA, arnoldiBasis_eq_zero_of_krylovGrade_le A b hj]

/-- **The recursion's `α` are the diagonal of the canonical Jacobi matrix**: for symmetric `A`,
`q ≤ ν(A, b)` and `j < q`, `α_j = (arnoldiDecomp A b q h).alpha j`. Source: Trefethen–Bau (1997)
[`tb97`], Lect. 36; Golub–Meurant (2010) [`gm10`], Alg. 4.1.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosAlpha_eq_alpha {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {q : ℕ}
    (h : q ≤ krylovGrade A b) {j : ℕ} (hj : j < q) :
    lanczosAlpha A b j = LanczosDecomp.alpha (arnoldiDecomp A b q h) j := by
  rw [LanczosDecomp.alpha, dif_pos hj, LanczosDecomp.T, ArnoldiDecomp.H_apply, arnoldiDecomp_Q,
    arnoldiMatrix_col, lanczosAlpha, lanczosRecurrence_eq_arnoldiBasis hA]

/-- **The recursion's `β` are the off-diagonal of the canonical Jacobi matrix**: for symmetric
`A`, `q ≤ ν(A, b)` and `j < q`, `β_j = (arnoldiDecomp A b q h).beta j` (both `0` at `j = 0`).
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Golub–Meurant (2010) [`gm10`], Alg. 4.1.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosBeta_eq_beta {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {q : ℕ}
    (h : q ≤ krylovGrade A b) {j : ℕ} (hj : j < q) :
    lanczosBeta A b j = LanczosDecomp.beta (arnoldiDecomp A b q h) j := by
  cases j with
  | zero => simp [LanczosDecomp.beta]
  | succ j =>
    rw [LanczosDecomp.beta, dif_pos ⟨Nat.succ_pos j, hj⟩, LanczosDecomp.T, ArnoldiDecomp.H_apply,
      arnoldiDecomp_Q, arnoldiMatrix_col, arnoldiMatrix_col, lanczosBeta_succ_eq_dotProduct hA]
    rfl

/-- **The recursion produces a graded Krylov basis**: for symmetric `A` and `q ≤ ν(A, b)`, the
matrix with columns `q_0, …, q_{q−1}` of the recursion is a graded orthonormal Krylov basis (it
is `arnoldiMatrix A b q`). Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Saad (2011)
[`saad11`], Prop. 6.14. Uses atlas `graded-krylov-basis-def`.
atlas: lanczos-recurrence-algorithm -/
theorem isGradedKrylovBasis_lanczosRecurrence {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ)
    {q : ℕ} (h : q ≤ krylovGrade A b) :
    IsGradedKrylovBasis A b (Matrix.of fun r (j : Fin q) => lanczosRecurrence A b j r) := by
  have hQ : (Matrix.of fun r (j : Fin q) => lanczosRecurrence A b j r) = arnoldiMatrix A b q := by
    ext r j
    simp [arnoldiMatrix, lanczosRecurrence_eq_arnoldiBasis hA]
  rw [hQ]
  exact (arnoldiDecomp A b q h).graded

end NLAlib
