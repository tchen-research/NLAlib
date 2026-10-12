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
* The realisation theorem (scaffold) `lanczosRecurrence_eq_arnoldiBasis`: for symmetric `A`,
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
  /-- The coefficient `β_j = q_jᵀ A q_{j−1}`. -/
  beta : ℝ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One Lanczos step: `w = A q_j − α_j q_j − β_j q_{j−1}` with `α_j = q_jᵀ A q_j`, then
`β_{j+1} = ‖w‖ = √(wᵀw)` and `q_{j+1} = β_{j+1}⁻¹ w` (`0` at breakdown, since `0⁻¹ = 0`).
Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1; Saad (2011) [`saad11`], Alg. 6.15.
Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosStep (A : Matrix n n ℝ) (s : LanczosState n) : LanczosState n :=
  let w := A *ᵥ s.cur - (s.cur ⬝ᵥ (A *ᵥ s.cur)) • s.cur - s.beta • s.prev
  ⟨s.cur, (√(w ⬝ᵥ w))⁻¹ • w, √(w ⬝ᵥ w)⟩

/-- The initial state `(0, b/‖b‖, 0)` (`q_0 = 0` when `b = 0`). Source: Trefethen–Bau (1997)
[`tb97`], Alg. 36.1. Atlas: `lanczos-recurrence-algorithm`. -/
def lanczosInit (b : n → ℝ) : LanczosState n :=
  ⟨0, (√(b ⬝ᵥ b))⁻¹ • b, 0⟩

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
    lanczosRecurrence A b 0 = (√(b ⬝ᵥ b))⁻¹ • b := rfl

omit [DecidableEq n] in
/-- `β_0 = 0`. Atlas: `lanczos-recurrence-algorithm`. -/
@[simp] theorem lanczosBeta_zero (A : Matrix n n ℝ) (b : n → ℝ) : lanczosBeta A b 0 = 0 := rfl

omit [DecidableEq n] in
/-- The state at step `j + 1` remembers `q_j`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosState_succ_prev (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    (lanczosState A b (j + 1)).prev = lanczosRecurrence A b j := by
  rw [lanczosState_succ]; rfl

omit [DecidableEq n] in
/-- `β_j = √(wᵀw) ≥ 0`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosBeta_nonneg (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : 0 ≤ lanczosBeta A b j := by
  cases j with
  | zero => exact le_rfl
  | succ j => rw [lanczosBeta, lanczosState_succ]; exact Real.sqrt_nonneg _

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
  simp only [lanczosBeta, lanczosRecurrence, lanczosAlpha, lanczosState_succ, lanczosStep]
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
  simp only [lanczosStep]
  rw [sqrt_smul_inv_smul, hp]

omit [DecidableEq n] in
/-- The recursion's `β_{j+1}` is `q_{j+1}ᵀ w_j`, with `w_j = A q_j − α_j q_j − β_j q_{j−1}`
(`q_{−1} = 0`). No hypothesis on `A`. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosBeta_succ_eq (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    lanczosBeta A b (j + 1) = lanczosRecurrence A b (j + 1) ⬝ᵥ
      (A *ᵥ lanczosRecurrence A b j - lanczosAlpha A b j • lanczosRecurrence A b j -
        lanczosBeta A b j • (lanczosState A b j).prev) := by
  simp only [lanczosBeta, lanczosRecurrence, lanczosAlpha, lanczosState_succ A b j, lanczosStep]
  rw [smul_dotProduct, smul_eq_mul, inv_sqrt_mul_self]

/-! ### Realisation: the recursion is the Arnoldi process (symmetric `A`) -/

/-- SCAFFOLD: lanczos-recurrence-algorithm
**The three-term recursion is the Arnoldi process**: for symmetric `A`, `q_j = arnoldiBasis A b j`
for every `j` (below the grade the Gram–Schmidt vectors with positive `β`; from the grade on both
sides are `0`). Sign convention verified: the recursion has `q_0ᵀ b = ‖b‖ > 0` and
`q_{j+1}ᵀ A q_j = q_{j+1}ᵀ w_j = ‖w_j‖ ≥ 0` (`lanczosBeta_succ_eq`), the signs of the canonical
decomposition (`arnoldiBasis_zero_dotProduct_pos`, `arnoldiDecomp_H_subdiag_pos`).
Source: Trefethen–Bau (1997) [`tb97`], Alg. 36.1 and Lect. 36; Saad (2011) [`saad11`],
Alg. 6.15 and Prop. 6.14; Golub–Meurant (2010) [`gm10`], Thm 4.2.
Proof sketch: strong induction on `j`, carrying also `β_j = arnoldiBasis j ⬝ A arnoldiBasis (j−1)`.
Case `j + 1 < ν` (grade): apply `LanczosDecomp.mulVec_vec_eq` to `D = arnoldiDecomp A b (j + 2)`,
so `w_j = A q_j − α_j q_j − β_j q_{j−1} = β'_{j+1} q'_{j+1}` with `β'_{j+1} > 0`
(`beta_arnoldiDecomp_pos`) and `q'_{j+1}` a unit vector; hence `‖w_j‖ = β'_{j+1}` and
`q_{j+1} = q'_{j+1}`. Case `j + 1 = ν`: `A q_j ∈ K_ν` (`mulVec_mem_krylovSpace_krylovGrade`),
its coordinates in `arnoldiDecomp A b ν` are those of `α_j q_j + β_j q_{j−1}` (tridiagonality,
`T_apply_eq_zero_of_one_lt_dist`), so `w_j = 0` (`eq_of_forall_col_dotProduct_eq`) and
`q_ν = 0 = arnoldiBasis ν` (`arnoldiBasis_eq_zero_of_krylovGrade_le`). Case `j + 1 > ν`: the
state is `(0, 0, 0)` or `(q_{ν−1}, 0, 0)`, so `w_j = 0`. Base: `q_0 = b/‖b‖ = arnoldiBasis 0`
(`gramSchmidtNormed` of `b`). Uses atlas `lanczos-recurrence`, `graded-krylov-basis-def`. -/
theorem lanczosRecurrence_eq_arnoldiBasis {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ)
    (j : ℕ) : lanczosRecurrence A b j = arnoldiBasis A b j := by
  sorry

/-- **The recursion's `β` is the subdiagonal of the Arnoldi matrix**: for symmetric `A` and every
`j`, `β_{j+1} = q_{j+1}ᵀ A q_j` with `q = arnoldiBasis A b`. Proof: `lanczosBeta_succ_eq`,
`lanczosRecurrence_eq_arnoldiBasis` and orthogonality (`arnoldiBasis_dotProduct_of_ne`).
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36. Atlas: `lanczos-recurrence-algorithm`
(partial). -/
theorem lanczosBeta_succ_eq_dotProduct {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ)
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
theorem lanczosBeta_pos {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ) {j : ℕ} (h0 : 0 < j)
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
theorem lanczosBeta_eq_zero_of_krylovGrade_le {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ)
    {j : ℕ} (hj : krylovGrade A b ≤ j) : lanczosBeta A b j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [lanczosBeta_succ_eq_dotProduct hA, arnoldiBasis_eq_zero_of_krylovGrade_le A b hj,
      zero_dotProduct]

/-- **Breakdown characterisation**: for symmetric `A` and `j > 0`, `β_j = 0 ↔ ν(A, b) ≤ j`.
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Saad (2003) [`saad03`], Prop. 6.6.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosBeta_eq_zero_iff {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ) {j : ℕ}
    (h0 : 0 < j) : lanczosBeta A b j = 0 ↔ krylovGrade A b ≤ j := by
  refine ⟨fun h => ?_, lanczosBeta_eq_zero_of_krylovGrade_le hA b⟩
  by_contra hlt
  exact (lanczosBeta_pos hA b h0 (not_le.1 hlt)).ne' h

/-- The recursion's vectors vanish from the grade on: `q_j = 0` for `j ≥ ν(A, b)` (symmetric `A`).
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36. Atlas: `lanczos-recurrence-algorithm`. -/
theorem lanczosRecurrence_eq_zero_of_krylovGrade_le {A : Matrix n n ℝ} (hA : A.IsSymm)
    (b : n → ℝ) {j : ℕ} (hj : krylovGrade A b ≤ j) : lanczosRecurrence A b j = 0 := by
  rw [lanczosRecurrence_eq_arnoldiBasis hA, arnoldiBasis_eq_zero_of_krylovGrade_le A b hj]

/-- **The recursion's `α` are the diagonal of the canonical Jacobi matrix**: for symmetric `A`,
`q ≤ ν(A, b)` and `j < q`, `α_j = (arnoldiDecomp A b q h).alpha j`. Source: Trefethen–Bau (1997)
[`tb97`], Lect. 36; Golub–Meurant (2010) [`gm10`], Alg. 4.1.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosAlpha_eq_alpha {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ) {q : ℕ}
    (h : q ≤ krylovGrade A b) {j : ℕ} (hj : j < q) :
    lanczosAlpha A b j = LanczosDecomp.alpha (arnoldiDecomp A b q h) j := by
  rw [LanczosDecomp.alpha, dif_pos hj, LanczosDecomp.T, ArnoldiDecomp.H_apply, arnoldiDecomp_Q,
    arnoldiMatrix_col, lanczosAlpha, lanczosRecurrence_eq_arnoldiBasis hA]

/-- **The recursion's `β` are the off-diagonal of the canonical Jacobi matrix**: for symmetric
`A`, `q ≤ ν(A, b)` and `j < q`, `β_j = (arnoldiDecomp A b q h).beta j` (both `0` at `j = 0`).
Source: Trefethen–Bau (1997) [`tb97`], Lect. 36; Golub–Meurant (2010) [`gm10`], Alg. 4.1.
atlas: lanczos-recurrence-algorithm (partial) -/
theorem lanczosBeta_eq_beta {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ) {q : ℕ}
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
theorem isGradedKrylovBasis_lanczosRecurrence {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ)
    {q : ℕ} (h : q ≤ krylovGrade A b) :
    IsGradedKrylovBasis A b (Matrix.of fun r (j : Fin q) => lanczosRecurrence A b j r) := by
  have hQ : (Matrix.of fun r (j : Fin q) => lanczosRecurrence A b j r) = arnoldiMatrix A b q := by
    ext r j
    simp [arnoldiMatrix, lanczosRecurrence_eq_arnoldiBasis hA]
  rw [hQ]
  exact (arnoldiDecomp A b q h).graded

end NLAlib
