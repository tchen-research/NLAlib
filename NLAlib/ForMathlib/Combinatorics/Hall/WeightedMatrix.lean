import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted Hall bounds for nonnegative matrices

If every row of a nonnegative square matrix sums to `t ≥ 0` and no permutation
selects positive entries in every row, then
`t² ≤ card n * ∑ j (∑ i C i j - t)²`. A deficient set from Hall's theorem
concentrates at least `t` of the column error on its neighbours; finite
Cauchy–Schwarz gives the bound. Its contrapositive supplies a supported
permutation under a small row or column defect.

This packages the residual step used in Claim 3.3 of Garg–Gurvits–Oliveira–
Wigderson, *Operator scaling: theory and applications*, arXiv:1511.03730v4,
§3.1, as a direct Hall and Cauchy–Schwarz argument. Lemma 3.4 uses that step
in the operator-capacity reduction. The statements include empty index types
and `t = 0`; the no-permutation premise is impossible in the empty case.
-/

open scoped BigOperators

namespace Matrix

universe u

variable {n : Type u}

/-- If a nonnegative matrix with common row sum `t ≥ 0` has no supported
permutation, its squared column deviations satisfy this dimension-multiplied
lower bound. Source: the residual step of GGOW, arXiv:1511.03730v4, Claim 3.3,
proved here using Hall's theorem and finite Cauchy–Schwarz. -/
theorem sq_le_card_mul_sum_sq_column_sub_of_no_perm_pos [Fintype n] [DecidableEq n]
    (C : Matrix n n ℝ) (t : ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (ht : 0 ≤ t)
    (hrow : ∀ i, (∑ j : n, C i j) = t)
    (hno : ¬ ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i)) :
    t ^ 2 ≤ (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C i j) - t) ^ 2 := by
  classical
  let r : n → n → Prop := fun i j => 0 < C i j
  -- Hall: if every subset had a large enough neighbour set we would get a
  -- strictly positive row permutation, contradicting `hno`.
  have hhall : ¬ (∀ S : Finset n,
      S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, r i j)).card) := by
    intro hall
    have hinj : ∃ f : n → n, Function.Injective f ∧ ∀ i, r i (f i) :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hall
    rcases hinj with ⟨f, hfinj, hf⟩
    have hbij : Function.Bijective f := hfinj.bijective_of_finite
    refine hno ⟨Equiv.ofBijective f hbij, ?_⟩
    intro i
    exact hf i
  push Not at hhall
  rcases hhall with ⟨S, hS⟩
  let N : Finset n := Finset.univ.filter (fun j => ∃ i ∈ S, r i j)
  have hSN : N.card < S.card := by
    simpa [N] using hS
  -- Nonnegativity: entries of the rows of `S` outside the neighbour set vanish.
  have hC_zero {i j : n} (hi : i ∈ S) (hj : j ∉ N) : C i j = 0 := by
    have hnot : ¬ ∃ i ∈ S, 0 < C i j := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    have hle : C i j ≤ 0 := by
      by_contra hgt
      exact hnot ⟨i, hi, lt_of_not_ge hgt⟩
    exact le_antisymm hle (hC i j)
  -- Hence the row sum `t` is already achieved on `N`.
  have hrow_N (i : n) (hi : i ∈ S) : (∑ j ∈ N, C i j) = t := by
    have hsum : (∑ j ∈ N, C i j) = ∑ j ∈ Finset.univ, C i j :=
      Finset.sum_subset (Finset.subset_univ N) (fun j _ hjn => hC_zero hi hjn)
    simpa using hsum.trans (by simpa using hrow i)
  have hsumSN : (∑ i ∈ S, ∑ j ∈ N, C i j) = S.card * t := by
    calc
      (∑ i ∈ S, ∑ j ∈ N, C i j) = ∑ i ∈ S, t := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrow_N i hi
      _ = S.card * t := by simp
  -- Column sums over `N` dominate the mass already counted on `S`.
  have hcol_le (j : n) : (∑ i ∈ S, C i j) ≤ ∑ i : n, C i j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro i _ _
    exact hC i j
  have hSle : (S.card : ℝ) * t ≤ ∑ j ∈ N, (∑ i : n, C i j) := by
    calc
      (S.card : ℝ) * t = ∑ j ∈ N, (∑ i ∈ S, C i j) := by
        rw [← hsumSN]
        exact Finset.sum_comm
      _ ≤ ∑ j ∈ N, (∑ i : n, C i j) := by
        exact Finset.sum_le_sum (fun j _ => hcol_le j)
  let e : n → ℝ := fun j => (∑ i : n, C i j) - t
  have hE : t ≤ ∑ j ∈ N, e j := by
    have h1 : (S.card : ℝ) * t ≤ ∑ j ∈ N, (e j + t) := by
      calc
        (S.card : ℝ) * t ≤ ∑ j ∈ N, (∑ i : n, C i j) := hSle
        _ = ∑ j ∈ N, (e j + t) := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [e]
          ring
    have h2 : (∑ j ∈ N, (e j + t)) = (∑ j ∈ N, e j) + (N.card : ℝ) * t := by
      rw [Finset.sum_add_distrib]
      simp
    have h3 : (S.card : ℝ) * t - (N.card : ℝ) * t ≤ ∑ j ∈ N, e j := by
      linarith
    let d : ℕ := S.card - N.card
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.pos_of_ne_zero (Nat.sub_ne_zero_of_lt hSN)
    have hd1 : (1 : ℕ) ≤ d := by
      exact Nat.succ_le_of_lt hdpos
    have hd1r : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hcast_sub : (S.card : ℝ) - (N.card : ℝ) = (d : ℝ) := by
      dsimp [d]
      exact (Nat.cast_sub (m := N.card) (n := S.card) (Nat.le_of_lt hSN)).symm
    have hdt : t ≤ (d : ℝ) * t := by
      calc
        t = (1 : ℝ) * t := by ring
        _ ≤ (d : ℝ) * t := mul_le_mul_of_nonneg_right hd1r ht
    have hdE : (d : ℝ) * t ≤ ∑ j ∈ N, e j := by
      calc
        (d : ℝ) * t = ((S.card : ℝ) - (N.card : ℝ)) * t := by rw [hcast_sub]
        _ = (S.card : ℝ) * t - (N.card : ℝ) * t := by ring
        _ ≤ ∑ j ∈ N, e j := h3
    exact le_trans hdt hdE
  have hsq : t ^ 2 ≤ (∑ j ∈ N, e j) ^ 2 := pow_le_pow_left₀ ht hE 2
  have hcs : (∑ j ∈ N, e j) ^ 2 ≤ (N.card : ℝ) * ∑ j ∈ N, e j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq N (fun _ => (1 : ℝ)) e
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  have hsqN : (∑ j ∈ N, e j ^ 2) ≤ ∑ j : n, e j ^ 2 := by
    simpa using
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
        (fun j _ _ => sq_nonneg _))
  have hNle0 : (N.card : ℝ) ≤ ((Finset.univ : Finset n).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ N))
  have hNle : (N.card : ℝ) ≤ (Fintype.card n : ℝ) := by
    simpa using hNle0
  calc
    t ^ 2 ≤ (∑ j ∈ N, e j) ^ 2 := hsq
    _ ≤ (N.card : ℝ) * ∑ j ∈ N, e j ^ 2 := hcs
    _ ≤ (N.card : ℝ) * ∑ j : n, e j ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsqN (Nat.cast_nonneg _)
    _ ≤ (Fintype.card n : ℝ) * ∑ j : n, e j ^ 2 := by
      exact mul_le_mul_of_nonneg_right hNle (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    _ = (Fintype.card n : ℝ) * ∑ j : n, ((∑ i : n, C i j) - t) ^ 2 := by
      simp [e]

/-- A nonnegative row-stochastic matrix whose dimension-multiplied squared
column defect is less than one has a permutation selecting positive entries
in every row. This is the contrapositive of the weighted Hall bound at `t = 1`. -/
theorem exists_perm_pos_of_card_mul_sum_sq_column_sub_lt_one [Fintype n] [DecidableEq n]
    (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hrow : ∀ i, (∑ j : n, C i j) = 1)
    (herr : (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C i j) - 1) ^ 2 < 1) :
    ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i) := by
  by_contra hno
  have hle := sq_le_card_mul_sum_sq_column_sub_of_no_perm_pos C 1 hC zero_le_one hrow hno
  have hle' : (1 : ℝ) ≤ (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C i j) - 1) ^ 2 := by
    simpa using hle
  linarith

/-- A nonnegative column-stochastic matrix whose dimension-multiplied squared
row defect is less than one has a permutation selecting positive entries
in every row. Apply the row-stochastic result to the transpose and invert
its supported permutation. -/
theorem exists_perm_pos_of_card_mul_sum_sq_row_sub_lt_one [Fintype n] [DecidableEq n]
    (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hcol : ∀ j, (∑ i : n, C i j) = 1)
    (herr : (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C j i) - 1) ^ 2 < 1) :
    ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i) := by
  obtain ⟨τ, hτ⟩ := exists_perm_pos_of_card_mul_sum_sq_column_sub_lt_one (Matrix.transpose C)
    (by intro i j; simpa using hC j i)
    (by intro i; simpa using hcol i)
    (by simpa [Matrix.transpose_apply] using herr)
  refine ⟨τ.symm, ?_⟩
  intro i
  have hi := hτ (τ.symm i)
  simpa using hi

end Matrix
