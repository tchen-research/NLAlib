import NLAlib.ForMathlib.Combinatorics.Hall.WeightedMatrix
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Tactic.GCongr

/-!
# Extracting a balanced part from a nonnegative matrix

A nonnegative square matrix with a common row sum contains a nonnegative
matrix with equal row and column sums whose residual has no supported
permutation. Subtract a smallest positive supported permutation at each
step; the number of nonzero entries strictly decreases. The support induction
adapts Bhavik Mehta's Apache-2.0 Mathlib proof in `Analysis.Convex.Birkhoff`.

This is the finite extraction argument in GGOW, *Operator scaling: theory
and applications*, arXiv:1511.03730v4, Claim 3.3. The residual Hall estimate
is provided by `WeightedMatrix`.
-/

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A common-row-sum nonnegative matrix has a balanced nonnegative part
whose residual has no permutation of positive entries. The extracted part
has a common row and column sum between zero and the original row sum.
Source: GGOW, arXiv:1511.03730v4, Claim 3.3. -/
theorem exists_balanced_le_with_no_perm_pos (C : Matrix n n ℝ) (s : ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hs : 0 ≤ s) (hrow : ∀ i, ∑ j, C i j = s) :
    ∃ (D : Matrix n n ℝ) (a : ℝ), 0 ≤ a ∧ a ≤ s ∧
      (∀ i j, 0 ≤ D i j) ∧ (∀ i, ∑ j, D i j = a) ∧
      (∀ j, ∑ i, D i j = a) ∧ (∀ i j, D i j ≤ C i j) ∧
      ¬ ∃ σ : Equiv.Perm n, ∀ i, 0 < (C - D) i (σ i) := by
  classical
  set d : ℕ := #{ij : n × n | C ij.1 ij.2 ≠ 0} with hd
  clear_value d
  induction d using Nat.strongRecOn generalizing C s with
  | ind d ih =>
    by_cases hp : ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i)
    · obtain ⟨σ, hσ⟩ := hp
      obtain ⟨i, _, hi⟩ := exists_min_image univ (fun i => C i (σ i)) univ_nonempty
      let t := C i (σ i)
      let P := σ.permMatrix ℝ
      let N := C - t • P
      have ht : 0 < t := hσ i
      have hmin (j : n) : t ≤ C j (σ j) := hi j (mem_univ j)
      have hts : t ≤ s := by
        rw [← hrow i]
        exact single_le_sum (fun j _ => hC i j) (mem_univ _)
      have hP := mem_doublyStochastic_iff_sum.mp
        (permMatrix_mem_doublyStochastic (σ := σ) (R := ℝ))
      have hN (j k : n) : 0 ≤ N j k := by
        dsimp [N, P]
        simp only [Option.mem_def, Option.some.injEq]
        split_ifs with hjk
        · subst k
          simpa using sub_nonneg.mpr (hmin j)
        · simpa using hC j k
      have hNrow (j : n) : ∑ k, N j k = s - t := by
        simp only [N, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          sum_sub_distrib, ← mul_sum]
        rw [hrow j, hP.2.1 j, mul_one]
      have hdN : #{ij : n × n | N ij.1 ij.2 ≠ 0} < d := by
        rw [hd]
        apply card_lt_card
        apply ssubset_iff_subset_ne.mpr
        refine ⟨?_, ?_⟩
        · intro jk hjk
          simp only [mem_filter_univ] at hjk ⊢
          intro hzero
          have hNzero : N jk.1 jk.2 = 0 := by
            have hPzero : P jk.1 jk.2 = 0 := by
              dsimp [P]
              simp only [Option.mem_def, Option.some.injEq, ite_eq_right_iff, one_ne_zero, imp_false]
              intro heq
              exact (hσ jk.1).ne' (by simpa [heq] using hzero)
            simp [N, hzero, hPzero]
          exact hjk hNzero
        · intro heq
          have hmem : (i, σ i) ∈ ({ij : n × n | C ij.1 ij.2 ≠ 0} : Finset (n × n)) := by
            simp [ht.ne', ← show t = C i (σ i) from rfl]
          have hmemN := (Finset.ext_iff.mp heq (i, σ i)).mpr hmem
          simp [N, P, t, Equiv.toPEquiv_apply] at hmemN
      obtain ⟨D, a, ha, has, hD, hDr, hDc, hDN, hno⟩ :=
        ih _ hdN N (s - t) hN (sub_nonneg.mpr hts) hNrow rfl
      refine ⟨t • P + D, t + a, add_nonneg ht.le ha, by linarith, ?_, ?_, ?_, ?_, ?_⟩
      · intro j k
        exact add_nonneg (mul_nonneg ht.le (hP.1 j k)) (hD j k)
      · intro j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          sum_add_distrib, ← mul_sum]
        rw [hP.2.1 j, hDr j, mul_one]
      · intro k
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          sum_add_distrib, ← mul_sum]
        rw [hP.2.2 k, hDc k, mul_one]
      · intro j k
        have h := hDN j k
        change D j k ≤ C j k - t * P j k at h
        change t * P j k + D j k ≤ C j k
        linarith
      · have hres : C - (t • P + D) = N - D := by
          ext j k
          simp only [N, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          ring
        rw [hres]
        exact hno
    · exact ⟨0, 0, le_rfl, hs, by simp, by simp, by simp, by simpa using hC,
        by simpa using hp⟩

/-- A nonnegative row-stochastic matrix contains a scalar multiple of a
doubly stochastic matrix. The scalar is at least one minus the square root
of the dimension times the squared column-sum defect. This is GGOW,
arXiv:1511.03730v4, Claim 3.3, including a possibly zero extracted part. -/
theorem exists_smul_doublyStochastic_le_of_row_sum_one (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hrow : ∀ i, ∑ j, C i j = 1) :
    ∃ (B : Matrix n n ℝ) (a : ℝ), B ∈ doublyStochastic ℝ n ∧
      0 ≤ a ∧ a ≤ 1 ∧
      1 - Real.sqrt ((Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2) ≤ a ∧
      ∀ i j, a * B i j ≤ C i j := by
  obtain ⟨D, a, ha, ha1, hD, hDr, hDc, hDC, hno⟩ :=
    exists_balanced_le_with_no_perm_pos C 1 hC zero_le_one hrow
  have hresrow (i : n) : ∑ j, (C - D) i j = 1 - a := by
    simp only [Matrix.sub_apply, sum_sub_distrib, hrow i, hDr i]
  have hHall := sq_le_card_mul_sum_sq_column_sub_of_no_perm_pos
    (C - D) (1 - a) (fun i j => sub_nonneg.mpr (hDC i j))
    (sub_nonneg.mpr ha1) hresrow hno
  have heq (j : n) : (∑ i, (C - D) i j) - (1 - a) = (∑ i, C i j) - 1 := by
    simp only [Matrix.sub_apply, sum_sub_distrib, hDc j]
    ring
  simp_rw [heq] at hHall
  have herr : 0 ≤ (Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
  have hroot := Real.sq_sqrt herr
  have hroot0 := Real.sqrt_nonneg ((Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2)
  have hbound : 1 - Real.sqrt ((Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2) ≤ a := by
    nlinarith
  obtain ⟨B, hB, hDB⟩ := (exists_mem_doublyStochastic_eq_smul_iff ha).mpr ⟨hD, hDr, hDc⟩
  refine ⟨B, a, hB, ha, ha1, hbound, ?_⟩
  intro i j
  simpa only [hDB, Matrix.smul_apply, smul_eq_mul] using hDC i j

/-- The column-stochastic version of finite balanced extraction, with the
defect measured in the row sums. Transposition preserves double stochasticity.
Source: GGOW, arXiv:1511.03730v4, Claim 3.3 in transposed orientation. -/
theorem exists_smul_doublyStochastic_le_of_col_sum_one (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hcol : ∀ j, ∑ i, C i j = 1) :
    ∃ (B : Matrix n n ℝ) (a : ℝ), B ∈ doublyStochastic ℝ n ∧
      0 ≤ a ∧ a ≤ 1 ∧
      1 - Real.sqrt ((Fintype.card n : ℝ) * ∑ i, ((∑ j, C i j) - 1) ^ 2) ≤ a ∧
      ∀ i j, a * B i j ≤ C i j := by
  obtain ⟨B, a, hB, ha, ha1, hbound, hBC⟩ :=
    exists_smul_doublyStochastic_le_of_row_sum_one Cᵀ
      (fun i j => hC j i) hcol
  exact ⟨Bᵀ, a, transpose_mem_doublyStochastic_iff.mpr hB,
    ha, ha1, hbound, fun i j => hBC j i⟩

end Matrix
