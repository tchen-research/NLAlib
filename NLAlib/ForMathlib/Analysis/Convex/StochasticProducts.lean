import NLAlib.ForMathlib.Combinatorics.Hall.WeightedDecomposition
import Mathlib.Analysis.MeanInequalities

/-!
# Products of stochastic matrix-vector coordinates

A doubly stochastic matrix increases the product of positive coordinates.
Combining weighted AM--GM with finite balanced extraction gives the sharp
near-stochastic product lower bound used in GGOW, *Operator scaling: theory
and applications*, arXiv:1511.03730v4, Lemmas 3.2 and 3.4.

All statements are about actual matrix-vector products. No capacity
minimizer, permanent, or scaling algorithm is assumed.
-/

noncomputable section

open scoped BigOperators Matrix
open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A doubly stochastic matrix increases the product of positive
coordinates, by rowwise weighted AM--GM and the column-sum identity.
This is the scalar product inequality used in GGOW, Lemma 3.2. -/
theorem prod_le_prod_mulVec_of_mem_doublyStochastic {B : Matrix n n ℝ}
    (hB : B ∈ doublyStochastic ℝ n) (x : n → ℝ) (hx : ∀ j, 0 < x j) :
    (∏ j, x j) ≤ ∏ i, (B *ᵥ x) i := by
  have hrow (i : n) : (∏ j, x j ^ B i j) ≤ (B *ᵥ x) i := by
    exact Real.geom_mean_le_arith_mean_weighted univ (B i) x
      (fun j _ => nonneg_of_mem_doublyStochastic hB)
      (sum_row_of_mem_doublyStochastic hB i) (fun j _ => (hx j).le)
  calc
    (∏ j, x j) = ∏ i, ∏ j, x j ^ B i j := by
      rw [prod_comm]
      apply prod_congr rfl
      intro j _
      rw [← Real.rpow_sum_of_pos (hx j), sum_col_of_mem_doublyStochastic hB j]
      exact (Real.rpow_one _).symm
    _ ≤ ∏ i, (B *ᵥ x) i :=
      prod_le_prod (fun i _ => prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _)
        (fun i _ => hrow i)

/-- If a nonnegative matrix dominates a nonnegative multiple of a doubly
stochastic matrix, its coordinate product dominates the corresponding
power of that multiple times the original product. -/
theorem mul_prod_le_prod_mulVec_of_doublyStochastic_le {C B : Matrix n n ℝ}
    (hB : B ∈ doublyStochastic ℝ n) {a : ℝ} (ha : 0 ≤ a)
    (hBC : ∀ i j, a * B i j ≤ C i j) (x : n → ℝ) (hx : ∀ j, 0 < x j) :
    a ^ Fintype.card n * (∏ j, x j) ≤ ∏ i, (C *ᵥ x) i := by
  have hBx (i : n) : 0 ≤ (B *ᵥ x) i :=
    sum_nonneg fun j _ => mul_nonneg (nonneg_of_mem_doublyStochastic hB) (hx j).le
  have hmul (i : n) : a * (B *ᵥ x) i ≤ (C *ᵥ x) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply sum_le_sum
    intro j _
    calc
      a * (B i j * x j) = (a * B i j) * x j := (mul_assoc _ _ _).symm
      _ ≤ C i j * x j := mul_le_mul_of_nonneg_right (hBC i j) (hx j).le
  calc
    a ^ Fintype.card n * (∏ j, x j) ≤ a ^ Fintype.card n * (∏ i, (B *ᵥ x) i) :=
      mul_le_mul_of_nonneg_left (prod_le_prod_mulVec_of_mem_doublyStochastic hB x hx)
        (pow_nonneg ha _)
    _ = ∏ i, a * (B *ᵥ x) i := by rw [prod_mul_distrib]; simp
    _ ≤ ∏ i, (C *ᵥ x) i :=
      prod_le_prod (fun i _ => mul_nonneg ha (hBx i)) (fun i _ => hmul i)

/-- A column-stochastic nonnegative matrix with squared row-sum defect
at most `ε ≤ 1/(card n + 1)` has the product lower bound
`(1 - sqrt (card n * ε)) ^ card n`. This is GGOW, arXiv:1511.03730v4,
Lemma 3.2 in the orientation used by Lemma 3.4. -/
theorem mul_prod_le_prod_mulVec_of_col_sum_one (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hcol : ∀ j, ∑ i, C i j = 1)
    {ε : ℝ} (hε : ∑ i, ((∑ j, C i j) - 1) ^ 2 ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1))
    (x : n → ℝ) (hx : ∀ j, 0 < x j) :
    (1 - Real.sqrt ((Fintype.card n : ℝ) * ε)) ^ Fintype.card n *
      (∏ j, x j) ≤ ∏ i, (C *ᵥ x) i := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hε0 : 0 ≤ ε := (sum_nonneg fun _ _ => sq_nonneg _).trans hε
  have hn0 : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hεbound := (le_div_iff₀ (show (0 : ℝ) < (Fintype.card n : ℝ) + 1 by positivity)).mp hεsmall
  have hsmall : (Fintype.card n : ℝ) * ε ≤ 1 := by nlinarith
  have hbase : 0 ≤ 1 - Real.sqrt ((Fintype.card n : ℝ) * ε) :=
    sub_nonneg.mpr (Real.sqrt_le_one.mpr hsmall)
  obtain ⟨B, a, hB, ha, _, hbound, hBC⟩ :=
    exists_smul_doublyStochastic_le_of_col_sum_one C hC hcol
  have hbasea : 1 - Real.sqrt ((Fintype.card n : ℝ) * ε) ≤ a := by
    have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hε hn0)
    linarith
  calc
    _ ≤ a ^ Fintype.card n * (∏ j, x j) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase hbasea _)
        (prod_nonneg fun j _ => (hx j).le)
    _ ≤ _ := mul_prod_le_prod_mulVec_of_doublyStochastic_le hB ha hBC x hx

end Matrix
