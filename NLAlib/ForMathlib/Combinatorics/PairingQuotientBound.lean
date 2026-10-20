import NLAlib.ForMathlib.Combinatorics.PairingQuotientGraph
import NLAlib.ForMathlib.Combinatorics.BipartitePartitionBound
import Mathlib.Tactic.FieldSimp

/-!
# Per-pairing exact smaller-iid comparator for the Gaussian extremum route

This file formalizes deterministic sum bounds for the alternating Gram-cycle
quotient. For a positive cycle dimension `p = q + 1`, endpoint maps
`alpha beta : E → Fin p ⊕ Fin p` covering the occurrences bijectively, and
arbitrary finite label types `I`, `J`, the unrestricted indicator sum
`pairingSum` equals the quotient partition sum
(`pairingSum_eq_sum_quotient`). The connectedness of the paired quotient
graph (proved in `PairingQuotientGraph`) yields the universal graph bound
`pairingSum_cycle_le`, whose exponents are the row-quotient and
column-quotient cardinalities. Replacing the column/row-sum bounds `a`, `c`
by natural-number bounds `d1`, `d2` gives `pairingSum_cycle_le_of_nat_bounds`; the
exact unit-profile identity `pairingSum_cycle_one` counts all labels;
and the normalized per-pairing comparator `pairingSum_cycle_div_card_le`
divides both sides by the label cardinalities.

This is deterministic combinatorial infrastructure for
`independent-entry-gaussian-extremum`; no Gaussian probability statement appears
here.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib.PairingQuotient

variable {O R C E I J : Type*}

/-- The unrestricted indicator sum over original labels: for each pair of row
and column labelings, the product over paired pairs of the weight at the
`alpha` endpoints when the paired pair identifies its row endpoints and its
column endpoints, and zero otherwise. This is exactly the left-hand side of
`sum_prod_indicator_eq_sum_quotient`. -/
noncomputable def pairingSum [Fintype R] [Fintype C] [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq R] [DecidableEq C] [DecidableEq I] [DecidableEq J]
    (sr : O → R) (tg : O → C) (alpha beta : E → O) (w : I → J → ℝ) : ℝ :=
  ∑ x : R → I, ∑ y : C → J,
    ∏ e : E,
      if x (sr (alpha e)) = x (sr (beta e)) ∧ y (tg (alpha e)) = y (tg (beta e))
      then w (x (sr (alpha e))) (y (tg (alpha e))) else 0

/-- The exact quotient identity for `pairingSum`: the unrestricted indicator
sum over original labels equals the sum over quotient labels of the product of
the weights at the endpoint classes. -/
lemma pairingSum_eq_sum_quotient (sr : O → R) (tg : O → C) (alpha beta : E → O)
    [Fintype R] [Fintype C] [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq R] [DecidableEq C] [DecidableEq I] [DecidableEq J]
    [Fintype (RowQuotient sr alpha beta)] [Fintype (ColQuotient tg alpha beta)]
    [DecidableEq (RowQuotient sr alpha beta)] [DecidableEq (ColQuotient tg alpha beta)]
    (w : I → J → ℝ) :
    pairingSum sr tg alpha beta w =
      ∑ f : RowQuotient sr alpha beta → I, ∑ g : ColQuotient tg alpha beta → J,
        ∏ e : E, w (f (rowEnd sr alpha beta e)) (g (colEnd tg alpha beta e)) := by
  simpa [pairingSum] using (sum_prod_indicator_eq_sum_quotient sr tg alpha beta w)

/-- The row quotient of the Gram cycle is finite, with the actual finite
`Fintype` instance from the finite row type `Fin (q + 1)`. -/
noncomputable instance cycleRowQuotientFintype (q : ℕ) {E : Type*}
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Fintype (RowQuotient (cycleRow (q + 1)) alpha beta) := by
  classical
  exact Quotient.fintype (rowSetoid (cycleRow (q + 1)) alpha beta)

/-- The column quotient of the Gram cycle is finite, with the actual finite
`Fintype` instance from the finite column type `Fin (q + 1)`. -/
noncomputable instance cycleColQuotientFintype (q : ℕ) {E : Type*}
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Fintype (ColQuotient (cycleCol (q + 1)) alpha beta) := by
  classical
  exact Quotient.fintype (colSetoid (cycleCol (q + 1)) alpha beta)

/-- The row quotient of the Gram cycle is nonempty (class of row `0`). -/
noncomputable instance cycleRowQuotientNonempty (q : ℕ) {E : Type*}
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Nonempty (RowQuotient (cycleRow (q + 1)) alpha beta) :=
  rowQuotient_nonempty_cycle q alpha beta

/-- The column quotient of the Gram cycle is nonempty (class of column `0`). -/
noncomputable instance cycleColQuotientNonempty (q : ℕ) {E : Type*}
    (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1)) :
    Nonempty (ColQuotient (cycleCol (q + 1)) alpha beta) :=
  colQuotient_nonempty_cycle q alpha beta

/-- For the alternating Gram cycle of positive dimension `q + 1`, the
unrestricted indicator sum is bounded by `(card I) * a ^ (r - 1) * c ^ v`,
where `r` and `v` are the row- and column-quotient cardinalities, whenever the
weights are nonnegative, at most `1`, have column sums at most `a`, row sums at
most `c`, and `a`, `c` are nonnegative. Empty label types `I`, `J` are
allowed. -/
theorem pairingSum_cycle_le [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (hcover : Function.Bijective (Sum.elim alpha beta))
    (w : I → J → ℝ) (a c : ℝ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hwle : ∀ i j, w i j ≤ 1)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ a)
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ c)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w ≤
      (Fintype.card I : ℝ) *
        a ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) *
        c ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
  classical
  have hsum : pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w =
      ∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → I,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → J,
          ∏ e : E, w (f (rowEnd (cycleRow (q + 1)) alpha beta e))
            (g (colEnd (cycleCol (q + 1)) alpha beta e)) := by
    exact pairingSum_eq_sum_quotient (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w
  rw [hsum]
  have hG : (SimpleGraph.bipartiteOccurrenceGraph
      (rowEnd (cycleRow (q + 1)) alpha beta) (colEnd (cycleCol (q + 1)) alpha beta)).Connected :=
    bipartiteOccurrenceGraph_quotient_cycle_connected q alpha beta hcover
  have hb : (∑ x : RowQuotient (cycleRow (q + 1)) alpha beta → I,
        ∑ y : ColQuotient (cycleCol (q + 1)) alpha beta → J,
          ∏ e : E, w (x (rowEnd (cycleRow (q + 1)) alpha beta e))
            (y (colEnd (cycleCol (q + 1)) alpha beta e))) ≤
      (Fintype.card I : ℝ) *
        a ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) *
        c ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
    have hcore := sum_prod_bipartite_edge_weight_le_of_connected
      (U := RowQuotient (cycleRow (q + 1)) alpha beta)
      (V := ColQuotient (cycleCol (q + 1)) alpha beta)
      (E := E) (I := I) (J := J)
      (sr := rowEnd (cycleRow (q + 1)) alpha beta)
      (tg := colEnd (cycleCol (q + 1)) alpha beta)
      hG w a c 1 hwnn hcol hrow hwle ha hc (by norm_num)
    simpa [one_pow, mul_one] using hcore
  exact hb

/-- Same bound with the column/row-sum bounds replaced by natural-number bounds:
if `a ≤ d1` and `c ≤ d2` for naturals `d1`, `d2`, then
`pairingSum ... ≤ (card I) * (d1 : ℝ) ^ (r - 1) * (d2 : ℝ) ^ v`. -/
theorem pairingSum_cycle_le_of_nat_bounds [Fintype E] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (hcover : Function.Bijective (Sum.elim alpha beta))
    (w : I → J → ℝ) (a c : ℝ) (d1 d2 : ℕ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hwle : ∀ i j, w i j ≤ 1)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ a)
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ c)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hd1 : a ≤ (d1 : ℝ)) (hd2 : c ≤ (d2 : ℝ)) :
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w ≤
      (Fintype.card I : ℝ) *
        (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
  classical
  have h1 := pairingSum_cycle_le q alpha beta hcover w a c hwnn hwle hcol hrow ha hc
  have hpow1 : a ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) ≤
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) :=
    pow_le_pow_left₀ ha hd1 _
  have hpow2 : c ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) ≤
      (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) :=
    pow_le_pow_left₀ hc hd2 _
  have hcard : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hd1nn : 0 ≤ (d1 : ℝ) := Nat.cast_nonneg d1
  calc
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w
        ≤ (Fintype.card I : ℝ) * a ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * c ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := h1
    _ ≤ (Fintype.card I : ℝ) * (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * c ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 hcard) (pow_nonneg hc _)
    _ ≤ (Fintype.card I : ℝ) * (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
        exact mul_le_mul_of_nonneg_left hpow2 (mul_nonneg hcard (pow_nonneg hd1nn _))

/-- The exact unit-profile identity: with the constant-one profile on
`Fin d1 × Fin d2` the unrestricted indicator sum equals
`(d1 : ℝ) ^ r * (d2 : ℝ) ^ v`. The identity remains valid for `d1 = 0` or
`d2 = 0`, preserving `0 ^ 0 = 1`. -/
theorem pairingSum_cycle_one [Fintype E]
    (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (d1 d2 : ℕ) :
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
      (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) =
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
  classical
  have hsum : pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
        (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) =
      ∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
          ∏ e : E, (1 : ℝ) := by
    exact pairingSum_eq_sum_quotient (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
      (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ))
  rw [hsum]
  have hcount : (∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
          (1 : ℝ)) =
      (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1) : ℝ) *
        (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  calc
    (∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
        ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
          ∏ e : E, (1 : ℝ))
        = ∑ f : RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1,
            ∑ g : ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2,
              (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          refine Finset.sum_congr rfl ?_
          intro g hg
          simp
    _ = (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta → Fin d1) : ℝ) *
          (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta → Fin d2) : ℝ) := hcount
    _ = (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) *
          (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          rw [Nat.cast_pow, Nat.cast_pow]

/-- The normalized per-pairing comparator: with nonempty `I` and positive
`d1`, dividing by the label cardinalities turns the bound of
`pairingSum_cycle_le_of_nat_bounds` into an inequality comparing the indicator
sum for arbitrary weights against the constant-one profile on
`Fin d1 × Fin d2`. No positivity of `d2` is required. -/
theorem pairingSum_cycle_div_card_le [Fintype E] [Fintype I] [Fintype J]
    [Nonempty I] [DecidableEq I] [DecidableEq J]
    (q : ℕ) (alpha beta : E → Fin (q + 1) ⊕ Fin (q + 1))
    (hcover : Function.Bijective (Sum.elim alpha beta))
    (w : I → J → ℝ) (d1 d2 : ℕ)
    (hwnn : ∀ i j, 0 ≤ w i j)
    (hwle : ∀ i j, w i j ≤ 1)
    (hcol : ∀ j : J, (∑ i : I, w i j) ≤ (d1 : ℝ))
    (hrow : ∀ i : I, (∑ j : J, w i j) ≤ (d2 : ℝ))
    (hd1 : 0 < d1) :
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w /
        (Fintype.card I : ℝ) ≤
      pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
        (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) / (d1 : ℝ) := by
  classical
  have hIposN : 0 < Fintype.card I := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
  have hIpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hIposN
  have hd1pos : 0 < (d1 : ℝ) := by exact_mod_cast hd1
  have hd1ne : (d1 : ℝ) ≠ 0 := ne_of_gt hd1pos
  have hUpos : 0 < Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) :=
    Fintype.card_pos_iff.mpr (rowQuotient_nonempty_cycle q alpha beta)
  have hUsub : Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) =
      (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_iff.mp hUpos)).symm
  have hb : pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w ≤
      (Fintype.card I : ℝ) *
        (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
    exact pairingSum_cycle_le_of_nat_bounds q alpha beta hcover w (d1 : ℝ) (d2 : ℝ) d1 d2
      hwnn hwle hcol hrow (by exact_mod_cast (le_of_lt hd1)) (by exact_mod_cast (Nat.zero_le d2))
      (le_rfl : (d1 : ℝ) ≤ (d1 : ℝ)) (le_rfl : (d2 : ℝ) ≤ (d2 : ℝ))
  have hdiv : pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w /
        (Fintype.card I : ℝ) ≤
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
    rw [div_le_iff₀ hIpos]
    calc
      pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w
          ≤ (Fintype.card I : ℝ) * (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := hb
      _ = ((d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta))) * (Fintype.card I : ℝ) := by ring
  have hunit : pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
        (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) =
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
    exact pairingSum_cycle_one q alpha beta d1 d2
  have hpowr : (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) =
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * (d1 : ℝ) := by
    calc
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta))
          = (d1 : ℝ) ^ ((Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) + 1) := by
            exact congrArg (fun k : ℕ => (d1 : ℝ) ^ k) hUsub
      _ = (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * (d1 : ℝ) := by
            rw [pow_succ]
  have hdiv1 : (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta)) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) / (d1 : ℝ) =
      (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) *
        (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := by
    rw [hpowr]
    field_simp [hd1ne]
  calc
    pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta w / (Fintype.card I : ℝ)
        ≤ (d1 : ℝ) ^ (Fintype.card (RowQuotient (cycleRow (q + 1)) alpha beta) - 1) * (d2 : ℝ) ^ (Fintype.card (ColQuotient (cycleCol (q + 1)) alpha beta)) := hdiv
    _ = pairingSum (cycleRow (q + 1)) (cycleCol (q + 1)) alpha beta
          (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) / (d1 : ℝ) := by
        rw [hunit]
        exact hdiv1.symm

end NLAlib.PairingQuotient
