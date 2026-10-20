import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.List.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianGramWick
import NLAlib.ForMathlib.Combinatorics.PairingQuotientBound
import NLAlib.Matrix.Basic.NormalizedTrace

/-!
# Smaller iid Gaussian comparison for independent-entry Gram moments

Independent symmetric real entries with Gaussian-dominated even moments and a
nonnegative profile whose maximal squared entry is one have every positive
integer normalized Gram moment bounded by a homogeneous Gaussian comparator.
Its row count is the ceiling of the maximum column sum of entry squares; its
column count is the ceiling of the maximum row sum. Each trace is divided by
its own row dimension, and the comparator dimensions are independent of the
moment order.

The proof combines the independent-entry moment comparison with the native
Gaussian Wick expansion. For each canonical pairing, its covariance product is
identified with the unrestricted partition sum of the connected pairing
quotient, so the exact per-pairing comparison applies. Finite maxima then give
the source's ceiling dimensions. The native Gaussian step permits signed
profiles, empty column types, and any natural comparator column count; the final source
statement assumes both original index types nonempty and maximum entry square
one. No quotient connectivity or Gaussian moment comparison is assumed.

Source: Brailovskaya–van Handel, arXiv:2401.06284v2, Model 1.3 and Theorems
1.7 and 4.1. This file realizes `independent-entry-gaussian-extremum`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
open NLAlib.PairingQuotient

namespace NLAlib

section GramExtremumMaxima

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The maximal squared entry of the profile: the `sup'` over `I × J` of the
entry squares `b i j ^ 2`. This is `sigma_*^2`; for a nonnegative scale this
equals `1` exactly when `sigma_* = 1`. -/
private def gramEntryMaxSq (b : I → J → ℝ) : ℝ :=
  (Finset.univ : Finset (I × J)).sup' Finset.univ_nonempty (fun e => b e.1 e.2 ^ 2)

/-- The maximal column sum of entry squares: the `sup'` over `J` of
`∑ i : I, b i j ^ 2`. -/
private def gramColMaxSum (b : I → J → ℝ) : ℝ :=
  (Finset.univ : Finset J).sup' Finset.univ_nonempty (fun j => ∑ i : I, b i j ^ 2)

/-- The maximal row sum of entry squares: the `sup'` over `I` of
`∑ j : J, b i j ^ 2`. -/
private def gramRowMaxSum (b : I → J → ℝ) : ℝ :=
  (Finset.univ : Finset I).sup' Finset.univ_nonempty (fun i => ∑ j : J, b i j ^ 2)

/-- The maximal squared entry is nonnegative, since it is attained at an
actual entry square. -/
private lemma gramEntryMaxSq_nonneg (b : I → J → ℝ) : 0 ≤ gramEntryMaxSq b := by
  classical
  unfold gramEntryMaxSq
  obtain ⟨e, he, hEq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (I × J))) (H := Finset.univ_nonempty)
    (f := fun e : I × J => b e.1 e.2 ^ 2)
  rw [hEq]
  exact sq_nonneg (b e.1 e.2)

/-- If the maximal squared entry is `1`, then every entry square is at most
`1`. -/
private lemma gram_entry_sq_le_one_of_gramEntryMaxSq_eq_one (b : I → J → ℝ)
    (hmax : gramEntryMaxSq b = 1) (i : I) (j : J) : b i j ^ 2 ≤ 1 := by
  classical
  unfold gramEntryMaxSq at hmax
  rw [← hmax]
  exact Finset.le_sup' (s := (Finset.univ : Finset (I × J)))
    (f := fun e : I × J => b e.1 e.2 ^ 2) (Finset.mem_univ (i, j))

omit [Nonempty I] in
/-- Each column sum of squares is at most the maximal column sum. -/
private lemma gram_col_sum_le_gramColMaxSum (b : I → J → ℝ) (j : J) :
    (∑ i : I, b i j ^ 2) ≤ gramColMaxSum b := by
  classical
  unfold gramColMaxSum
  exact Finset.le_sup' (s := (Finset.univ : Finset J))
    (f := fun j : J => ∑ i : I, b i j ^ 2) (Finset.mem_univ j)

omit [Nonempty J] in
/-- Each row sum of squares is at most the maximal row sum. -/
private lemma gram_row_sum_le_gramRowMaxSum (b : I → J → ℝ) (i : I) :
    (∑ j : J, b i j ^ 2) ≤ gramRowMaxSum b := by
  classical
  unfold gramRowMaxSum
  exact Finset.le_sup' (s := (Finset.univ : Finset I))
    (f := fun i : I => ∑ j : J, b i j ^ 2) (Finset.mem_univ i)

/-- If the maximal squared entry is `1`, then the maximal column sum is at
least `1`: an entry attaining the maximum `1` contributes its square to its
column sum. -/
private lemma gramColMaxSum_ge_one_of_gramEntryMaxSq_eq_one (b : I → J → ℝ)
    (hmax : gramEntryMaxSq b = 1) : 1 ≤ gramColMaxSum b := by
  classical
  obtain ⟨e, he, hEq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (I × J))) (H := Finset.univ_nonempty)
    (f := fun e : I × J => b e.1 e.2 ^ 2)
  have he1 : b e.1 e.2 ^ 2 = 1 := by
    rw [← hEq]
    exact hmax
  have hsingle : b e.1 e.2 ^ 2 ≤ ∑ i : I, b i e.2 ^ 2 := by
    calc
      b e.1 e.2 ^ 2 = ∑ i ∈ ({e.1} : Finset I), b i e.2 ^ 2 := by simp
      _ ≤ ∑ i ∈ (Finset.univ : Finset I), b i e.2 ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.singleton_subset_iff.2 (Finset.mem_univ e.1))
          (fun i hi hnot => sq_nonneg (b i e.2))
  calc
    1 = b e.1 e.2 ^ 2 := he1.symm
    _ ≤ ∑ i : I, b i e.2 ^ 2 := hsingle
    _ ≤ gramColMaxSum b := gram_col_sum_le_gramColMaxSum b e.2

/-- If the maximal squared entry is `1`, then the maximal row sum is at
least `1`. -/
private lemma gramRowMaxSum_ge_one_of_gramEntryMaxSq_eq_one (b : I → J → ℝ)
    (hmax : gramEntryMaxSq b = 1) : 1 ≤ gramRowMaxSum b := by
  classical
  obtain ⟨e, he, hEq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (I × J))) (H := Finset.univ_nonempty)
    (f := fun e : I × J => b e.1 e.2 ^ 2)
  have he1 : b e.1 e.2 ^ 2 = 1 := by
    rw [← hEq]
    exact hmax
  have hsingle : b e.1 e.2 ^ 2 ≤ ∑ j : J, b e.1 j ^ 2 := by
    calc
      b e.1 e.2 ^ 2 = ∑ j ∈ ({e.2} : Finset J), b e.1 j ^ 2 := by simp
      _ ≤ ∑ j ∈ (Finset.univ : Finset J), b e.1 j ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.singleton_subset_iff.2 (Finset.mem_univ e.2))
          (fun j hj hnot => sq_nonneg (b e.1 j))
  calc
    1 = b e.1 e.2 ^ 2 := he1.symm
    _ ≤ ∑ j : J, b e.1 j ^ 2 := hsingle
    _ ≤ gramRowMaxSum b := gram_row_sum_le_gramRowMaxSum b e.1

/-- The natural ceiling of the maximal column sum is positive when the maximal
squared entry is `1`. -/
private lemma gramColMaxSum_ceil_pos (b : I → J → ℝ) (hmax : gramEntryMaxSq b = 1) :
    0 < Nat.ceil (gramColMaxSum b) := by
  classical
  exact Nat.ceil_pos.2 (lt_of_lt_of_le zero_lt_one (gramColMaxSum_ge_one_of_gramEntryMaxSq_eq_one b hmax))

/-- The natural ceiling of the maximal row sum is positive when the maximal
squared entry is `1`. -/
private lemma gramRowMaxSum_ceil_pos (b : I → J → ℝ) (hmax : gramEntryMaxSq b = 1) :
    0 < Nat.ceil (gramRowMaxSum b) := by
  classical
  exact Nat.ceil_pos.2 (lt_of_lt_of_le zero_lt_one (gramRowMaxSum_ge_one_of_gramEntryMaxSq_eq_one b hmax))

omit [Nonempty I] in
/-- Every column sum of squares is at most its natural ceiling
`Nat.ceil (gramColMaxSum b)`. -/
private lemma gram_col_sum_le_ceil_gramColMaxSum (b : I → J → ℝ) (j : J) :
    (∑ i : I, b i j ^ 2) ≤ (Nat.ceil (gramColMaxSum b) : ℝ) := by
  classical
  exact (gram_col_sum_le_gramColMaxSum b j).trans (Nat.le_ceil (gramColMaxSum b))

omit [Nonempty J] in
/-- Every row sum of squares is at most its natural ceiling
`Nat.ceil (gramRowMaxSum b)`. -/
private lemma gram_row_sum_le_ceil_gramRowMaxSum (b : I → J → ℝ) (i : I) :
    (∑ j : J, b i j ^ 2) ≤ (Nat.ceil (gramRowMaxSum b) : ℝ) := by
  classical
  exact (gram_row_sum_le_gramRowMaxSum b i).trans (Nat.le_ceil (gramRowMaxSum b))

end GramExtremumMaxima

section GramExtremumAdapter

variable {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- The first occurrence of each edge of the canonical pairing `π` on the Gram cycle with
occurrence type `Fin p ⊕ Fin p`: edge index `e` is transported through `gramCycleEquiv p`
from the first endpoint of `(gaussianPairingEdges π).get e` in `Fin (p + p)`. -/
def gramPairingFirstOccurrence (p : ℕ) (π : GaussianPairings (p + p)) :
    Fin (gaussianPairingEdges π).length → Fin p ⊕ Fin p :=
  fun e => gramCycleEquiv p ((gaussianPairingEdges π).get e).1

/-- The second occurrence of each edge of the canonical pairing `π` on the Gram cycle with
occurrence type `Fin p ⊕ Fin p`: edge index `e` is transported through `gramCycleEquiv p`
from the second endpoint of `(gaussianPairingEdges π).get e` in `Fin (p + p)`. -/
def gramPairingSecondOccurrence (p : ℕ) (π : GaussianPairings (p + p)) :
    Fin (gaussianPairingEdges π).length → Fin p ⊕ Fin p :=
  fun e => gramCycleEquiv p ((gaussianPairingEdges π).get e).2

/-- The transported endpoints of the edge list of a canonical pairing cover the
Gram cycle occurrences bijectively: the existing endpoint bijection of
`gaussianPairingEdges` composed with `gramCycleEquiv p`. -/
lemma bijective_sum_elim_gramPairingFirstOccurrence_gramPairingSecondOccurrence (p : ℕ) (π : GaussianPairings (p + p)) :
    Function.Bijective
      (Sum.elim (gramPairingFirstOccurrence p π) (gramPairingSecondOccurrence p π) :
        Fin (gaussianPairingEdges π).length ⊕ Fin (gaussianPairingEdges π).length →
          Fin p ⊕ Fin p) := by
  have hb : Function.Bijective
      (Sum.elim (fun e : Fin (gaussianPairingEdges π).length =>
          ((gaussianPairingEdges π).get e).1)
        (fun e : Fin (gaussianPairingEdges π).length =>
          ((gaussianPairingEdges π).get e).2) :
        Fin (gaussianPairingEdges π).length ⊕ Fin (gaussianPairingEdges π).length →
          Fin (p + p)) :=
    gaussianPairingEdges_endpoints_bijective π
  have href : Sum.elim (gramPairingFirstOccurrence p π) (gramPairingSecondOccurrence p π) =
      (gramCycleEquiv p ∘ Sum.elim
        (fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).1)
        (fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).2)) := by
    funext s
    cases s <;> rfl
  rw [href]
  exact (gramCycleEquiv p).bijective.comp hb

omit [Fintype I] [Fintype J] in
/-- Per edge of a canonical pairing, the square covariance of the two paired
Gram cycle occurrences is exactly the equality-indicator term of `pairingSum`
with the transported endpoint maps. The edge is given as a pair of positions in
`Fin (p + p)`. -/
private lemma gram_edge_weight_eq_pairingSum_indicator (b : I → J → ℝ) (p : ℕ)
    (x : Fin p → I) (y : Fin p → J)
    (e : Fin (p + p) × Fin (p + p)) :
    gramCyclePairCovariance b p x y e.1 e.2 =
      if x (cycleRow p (gramCycleEquiv p e.1)) = x (cycleRow p (gramCycleEquiv p e.2)) ∧
          y (cycleCol p (gramCycleEquiv p e.1)) = y (cycleCol p (gramCycleEquiv p e.2))
        then b (x (cycleRow p (gramCycleEquiv p e.1))) (y (cycleCol p (gramCycleEquiv p e.1))) ^ 2
        else 0 := by
  unfold gramCyclePairCovariance
  cases h1 : gramCycleEquiv p e.1 <;> cases h2 : gramCycleEquiv p e.2 <;>
    simp [gramCycleIdx, cycleRow, cycleCol, Prod.ext_iff]
  rfl

omit [Fintype I] [Fintype J] in
/-- The pairing weight of the Gram-cycle covariance writes as the product over
the edge list of the equality-indicator terms of `pairingSum`. -/
private lemma gaussianPairingWeight_cycle_eq_prod_gaussianPairingEdges (b : I → J → ℝ)
    (p : ℕ) (x : Fin p → I) (y : Fin p → J)
    (π : GaussianPairings (p + p)) :
    gaussianPairingWeight (gramCyclePairCovariance b p x y) π =
      ((gaussianPairingEdges π).map (fun e =>
        if x (cycleRow p (gramCycleEquiv p e.1)) = x (cycleRow p (gramCycleEquiv p e.2)) ∧
            y (cycleCol p (gramCycleEquiv p e.1)) = y (cycleCol p (gramCycleEquiv p e.2))
          then b (x (cycleRow p (gramCycleEquiv p e.1))) (y (cycleCol p (gramCycleEquiv p e.1))) ^ 2
          else 0)).prod := by
  rw [gaussianPairingWeight_eq_prod_gaussianPairingEdges]
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  exact gram_edge_weight_eq_pairingSum_indicator b p x y e

/-- **Canonical-pairing adapter**: the per-pairing contribution of the native
Gaussian Gram Wick expansion is exactly the unrestricted equality-indicator sum
of `pairingSum` with the transported cycle endpoint maps and weights the entry
squares. The identity holds for arbitrary real profiles `b`, including signed
ones. -/
theorem gramPairingContribution_eq_pairingSum_cycle (b : I → J → ℝ) (p : ℕ)
    (π : GaussianPairings (p + p)) :
    gramPairingContribution b p π =
      pairingSum (cycleRow p) (cycleCol p) (gramPairingFirstOccurrence p π) (gramPairingSecondOccurrence p π)
        (fun i j => b i j ^ 2) := by
  classical
  unfold gramPairingContribution pairingSum
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [gaussianPairingWeight_cycle_eq_prod_gaussianPairingEdges b p x y π]
  rw [← Fin.prod_univ_fun_getElem (gaussianPairingEdges π)]
  apply Finset.prod_congr rfl
  intro i _
  simp [gramPairingFirstOccurrence, gramPairingSecondOccurrence]; rfl

/-- **Stage 1 bound**: for every canonical pairing, the per-pairing
contribution normalized by the row cardinality is at most the unit-profile
contribution on `Fin d1 × Fin d2` normalized by `d1`, whenever the entry
squares are at most `1`, column sums at most `d1`, row sums at most `d2`, and
`d1 > 0`. -/
theorem gramPairingContribution_div_card_le_unit_profile
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I]
    [DecidableEq I] [DecidableEq J]
    (b : I → J → ℝ) (p : ℕ) (hp : 0 < p)
    (π : GaussianPairings (p + p)) (d1 d2 : ℕ)
    (hentry : ∀ i j, b i j ^ 2 ≤ 1)
    (hcol : ∀ j : J, (∑ i : I, b i j ^ 2) ≤ (d1 : ℝ))
    (hrow : ∀ i : I, (∑ j : J, b i j ^ 2) ≤ (d2 : ℝ))
    (hd1 : 0 < d1) :
    gramPairingContribution b p π / (Fintype.card I : ℝ) ≤
      gramPairingContribution (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) p π /
        (d1 : ℝ) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp)
  change gramPairingContribution b (q + 1) π / (Fintype.card I : ℝ) ≤
    gramPairingContribution (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) (q + 1) π /
      (d1 : ℝ)
  have hb := pairingSum_cycle_div_card_le (q := q)
    (alpha := gramPairingFirstOccurrence (q + 1) π) (beta := gramPairingSecondOccurrence (q + 1) π)
    (hcover := bijective_sum_elim_gramPairingFirstOccurrence_gramPairingSecondOccurrence (q + 1) π)
    (w := fun i j => b i j ^ 2) (d1 := d1) (d2 := d2)
    (hwnn := (fun i j => sq_nonneg (b i j)))
    (hwle := hentry) (hcol := hcol) (hrow := hrow) (hd1 := hd1)
  simpa only [gramPairingContribution_eq_pairingSum_cycle, one_pow] using hb

end GramExtremumAdapter

section GramExtremumNativeComparator

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I]
  [DecidableEq I] [DecidableEq J]

/-- The raw trace moment of the homogeneous Gaussian matrix on `Fin d1 × Fin d2`
equals the pairing sum of the unit-profile contributions. -/
private lemma integral_unit_gaussian_trace_pow_eq_sum_pairings (p : ℕ) (hp : 0 < p)
    (d1 d2 : ℕ) :
    (∫ Y : Matrix (Fin d1) (Fin d2) ℝ,
        (((Y) *
          (Y)ᴴ) ^ p).trace
        ∂ gaussianMatrix (Fin d1) (Fin d2)) =
      ∑ π : GaussianPairings (p + p),
        gramPairingContribution (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) p π := by
  have hof (Y : Matrix (Fin d1) (Fin d2) ℝ) :
      Matrix.of (fun i j => Y i j) = Y := rfl
  simpa only [one_mul, hof] using
    integral_trace_gram_pow_gaussianMatrix_eq_sum_pairings_outer
    (I := Fin d1) (J := Fin d2)
    (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) p hp

/-- **Stage 2: native Gaussian rectangular comparator**. For every `p ≥ 1`,
the normalized raw trace moment of `b .* G` under the genuine `gaussianMatrix I J`
law is at most the normalized raw trace moment of the homogeneous Gaussian
matrix on `Fin d1 × Fin d2`, whenever the entry squares are at most `1`,
column sums at most `d1`, row sums at most `d2`, and `d1 > 0`. No positivity of
`b` is required. -/
theorem integral_trace_gram_pow_div_card_le_integral_gaussianMatrix_of_sq_bounds
    (b : I → J → ℝ) (p : ℕ) (hp : 0 < p)
    (d1 d2 : ℕ)
    (hentry : ∀ i j, b i j ^ 2 ≤ 1)
    (hcol : ∀ j : J, (∑ i : I, b i j ^ 2) ≤ (d1 : ℝ))
    (hrow : ∀ i : I, (∑ j : J, b i j ^ 2) ≤ (d2 : ℝ))
    (hd1 : 0 < d1) :
    (∫ G : Matrix I J ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ p).trace
        ∂ gaussianMatrix I J) / (Fintype.card I : ℝ) ≤
      (∫ Y : Matrix (Fin d1) (Fin d2) ℝ,
        (((Y) *
          (Y)ᴴ) ^ p).trace
        ∂ gaussianMatrix (Fin d1) (Fin d2)) / (d1 : ℝ) := by
  classical
  rw [integral_trace_gram_pow_gaussianMatrix_eq_sum_pairings_outer b p hp]
  rw [integral_unit_gaussian_trace_pow_eq_sum_pairings p hp d1 d2]
  calc
    (∑ π : GaussianPairings (p + p), gramPairingContribution b p π) /
        (Fintype.card I : ℝ)
        = ∑ π : GaussianPairings (p + p),
            gramPairingContribution b p π / (Fintype.card I : ℝ) := by
          rw [Finset.sum_div]
    _ ≤ ∑ π : GaussianPairings (p + p),
          gramPairingContribution (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) p π /
            (d1 : ℝ) := by
          exact Finset.sum_le_sum (fun π _ =>
            gramPairingContribution_div_card_le_unit_profile b p hp π d1 d2 hentry hcol hrow hd1)
    _ = (∑ π : GaussianPairings (p + p),
          gramPairingContribution (fun (_ : Fin d1) (_ : Fin d2) => (1 : ℝ)) p π) /
            (d1 : ℝ) := by
          rw [Finset.sum_div]

end GramExtremumNativeComparator

section GramExtremumIndependent

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I]
  [DecidableEq I] [DecidableEq J]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : I → J → Ω → ℝ}

/-- **Stage 3: independent symmetric entries, explicit natural caps**. For
independent symmetric entries with Gaussian-dominated even moments and a
nonnegative profile `b` with squares at most `1`, column sums at most `d1`,
row sums at most `d2`, `d1 > 0`, every positive integer normalized Gram trace
moment of the profiled matrix `(b i j * X i j)` is at most the normalized moment of the homogeneous Gaussian matrix on
`Fin d1 × Fin d2`. -/
theorem integral_trace_gram_pow_div_card_le_integral_gaussianMatrix_of_even_moments
    (hX : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ e : I × J, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : I × J, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ ∧
      ∫ w, (X e.1 e.2 w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (b : I → J → ℝ) (hb : ∀ e : I × J, 0 ≤ b e.1 e.2)
    (p : ℕ) (hp : 0 < p)
    (d1 d2 : ℕ)
    (hentry : ∀ i j, b i j ^ 2 ≤ 1)
    (hcol : ∀ j : J, (∑ i : I, b i j ^ 2) ≤ (d1 : ℝ))
    (hrow : ∀ i : I, (∑ j : J, b i j ^ 2) ≤ (d2 : ℝ))
    (hd1 : 0 < d1) :
    (∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p).trace ∂μ)
      / (Fintype.card I : ℝ) ≤
    (∫ Y : Matrix (Fin d1) (Fin d2) ℝ,
        (((Y) *
          (Y)ᴴ) ^ p).trace
        ∂ gaussianMatrix (Fin d1) (Fin d2)) / (d1 : ℝ) := by
  classical
  have hI := integral_trace_gram_pow_le_integral_gaussianMatrix_nat hX hsym h2 b hb p
  have hG := integral_trace_gram_pow_div_card_le_integral_gaussianMatrix_of_sq_bounds (I := I) (J := J)
    b p hp d1 d2 hentry hcol hrow hd1
  have hcardNN : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  exact (div_le_div_of_nonneg_right hI hcardNN).trans hG

end GramExtremumIndependent

section GramExtremumCeilingWrapper

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : I → J → Ω → ℝ}

/-- Every positive integer normalized Gram moment of independent symmetric
real entries with Gaussian-dominated even moments is bounded by the moment of
the homogeneous Gaussian matrix whose dimensions are the ceilings of the
maximal column and row sums of profile squares. The nonnegative profile has
maximal entry square one, equivalently the source's nonnegative scale `σ* = 1`.
Each trace uses its own row dimension. Both maxima and the native Gaussian
comparator appear explicitly in the conclusion.

Source: Brailovskaya–van Handel, arXiv:2401.06284v2, Model 1.3 and Theorem 1.7.

atlas: independent-entry-gaussian-extremum
-/
theorem integral_normalizedTrace_gram_pow_le_integral_gaussianMatrix
    (hX : iIndepFun (fun e : I × J => X e.1 e.2) μ)
    (hsym : ∀ e : I × J, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : I × J, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ ∧
      ∫ w, (X e.1 e.2 w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (b : I → J → ℝ) (hb : ∀ e : I × J, 0 ≤ b e.1 e.2)
    (hmax : (Finset.univ : Finset (I × J)).sup' Finset.univ_nonempty
      (fun e => b e.1 e.2 ^ 2) = 1)
    (p : ℕ) (hp : 0 < p) :
    (∫ w, normalizedTrace (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p) ∂μ) ≤
      (∫ Y : Matrix (Fin (Nat.ceil ((Finset.univ : Finset J).sup' Finset.univ_nonempty
        (fun j => ∑ i : I, b i j ^ 2))))
          (Fin (Nat.ceil ((Finset.univ : Finset I).sup' Finset.univ_nonempty
        (fun i => ∑ j : J, b i j ^ 2)))) ℝ,
        normalizedTrace (((Y) *
          (Y)ᴴ) ^ p)
        ∂ gaussianMatrix (Fin (Nat.ceil ((Finset.univ : Finset J).sup' Finset.univ_nonempty
        (fun j => ∑ i : I, b i j ^ 2))))
          (Fin (Nat.ceil ((Finset.univ : Finset I).sup' Finset.univ_nonempty
        (fun i => ∑ j : J, b i j ^ 2))))) := by
  classical
  let sigma1Sq : ℝ :=
    (Finset.univ : Finset J).sup' Finset.univ_nonempty (fun j => ∑ i : I, b i j ^ 2)
  let sigma2Sq : ℝ :=
    (Finset.univ : Finset I).sup' Finset.univ_nonempty (fun i => ∑ j : J, b i j ^ 2)
  let d1 : ℕ := Nat.ceil sigma1Sq
  let d2 : ℕ := Nat.ceil sigma2Sq
  change (∫ w, normalizedTrace (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p) ∂μ) ≤
    (∫ Y : Matrix (Fin d1) (Fin d2) ℝ,
      normalizedTrace (((Y) *
        (Y)ᴴ) ^ p)
      ∂ gaussianMatrix (Fin d1) (Fin d2))
  have hentry : ∀ i j, b i j ^ 2 ≤ 1 := gram_entry_sq_le_one_of_gramEntryMaxSq_eq_one b hmax
  have hcol : ∀ j : J, (∑ i : I, b i j ^ 2) ≤ (d1 : ℝ) := by
    intro j
    dsimp [d1, sigma1Sq]
    simpa [gramColMaxSum] using gram_col_sum_le_ceil_gramColMaxSum b j
  have hrow : ∀ i : I, (∑ j : J, b i j ^ 2) ≤ (d2 : ℝ) := by
    intro i
    dsimp [d2, sigma2Sq]
    simpa [gramRowMaxSum] using gram_row_sum_le_ceil_gramRowMaxSum b i
  have hd1 : 0 < d1 := by
    dsimp [d1, sigma1Sq]
    simpa [gramColMaxSum] using gramColMaxSum_ceil_pos b hmax
  have hcmp := integral_trace_gram_pow_div_card_le_integral_gaussianMatrix_of_even_moments (I := I) (J := J)
    hX hsym h2 b hb p hp d1 d2 hentry hcol hrow hd1
  have hintL : (∫ w,
        normalizedTrace (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p) ∂μ) =
      (∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p).trace ∂μ) /
        (Fintype.card I : ℝ) := by
    simp_rw [NLAlib.normalizedTrace]
    rw [integral_const_mul]
    simp [div_eq_mul_inv, mul_comm]
  have hintR : (∫ Y : Matrix (Fin d1) (Fin d2) ℝ,
        normalizedTrace (((Y) *
          (Y)ᴴ) ^ p)
        ∂ gaussianMatrix (Fin d1) (Fin d2)) =
      (∫ Y : Matrix (Fin d1) (Fin d2) ℝ,
        (((Y) *
          (Y)ᴴ) ^ p).trace
        ∂ gaussianMatrix (Fin d1) (Fin d2)) / (d1 : ℝ) := by
    simp_rw [NLAlib.normalizedTrace]
    rw [integral_const_mul]
    simp [Fintype.card_fin, div_eq_mul_inv, mul_comm]
  rw [hintL, hintR]
  simpa [d1, d2] using hcmp

end GramExtremumCeilingWrapper

end NLAlib
