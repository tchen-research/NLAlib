import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.Probability.Gaussian.Moments.WickMonotonicity
import NLAlib.ForMathlib.Combinatorics.EndpointPairingQuotient

/-!
# Oriented Wick diagrams for symmetric Gaussian profiles

The actual symmetric Gaussian ensemble is dominated diagram by diagram by
the two covariance orientations. Each resulting diagram is exactly a
connected endpoint-quotient partition function, so the profile-sensitive
weighted graph inequality applies without distinct-label restrictions.

Source: Latała–van Handel–Youssef, arXiv:1711.00807v2, Section 2.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

open EndpointPairingQuotient

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] in
private theorem canonical_pair_eq_iff_sym2_eq (i j k l : n) :
    (max i j, min i j) = (max k l, min k l) ↔ s(i, j) = s(k, l) := by
  have hsort (a b : n) : s(max a b, min a b) = s(a, b) := by
    by_cases hab : a ≤ b
    · simp only [max_eq_right hab, min_eq_left hab, Sym2.eq_swap]
    · simp only [max_eq_left (le_of_not_ge hab), min_eq_right (le_of_not_ge hab)]
  constructor
  · intro h
    exact (hsort i j).symm.trans ((congrArg (fun p : n × n => s(p.1, p.2)) h).trans (hsort k l))
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp only [max_comm, min_comm]

omit [Fintype n] in
private theorem profile_max_min_eq (b : Matrix n n ℝ) (hb : b.IsSymm) (i j : n) :
    b (max i j) (min i j) = b i j := by
  by_cases hij : i ≤ j
  · simpa only [max_eq_right hij, min_eq_left hij] using hb.apply i j
  · simp only [max_eq_left (le_of_not_ge hij), min_eq_right (le_of_not_ge hij)]

omit [Fintype n] in
private theorem covariance_le_sum_orientations (b : Matrix n n ℝ) (i j k l : n) :
    (if s(i, j) = s(k, l) then b i j ^ 2 else 0) ≤
      (if i = k ∧ j = l then b i j ^ 2 else 0) +
        (if i = l ∧ j = k then b i j ^ 2 else 0) := by
  by_cases h : s(i, j) = s(k, l)
  · rw [if_pos h]
    rcases Sym2.eq_iff.mp h with h | h
    · rw [if_pos h]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · rw [if_pos h]
      exact le_add_of_nonneg_left (by split_ifs <;> positivity)
  · rw [if_neg h]
    exact add_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity)

/-- The endpoint quotient of a Wick pairing after independently choosing
an orientation for every pair of cyclic entry occurrences. -/
abbrev symmetricCycleVertexQuotient {k : ℕ} (π : GaussianPairings k)
    (flip : Fin (gaussianPairingEdges π).length → Bool) :=
  VertexQuotient
    (fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).1)
    (fun e => orientedCycleSource ((gaussianPairingEdges π).get e).2 (flip e))
    (fun e => finRotate k ((gaussianPairingEdges π).get e).1)
    (fun e => orientedCycleTarget ((gaussianPairingEdges π).get e).2 (flip e))

/-- One oriented cyclic Wick diagram evaluated at a labeling of its original
cyclic vertices. Local equality indicators impose exactly the paired endpoint
relations; no additional label coincidences are excluded. -/
def symmetricCycleDiagramWeight (b : Matrix n n ℝ) {k : ℕ}
    (π : GaussianPairings k) (flip : Fin (gaussianPairingEdges π).length → Bool)
    (x : Fin k → n) : ℝ :=
  ∏ e : Fin (gaussianPairingEdges π).length,
    if x ((gaussianPairingEdges π).get e).1 =
          x (orientedCycleSource ((gaussianPairingEdges π).get e).2 (flip e)) ∧
        x (finRotate k ((gaussianPairingEdges π).get e).1) =
          x (orientedCycleTarget ((gaussianPairingEdges π).get e).2 (flip e))
    then b (x ((gaussianPairingEdges π).get e).1)
      (x (finRotate k ((gaussianPairingEdges π).get e).1)) ^ 2 else 0

omit [Fintype n] in
/-- Splitting cyclic entry covariance into its two endpoint orientations
gives exactly the sum of all oriented cyclic diagram weights. -/
theorem gaussianPairingWeight_cycle_covariance_eq_sum_diagrams (b : Matrix n n ℝ)
    {k : ℕ} (π : GaussianPairings k) (x : Fin k → n) :
    gaussianPairingWeight (fun r s =>
      (if x r = x s ∧ x (finRotate k r) = x (finRotate k s)
        then b (x r) (x (finRotate k r)) ^ 2 else 0) +
      (if x r = x (finRotate k s) ∧ x (finRotate k r) = x s
        then b (x r) (x (finRotate k r)) ^ 2 else 0)) π =
      ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
        symmetricCycleDiagramWeight b π flip x := by
  rw [gaussianPairingWeight_add_eq_sum_orientations]
  apply Finset.sum_congr rfl
  intro flip _
  apply Finset.prod_congr rfl
  intro e _
  cases flip e <;> simp [orientedCycleSource, orientedCycleTarget]

omit [Fintype n] in
private theorem pairingWeight_le_sum_symmetricCycleDiagramWeight (b : Matrix n n ℝ)
    {k : ℕ} (π : GaussianPairings k) (x : Fin k → n) :
    gaussianPairingWeight (fun r s =>
      if s(x r, x (finRotate k r)) = s(x s, x (finRotate k s))
      then b (x r) (x (finRotate k r)) ^ 2 else 0) π ≤
      ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
        symmetricCycleDiagramWeight b π flip x := by
  let C := fun r s : Fin k => if x r = x s ∧ x (finRotate k r) = x (finRotate k s)
    then b (x r) (x (finRotate k r)) ^ 2 else 0
  let D := fun r s : Fin k => if x r = x (finRotate k s) ∧ x (finRotate k r) = x s
    then b (x r) (x (finRotate k r)) ^ 2 else 0
  calc
    _ ≤ gaussianPairingWeight (fun r s => C r s + D r s) π :=
      gaussianPairingWeight_le_gaussianPairingWeight _ _
        (fun _ _ => by split_ifs <;> positivity)
        (fun r s => covariance_le_sum_orientations b _ _ _ _) π
    _ = _ := gaussianPairingWeight_cycle_covariance_eq_sum_diagrams b π x

/-- The positive trace moments of the actual symmetric Gaussian matrix are
bounded by the sum of all oriented Wick diagrams. Both diagonal orientations
are retained, which is the diagonal variance two convention of the GOE
comparator. -/
theorem integral_trace_symmetricGaussianMatrix_pow_le_sum_diagrams
    (b : Matrix n n ℝ) (hb : b.IsSymm) (k : ℕ) :
    (∫ G, ((symmetricGaussianMatrix b G) ^ (k + 1)).trace ∂gaussianMatrix n n) ≤
      ∑ π : GaussianPairings (k + 1),
        ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
          ∑ x : Fin (k + 1) → n, symmetricCycleDiagramWeight b π flip x := by
  rw [integral_trace_symmetricGaussianMatrix_pow_eq_sum_pairings]
  simp_rw [canonical_pair_eq_iff_sym2_eq, profile_max_min_eq b hb]
  calc
    _ ≤ ∑ x : Fin (k + 1) → n, ∑ π : GaussianPairings (k + 1),
        ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
          symmetricCycleDiagramWeight b π flip x :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun π _ =>
        pairingWeight_le_sum_symmetricCycleDiagramWeight b π x
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro π _
      exact Finset.sum_comm

/-- Every oriented native Gaussian Wick diagram obeys the constant-one
profile-sensitive weighted graph bound, including single-vertex quotients,
loops and arbitrary further coincidences of quotient labels. -/
theorem sum_symmetricCycleDiagramWeight_le_of_power_sums
    (b : Matrix n n ℝ) (hb : b.IsSymm) {k : ℕ} (π : GaussianPairings (k + 1))
    (flip : Fin (gaussianPairingEdges π).length → Bool)
    (s : n → ℝ) (hcap : ∀ i j, b i j ^ 2 ≤ s i)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hdA : (∑ i, (∑ j, b i j ^ 2) ^ (gaussianPairingEdges π).length) ≤
      A ^ (gaussianPairingEdges π).length)
    (hsB : (∑ i, s i ^ (gaussianPairingEdges π).length) ≤ B ^ (gaussianPairingEdges π).length) :
    (∑ x : Fin (k + 1) → n, symmetricCycleDiagramWeight b π flip x) ≤
      A ^ (Nat.card (symmetricCycleVertexQuotient π flip) - 1) *
        B ^ ((gaussianPairingEdges π).length - (Nat.card (symmetricCycleVertexQuotient π flip) - 1)) := by
  classical
  let a := fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).1
  let b' := fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).2
  let Q := symmetricCycleVertexQuotient π flip
  let : Fintype Q := Fintype.ofFinite Q
  have hconn := paired_oriented_cycle_connected a b' (gaussianPairingEdges_endpoints_bijective π).surjective flip
  have hlength : 0 < (gaussianPairingEdges π).length := by
    have hh := two_mul_gaussianPairingEdges_length π
    omega
  have h := sum_prod_indicator_le_of_power_sums a
    (fun e => orientedCycleSource (b' e) (flip e))
    (fun e => finRotate (k + 1) (a e))
    (fun e => orientedCycleTarget (b' e) (flip e)) hconn
    (by simpa only [Fintype.card_fin] using hlength)
    (fun i j => b i j ^ 2) (fun _ _ => sq_nonneg _) (fun i j => by rw [hb.apply i j])
    s hcap A B hA hB (by simpa only [Fintype.card_fin] using hdA)
    (by simpa only [Fintype.card_fin] using hsB)
  simpa only [symmetricCycleDiagramWeight, Fintype.card_fin, Nat.card_eq_fintype_card] using h

end NLAlib
