import NLAlib.ForMathlib.Topology.CubicalGrid
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.NormNum

/-! # Finite canonical grid walks between specified vertices

Endpoint delta arrays give explicit interval edge coefficients by finite
prefix sums. Their native boundaries telescope to the two endpoints, and
only edges between those endpoints have nonzero coefficients.
-/

noncomputable section
open Finset
namespace Fin

/-- Finite prefix sums commute with subtraction. -/
theorem partialSum_sub {A : Type*} [AddCommGroup A] {n : ℕ}
    (f g : Fin n → A) (i : Fin (n + 1)) :
    partialSum (fun j => f j - g j) i = partialSum f i - partialSum g i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialSum_succ, partialSum_succ, partialSum_succ, ih]
    abel

/-- The actual prefix sum of one endpoint delta is its threshold indicator. -/
theorem partialSum_ite_eq_one {n : ℕ} (a : Fin n) (i : Fin (n + 1)) :
    partialSum (fun j => if j = a then (1 : ℤ) else 0) i =
      if a.castSucc < i then 1 else 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialSum_succ, ih]
    simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_succ_iff]
    rcases lt_trichotomy a i with h | rfl | h
    · simp [h, h.le, h.ne']
    · simp
    · have hna : ¬a < i := not_lt.mpr (le_of_lt h)
      have hna' : ¬a ≤ i := not_le.mpr h
      simp [hna, hna', ne_of_lt h]

end Fin

namespace Cubical.Grid
variable {n : ℕ}

/-- Signed canonical edge coefficients from vertex `a` to vertex `b` on a
finite ordered row. They are constructed by prefix sums of endpoint deltas. -/
def intervalCoefficients (a b : Fin (n + 1)) : Fin n → ℤ :=
  Fin.edgePrefix (fun j => (if j = a then 1 else 0) - (if j = b then 1 else 0))

/-- The explicit interval coefficients equal the difference of the two
threshold indicators. They allow either orientation and coinciding endpoints. -/
theorem intervalCoefficients_eq (a b : Fin (n + 1)) (i : Fin n) :
    intervalCoefficients a b i =
      (if a ≤ i.castSucc then 1 else 0) - (if b ≤ i.castSucc then 1 else 0) := by
  simp only [intervalCoefficients, Fin.edgePrefix, Fin.partialSum_sub,
    Fin.partialSum_ite_eq_one, Fin.castSucc_lt_succ_iff]

/-- The finite divergence of the actual interval walk is the initial delta
minus the final delta. -/
theorem edgeBoundary_intervalCoefficients (a b : Fin (n + 1)) (i : Fin (n + 1)) :
    Fin.edgeBoundary (intervalCoefficients a b) i =
      (if i = a then 1 else 0) - (if i = b then 1 else 0) := by
  apply Fin.edgeBoundary_edgePrefix
  simp only [sum_sub_distrib, sum_ite_eq', mem_univ, if_true, sub_self]

/-- An active edge of the actual interval walk lies between its endpoint
vertices, for either orientation. -/
theorem intervalCoefficients_ne_zero_bounds (a b : Fin (n + 1)) (i : Fin n)
    (hi : intervalCoefficients a b i ≠ 0) :
    min a b ≤ i.castSucc ∧ i.succ ≤ max a b := by
  rw [intervalCoefficients_eq] at hi
  split_ifs at hi with ha hb hb
  · exact False.elim (hi (by norm_num))
  · have hab : i.castSucc < b := lt_of_not_ge hb
    constructor
    · exact (min_le_left a b).trans ha
    · exact (Fin.castSucc_lt_iff_succ_le.mp hab).trans (le_max_right a b)
  · have hab : i.castSucc < a := lt_of_not_ge ha
    constructor
    · exact (min_le_right a b).trans hb
    · exact (Fin.castSucc_lt_iff_succ_le.mp hab).trans (le_max_left a b)
  · exact False.elim (hi (by norm_num))

end Cubical.Grid

open scoped unitInterval
namespace Cubical.Grid
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {m n : ℕ}

/-- The actual canonical straight-edge chain on one grid row between two
specified vertices, with signed coefficients for either orientation. -/
def horizontalWalk (v : Fin (m + 1) → Fin (n + 1) → E)
    (a b : Fin (m + 1)) (j : Fin (n + 1)) : OneChain E :=
  ∑ i, intervalCoefficients a b i • Finsupp.single (horizontal v i j) 1

/-- The actual canonical straight-edge chain on one grid column. -/
def verticalWalk (v : Fin (m + 1) → Fin (n + 1) → E)
    (i : Fin (m + 1)) (a b : Fin (n + 1)) : OneChain E :=
  ∑ j, intervalCoefficients a b j • Finsupp.single (vertical v i j) 1

/-- The native boundary of the finite horizontal walk is its final vertex
minus its initial vertex, including coinciding endpoints. -/
theorem boundaryOne_horizontalWalk
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (a b : Fin (m + 1)) (j : Fin (n + 1)) :
    boundaryOne (horizontalWalk v a b j) = Finsupp.single (v b j) 1 - Finsupp.single (v a j) 1 := by
  classical
  have he := Fin.sum_edgeBoundary_smul (intervalCoefficients a b)
    (fun i => Finsupp.single (v i j) (1 : ℤ))
  simp only [edgeBoundary_intervalCoefficients, sub_smul, ite_smul, one_smul, zero_smul,
    sum_sub_distrib, sum_ite_eq', mem_univ, if_true] at he
  simp only [horizontalWalk, map_sum, map_smul, boundaryOne,
    Finsupp.linearCombination_single, one_smul, horizontal, Path.coe_toContinuousMap,
    Path.source, Path.target, smul_sub, sum_sub_distrib]
  simpa only [smul_sub, sum_sub_distrib, neg_sub] using congrArg Neg.neg he.symm

/-- The native boundary of the finite vertical walk is its final vertex
minus its initial vertex, including coinciding endpoints. -/
theorem boundaryOne_verticalWalk
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (i : Fin (m + 1)) (a b : Fin (n + 1)) :
    boundaryOne (verticalWalk v i a b) = Finsupp.single (v i b) 1 - Finsupp.single (v i a) 1 := by
  classical
  have he := Fin.sum_edgeBoundary_smul (intervalCoefficients a b)
    (fun j => Finsupp.single (v i j) (1 : ℤ))
  simp only [edgeBoundary_intervalCoefficients, sub_smul, ite_smul, one_smul, zero_smul,
    sum_sub_distrib, sum_ite_eq', mem_univ, if_true] at he
  simp only [verticalWalk, map_sum, map_smul, boundaryOne,
    Finsupp.linearCombination_single, one_smul, vertical, Path.coe_toContinuousMap,
    Path.source, Path.target, smul_sub, sum_sub_distrib]
  simpa only [smul_sub, sum_sub_distrib, neg_sub] using congrArg Neg.neg he.symm

/-- The horizontal coefficient array of the fixed L-shaped walk, first
along the starting row and then along the final column. -/
def walkHorizontalCoefficients (p q : Fin (m + 1) × Fin (n + 1))
    (i : Fin m) (j : Fin (n + 1)) : ℤ :=
  if j = p.2 then intervalCoefficients p.1 q.1 i else 0

/-- The vertical coefficient array of that same L-shaped walk. -/
def walkVerticalCoefficients (p q : Fin (m + 1) × Fin (n + 1))
    (i : Fin (m + 1)) (j : Fin n) : ℤ :=
  if i = q.1 then intervalCoefficients p.2 q.2 j else 0

/-- The actual finite L-shaped canonical grid walk between two vertices. -/
def walkChain (v : Fin (m + 1) → Fin (n + 1) → E)
    (p q : Fin (m + 1) × Fin (n + 1)) : OneChain E :=
  edgeChain v (walkHorizontalCoefficients p q) (walkVerticalCoefficients p q)

/-- The actual L-shaped walk is exactly its row walk plus its column walk. -/
theorem walkChain_eq_horizontalWalk_add_verticalWalk
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (p q : Fin (m + 1) × Fin (n + 1)) :
    walkChain v p q = horizontalWalk v p.1 q.1 p.2 + verticalWalk v q.1 p.2 q.2 := by
  classical
  simp [walkChain, edgeChain, walkHorizontalCoefficients, walkVerticalCoefficients,
    horizontalWalk, verticalWalk, ite_smul]

/-- The intermediate corner cancels in the native endpoint boundary of
the actual L-shaped grid walk. -/
theorem boundaryOne_walkChain
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (p q : Fin (m + 1) × Fin (n + 1)) :
    boundaryOne (walkChain v p q) =
      Finsupp.single (v q.1 q.2) 1 - Finsupp.single (v p.1 p.2) 1 := by
  rw [walkChain_eq_horizontalWalk_add_verticalWalk, map_add,
    boundaryOne_horizontalWalk, boundaryOne_verticalWalk]
  abel

end Cubical.Grid
