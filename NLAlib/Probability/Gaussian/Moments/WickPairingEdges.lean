import NLAlib.Probability.Gaussian.Moments.WickPairings

/-!
# Edge lists of canonical Gaussian pairings

This file exposes the finite edge list of the canonical perfect matchings
`GaussianPairings m` as `gaussianPairingEdges` and proves its basic interface:
the flattened endpoints coincide with `gaussianPairingPositions`, the number of
edges is `m / 2` (twice the edge count is the dimension), the pairing weight is
the product of the covariance entries along the edges (no symmetry assumption
on the covariance matrix), and endpoint coverage follows from the existing
coverage results for positions.

The empty pairing has no edges and weight one. Odd position counts have no
pairings, so the interfaces impose no evenness or nonemptiness hypotheses.
These are combinatorial adapters for Wick expansions, not a matrix moment
comparison theorem.
-/

namespace NLAlib

/-- The finite list of edges of a canonical complete pairing, in the same
recursive order as `gaussianPairingPositions`: the edge of the first remaining
position, followed by the edges of the recursive pairing on the remaining
positions, mapped through the partner-induced reindexing.
Source: Janson 1997, *Gaussian Hilbert Spaces*, §1.5. -/
def gaussianPairingEdges : {m : ℕ} → GaussianPairings m → List (Fin m × Fin m)
  | 0, _ => []
  | 1, π => Empty.elim π
  | _m + 2, (j, π) => (0, j.succ) :: (gaussianPairingEdges π).map
      (fun e => ((j.succAbove e.1).succ, (j.succAbove e.2).succ))

/-- The flattened endpoints of the edge list of a canonical pairing are exactly
its `gaussianPairingPositions`, in the same interleaved order: each edge's first
endpoint is immediately followed by its second endpoint. -/
theorem gaussianPairingEdges_flatMap_eq_gaussianPairingPositions {m : ℕ}
    (π : GaussianPairings m) :
    (gaussianPairingEdges π).flatMap (fun e => [e.1, e.2]) =
      gaussianPairingPositions π := by
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => exact Empty.elim π
  | more m ih _ =>
      rcases π with ⟨j, π⟩
      simp only [gaussianPairingEdges, gaussianPairingPositions,
        List.flatMap_cons]
      have hmap : ((gaussianPairingEdges π).map (fun e =>
          ((j.succAbove e.1).succ, (j.succAbove e.2).succ))).flatMap
            (fun e => [e.1, e.2]) =
          ((gaussianPairingEdges π).flatMap (fun e => [e.1, e.2])).map
            (fun a => (j.succAbove a).succ) := by
        induction (gaussianPairingEdges π) with
        | nil => rfl
        | cons e T ih =>
            simp [List.flatMap_cons, ih]
      rw [hmap, ih]
      rfl

/-- The weight of a canonical pairing is the product of the covariance entries
over its edges, with no symmetry assumption on `C`. -/
theorem gaussianPairingWeight_eq_prod_gaussianPairingEdges {m : ℕ}
    (C : Fin m → Fin m → ℝ) (π : GaussianPairings m) :
    gaussianPairingWeight C π =
      ((gaussianPairingEdges π).map (fun e => C e.1 e.2)).prod := by
  induction m using Nat.twoStepInduction with
  | zero => simp [gaussianPairingWeight, gaussianPairingEdges]
  | one => exact Empty.elim π
  | more m ih _ =>
      rcases π with ⟨j, π⟩
      simp only [gaussianPairingWeight, gaussianPairingEdges, List.map_cons,
        List.map_map, List.prod_cons]
      rw [ih]
      rfl

/-- Twice the number of edges of a canonical complete pairing is the number of
labelled positions. -/
theorem two_mul_gaussianPairingEdges_length {m : ℕ} (π : GaussianPairings m) :
    2 * (gaussianPairingEdges π).length = m := by
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => exact Empty.elim π
  | more m ih _ =>
      rcases π with ⟨j, π⟩
      simp only [gaussianPairingEdges, List.length_cons, List.length_map]
      have h := ih π
      omega

/-- A canonical complete pairing on `2 * p` labelled positions has exactly `p`
edges. -/
theorem gaussianPairingEdges_length_two_mul {p : ℕ}
    (π : GaussianPairings (2 * p)) :
    (gaussianPairingEdges π).length = p := by
  have h := two_mul_gaussianPairingEdges_length π
  omega

/-- The flattened edge endpoints of a canonical pairing use every position at
most once. -/
theorem gaussianPairingEdges_flatten_nodup {m : ℕ} (π : GaussianPairings m) :
    ((gaussianPairingEdges π).flatMap (fun e => [e.1, e.2])).Nodup := by
  rw [gaussianPairingEdges_flatMap_eq_gaussianPairingPositions]
  exact gaussianPairingPositions_nodup π

/-- The flattened edge endpoints of a canonical pairing cover every labelled
position. Together with `gaussianPairingEdges_flatten_nodup` this says each
endpoint appears exactly once. -/
theorem gaussianPairingEdges_flatten_toFinset {m : ℕ}
    (π : GaussianPairings m) :
    ((gaussianPairingEdges π).flatMap (fun e => [e.1, e.2])).toFinset =
      Finset.univ := by
  rw [gaussianPairingEdges_flatMap_eq_gaussianPairingPositions]
  exact gaussianPairingPositions_toFinset π

/-- The endpoints of the edge list of a canonical pairing form a bijection from
the disjoint union of the left and right endpoint copies to the labelled
positions: the `Sum.inl`-side is the first endpoint of every edge (in edge
order) and the `Sum.inr`-side is the second endpoint of every edge. -/
theorem gaussianPairingEdges_endpoints_bijective {m : ℕ}
    (π : GaussianPairings m) :
    Function.Bijective
      (Sum.elim (fun e : Fin (gaussianPairingEdges π).length =>
          ((gaussianPairingEdges π).get e).1)
        (fun e : Fin (gaussianPairingEdges π).length =>
          ((gaussianPairingEdges π).get e).2) :
        Fin (gaussianPairingEdges π).length ⊕
          Fin (gaussianPairingEdges π).length → Fin m) := by
  let E := Fin (gaussianPairingEdges π).length
  let alpha : E → Fin m := fun e => ((gaussianPairingEdges π).get e).1
  let beta : E → Fin m := fun e => ((gaussianPairingEdges π).get e).2
  change Function.Bijective (Sum.elim alpha beta)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · intro i
    have hi : i ∈ (gaussianPairingEdges π).flatMap (fun e => [e.1, e.2]) := by
      rw [gaussianPairingEdges_flatMap_eq_gaussianPairingPositions]
      exact List.mem_toFinset.mp (by
        rw [gaussianPairingPositions_toFinset π]
        exact Finset.mem_univ i)
    obtain ⟨e, heL, hei⟩ := (List.mem_flatMap.mp hi)
    obtain ⟨a, ha⟩ := (List.mem_iff_get.mp heL)
    simp at hei
    rcases hei with hei | hei
    · refine ⟨Sum.inl a, ?_⟩
      change ((gaussianPairingEdges π).get a).1 = i
      rw [ha, hei]
    · refine ⟨Sum.inr a, ?_⟩
      change ((gaussianPairingEdges π).get a).2 = i
      rw [ha, hei]
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hlen := two_mul_gaussianPairingEdges_length π
    omega

end NLAlib
