import NLAlib.Matrix.Spectral.EigenvectorPairing
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Gershgorin row and column discs

Closed discs use the sum of the norms of off-diagonal entries. Their finite
unions retain zero-radius discs and allow overlapping discs within one union.
Source: Horn–Johnson (2013), Theorem 6.1.1.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n K : Type*} [Fintype n] [DecidableEq n] [NormedField K]

/-- The off-diagonal absolute row sum. Source: Horn–Johnson (2013),
Theorem 6.1.1; the radius of the corresponding closed Gershgorin disc. -/
def gershgorinRowRadius (A : Matrix n n K) (i : n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ‖A i j‖

/-- A closed Gershgorin row disc. Source: Horn–Johnson (2013), Theorem 6.1.1. -/
def gershgorinRowDisc (A : Matrix n n K) (i : n) : Set K :=
  Metric.closedBall (A i i) (gershgorinRowRadius A i)

/-- The union of a selected finite family of closed row discs.
Horn–Johnson (2013), Theorem 6.1.1; no internal disjointness is assumed. -/
def gershgorinRowUnion (A : Matrix n n K) (I : Finset n) : Set K :=
  ⋃ i ∈ I, gershgorinRowDisc A i

/-- The off-diagonal absolute column sum. Source: Horn–Johnson (2013),
Corollary 6.1.3; it is the row radius of the transpose. -/
def gershgorinColumnRadius (A : Matrix n n K) (i : n) : ℝ :=
  gershgorinRowRadius Aᵀ i

/-- A closed Gershgorin column disc. Source: Horn–Johnson (2013),
Corollary 6.1.3; transposition retains the diagonal center. -/
def gershgorinColumnDisc (A : Matrix n n K) (i : n) : Set K :=
  gershgorinRowDisc Aᵀ i

/-- The union of selected closed column discs. Source: Horn–Johnson (2013),
Corollary 6.1.3; multiplicity counting is obtained by transposition. -/
def gershgorinColumnUnion (A : Matrix n n K) (I : Finset n) : Set K :=
  gershgorinRowUnion Aᵀ I

/-- Every Gershgorin radius is nonnegative. Source: Horn–Johnson (2013),
Theorem 6.1.1; it is a finite sum of norms. -/
theorem gershgorinRowRadius_nonneg (A : Matrix n n K) (i : n) :
    0 ≤ gershgorinRowRadius A i := Finset.sum_nonneg fun j _ => norm_nonneg (A i j)

/-- The center belongs to its closed Gershgorin row disc, including radius
zero. Source: Horn–Johnson (2013), Theorem 6.1.1. -/
theorem diagonal_mem_gershgorinRowDisc (A : Matrix n n K) (i : n) :
    A i i ∈ gershgorinRowDisc A i := by
  change dist (A i i) (A i i) ≤ gershgorinRowRadius A i
  rw [dist_self]
  exact gershgorinRowRadius_nonneg A i

/-- Membership in one selected disc gives membership in its union.
Source: Horn–Johnson (2013), Theorem 6.1.1. -/
theorem mem_gershgorinRowUnion_of_mem {A : Matrix n n K} {I : Finset n}
    {i : n} (hi : i ∈ I) {z : K} (hz : z ∈ gershgorinRowDisc A i) :
    z ∈ gershgorinRowUnion A I := Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hz⟩⟩

/-- A finite union of Gershgorin discs is compact over a proper normed
field, including the real and complex fields. Source: Horn–Johnson (2013),
Theorem 6.1.1; this is the compactness input to exact counting. -/
theorem isCompact_gershgorinRowUnion [ProperSpace K] (A : Matrix n n K) (I : Finset n) :
    IsCompact (gershgorinRowUnion A I) :=
  I.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall (A i i) (gershgorinRowRadius A i)

/-- Every spectral point belongs to a closed row disc.
Horn–Johnson (2013), Theorem 6.1.1; the proof reuses Mathlib's Gershgorin theorem.
atlas: gershgorin-diagonal-dominance -/
theorem exists_mem_gershgorinRowDisc_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ i, μ ∈ gershgorinRowDisc A i := by
  obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
  exact eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hAx, hx⟩)

/-- Every spectral point belongs to a closed column disc.
Horn–Johnson (2013), Corollary 6.1.3; transpose preserves the characteristic
polynomial, so no symmetry hypothesis is needed.
atlas: gershgorin-diagonal-dominance -/
theorem exists_mem_gershgorinColumnDisc_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ i, μ ∈ gershgorinColumnDisc A i := by
  apply exists_mem_gershgorinRowDisc_of_mem_spectrum
  simpa only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose] using hμ

end NLAlib
