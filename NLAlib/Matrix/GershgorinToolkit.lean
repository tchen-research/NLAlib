import NLAlib.Matrix.GershgorinCounting
import NLAlib.Matrix.GershgorinBounds
import NLAlib.Matrix.DiagonalDominanceCorollaries

/-!
# The complete Gershgorin and diagonal-dominance toolkit

Closed row and column discs, exact algebraic-multiplicity counts in isolated
unions, absolute and weighted radius bounds, strict-dominance stability and
positive definiteness, and Taussky's irreducible weak-dominance theorem.
Source: Horn–Johnson (2013), §§6.1–6.2 and Corollary 7.2.3.
-/

noncomputable section
open scoped Matrix NNReal ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The full Gershgorin and diagonal-dominance contract, including exact
algebraic multiplicities in separated closed-disc unions, row/column and
positive-weight bounds, strict positive-real-diagonal stability, symmetric
positive definiteness, and Taussky nonsingularity and stability with at least
one strict row. Complex Hermitian positive-definiteness variants are included.
Source: Horn–Johnson (2013), Theorem 6.1.1, Corollaries 6.1.3–6.1.8, 6.2.27 and
7.2.3. Empty matrices are retained; finite maxima use nonnegative suprema.
atlas: gershgorin-diagonal-dominance -/
theorem gershgorin_diagonal_dominance_properties
    (A : Matrix n n ℂ) (Ar : Matrix n n ℝ) :
    (∀ μ ∈ spectrum ℂ A, ∃ i, μ ∈ gershgorinRowDisc A i) ∧
    (∀ μ ∈ spectrum ℂ A, ∃ i, μ ∈ gershgorinColumnDisc A i) ∧
    (∀ I : Finset n,
      Disjoint (gershgorinRowUnion A I) (gershgorinRowUnion A Iᶜ) →
      charpolyRootCountIn A (gershgorinRowUnion A I) = I.card) ∧
    (∀ I : Finset n,
      Disjoint (gershgorinColumnUnion A I) (gershgorinColumnUnion A Iᶜ) →
      charpolyRootCountIn A (gershgorinColumnUnion A I) = I.card) ∧
    (spectralRadius ℂ A ≤ min
      (Finset.univ.sup (fun i => Real.toNNReal (∑ j, ‖A i j‖)) : ENNReal)
      (Finset.univ.sup (fun j => Real.toNNReal (∑ i, ‖A i j‖)) : ENNReal)) ∧
    (∀ p : n → ℝ, (∀ i, 0 < p i) → spectralRadius ℂ A ≤
      (Finset.univ.sup (fun i => Real.toNNReal ((p i)⁻¹ * ∑ j, p j * ‖A i j‖)) : ENNReal)) ∧
    ((∀ i, gershgorinRowRadius A i < ‖A i i‖) → A.det ≠ 0) ∧
    ((∀ i, gershgorinColumnRadius A i < ‖A i i‖) → A.det ≠ 0) ∧
    ((∀ i, (A i i).im = 0) → (∀ i, 0 < (A i i).re) →
      (∀ i, gershgorinRowRadius A i < ‖A i i‖) →
      ∀ μ ∈ spectrum ℂ A, 0 < μ.re) ∧
    (Ar.IsHermitian → (∀ i, 0 < Ar i i) →
      (∀ i, gershgorinRowRadius Ar i < ‖Ar i i‖) → Ar.PosDef) ∧
    ((A.map norm).IsIrreducible → (∀ i, gershgorinRowRadius A i ≤ ‖A i i‖) →
      (∃ i, gershgorinRowRadius A i < ‖A i i‖) → A.det ≠ 0) ∧
    ((A.map norm).IsIrreducible → (∀ i, (A i i).im = 0) → (∀ i, 0 < (A i i).re) →
      (∀ i, gershgorinRowRadius A i ≤ ‖A i i‖) →
      (∃ i, gershgorinRowRadius A i < ‖A i i‖) →
      ∀ μ ∈ spectrum ℂ A, 0 < μ.re) ∧
    (Ar.IsHermitian → (Ar.map norm).IsIrreducible → (∀ i, 0 < Ar i i) →
      (∀ i, gershgorinRowRadius Ar i ≤ ‖Ar i i‖) →
      (∃ i, gershgorinRowRadius Ar i < ‖Ar i i‖) → Ar.PosDef) ∧
    (A.IsHermitian → (∀ i, (A i i).im = 0) → (∀ i, 0 < (A i i).re) →
      (∀ i, gershgorinRowRadius A i < ‖A i i‖) → A.PosDef) ∧
    (A.IsHermitian → (A.map norm).IsIrreducible →
      (∀ i, (A i i).im = 0) → (∀ i, 0 < (A i i).re) →
      (∀ i, gershgorinRowRadius A i ≤ ‖A i i‖) →
      (∃ i, gershgorinRowRadius A i < ‖A i i‖) → A.PosDef) :=
  ⟨fun _ hμ => exists_mem_gershgorinRowDisc_of_mem_spectrum hμ,
    fun _ hμ => exists_mem_gershgorinColumnDisc_of_mem_spectrum hμ,
    charpolyRootCountIn_gershgorinRowUnion_eq_card A,
    charpolyRootCountIn_gershgorinColumnUnion_eq_card A,
    spectralRadius_le_min_max_row_column_sum A,
    spectralRadius_le_max_weighted_row_sum A,
    det_ne_zero_of_sum_row_lt_diag,
    det_ne_zero_of_sum_col_lt_diag,
    fun hd hp hs _ hμ => re_pos_of_mem_spectrum_of_strict_diagonal_dominance hd hp hs hμ,
    posDef_of_isHermitian_of_strict_diagonal_dominance,
    det_ne_zero_of_irreducible_weak_diagonal_dominance A,
    fun hi hd hp hw hs _ hμ =>
      re_pos_of_mem_spectrum_of_irreducible_weak_diagonal_dominance hi hd hp hw hs hμ,
    posDef_of_isHermitian_of_irreducible_weak_diagonal_dominance,
    posDef_of_isHermitian_of_strict_diagonal_dominance_complex,
    posDef_of_isHermitian_of_irreducible_weak_diagonal_dominance_complex⟩

end NLAlib
