import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Instances.Matrix

/-!
# The measurable space of matrices

`Matrix m n α` gets the product σ-algebra of `m → n → α` (`Matrix.instMeasurableSpace`), and,
for finite index types and a second-countable Borel space `α`, this is the Borel σ-algebra of
the topology `Matrix` carries (`Matrix.instBorelSpace`). Mathlib declares no measurable space on
`Matrix` (it is a non-reducible `def`, so the instance on `m → n → α` is not found); these are the
instances Mathlib would add, and they are global.

The topology in `Matrix.instBorelSpace` is the product topology `Matrix.topologicalSpace`. The
normed structures that Mathlib provides as scoped or local instances
(`Matrix.Norms.L2Operator`, `Matrix.frobeniusNormedAddCommGroup`, `Matrix.normedAddCommGroup`)
all replace their topology by this one definitionally, so the instance also applies when one of
them is open.

API: `Matrix.measurable_entry` and `Matrix.measurable_of`; the entrywise bridge
`Matrix.measurable_iff_entries`; `Measurable.matrix_mul`; `Matrix.measurable_transpose`,
`Matrix.measurable_conjTranspose`; and `Matrix.ofMeasurableEquiv`, `Matrix.of` as a measurable
equivalence. Candidate for `Mathlib/MeasureTheory/Constructions/Matrix.lean`.

Foundation change F2 (docs/FOUNDATIONS_BRIEF.md §2).
-/

open MeasureTheory

namespace Matrix

variable {β l m n α : Type*}

/-- The product σ-algebra on `Matrix m n α`, that of the array type `m → n → α`. -/
instance instMeasurableSpace [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
  MeasurableSpace.pi

/-- For finite index types and a second-countable Borel space `α`, the product σ-algebra on
`Matrix m n α` is the Borel σ-algebra of its (product) topology. -/
instance instBorelSpace [Fintype m] [Fintype n] [TopologicalSpace α] [MeasurableSpace α]
    [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  Pi.borelSpace

variable [MeasurableSpace α] [MeasurableSpace β]

/-- Each entry `A ↦ A i j` is measurable. -/
theorem measurable_entry (i : m) (j : n) : Measurable fun A : Matrix m n α => A i j :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- `Matrix.of` is measurable from the array type. -/
@[fun_prop]
theorem measurable_of : Measurable (of : (m → n → α) → Matrix m n α) :=
  measurable_id

/-- A matrix-valued map is measurable iff all its entries are. -/
theorem measurable_iff_entries {f : β → Matrix m n α} :
    Measurable f ↔ ∀ i j, Measurable fun x => f x i j := by
  refine ⟨fun hf i j => (measurable_entry i j).comp hf, fun h => ?_⟩
  exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

/-- `Matrix.of` as a measurable equivalence between the array type and `Matrix m n α`. -/
def ofMeasurableEquiv : (m → n → α) ≃ᵐ Matrix m n α where
  toEquiv := of
  measurable_toFun := measurable_of
  measurable_invFun := measurable_id

@[simp]
theorem coe_ofMeasurableEquiv : ⇑(ofMeasurableEquiv : (m → n → α) ≃ᵐ Matrix m n α) = of :=
  rfl

@[simp]
theorem coe_ofMeasurableEquiv_symm :
    ⇑(ofMeasurableEquiv : (m → n → α) ≃ᵐ Matrix m n α).symm = of.symm :=
  rfl

/-- Transposition is measurable. -/
@[fun_prop]
theorem measurable_transpose : Measurable (transpose : Matrix m n α → Matrix n m α) :=
  measurable_iff_entries.mpr fun i j => measurable_entry j i

/-- Conjugate transposition is measurable when `star` is continuous on a Borel space. -/
@[fun_prop]
theorem measurable_conjTranspose [Star α] [TopologicalSpace α] [ContinuousStar α]
    [BorelSpace α] : Measurable (conjTranspose : Matrix m n α → Matrix n m α) :=
  measurable_iff_entries.mpr fun i j => continuous_star.measurable.comp (measurable_entry j i)

end Matrix

/-- The product of measurable matrix-valued maps is measurable. -/
@[fun_prop]
theorem Measurable.matrix_mul {β l m n α : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype m] [NonUnitalNonAssocSemiring α] [MeasurableMul₂ α] [MeasurableAdd₂ α]
    {f : β → Matrix l m α} {g : β → Matrix m n α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x := by
  refine Matrix.measurable_iff_entries.mpr fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((Matrix.measurable_entry i k).comp hf).mul ((Matrix.measurable_entry k j).comp hg)
