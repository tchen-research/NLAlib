import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Finite group Fourier coordinates

The regular action, actual coefficient vectors and normalized Fourier matrices
are defined from a family of representations. Completeness means that every
finite-dimensional irreducible is equivalent to a listed representation;
orthogonality, dimension and Fourier unitarity are subsequent conclusions.
Source: finite Schur route for `gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix Kronecker
namespace NLAlib

universe u v
variable {G : Type u} [Group G]

/-- The left regular representation on functions, in the convention
`rho(h) f(g) = f(h⁻¹g)`. -/
def finiteGroupLeftRegularRepresentation : Representation ℂ G (G → ℂ) where
  toFun h :=
    { toFun := fun f g => f (h⁻¹ * g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' h k := by ext f g; simp [_root_.mul_inv_rev, mul_assoc]

/-- The regular action evaluated at one group element. -/
@[simp] theorem finiteGroupLeftRegularRepresentation_apply (h : G) (f : G → ℂ) (g : G) :
    finiteGroupLeftRegularRepresentation h f g = f (h⁻¹ * g) := rfl

/-- The counting-inner-product realization of the left regular representation. -/
def finiteGroupLeftRegularL2Representation [Fintype G] :
    Representation ℂ G (EuclideanSpace ℂ G) :=
  (((WithLp.linearEquiv 2 ℂ (G → ℂ)).symm.conjAlgEquiv ℂ).toMonoidHom).comp
    finiteGroupLeftRegularRepresentation

/-- Evaluation formula for the counting-inner-product regular action. -/
@[simp] theorem finiteGroupLeftRegularL2Representation_apply [Fintype G]
    (h : G) (f : EuclideanSpace ℂ G) (g : G) :
    finiteGroupLeftRegularL2Representation h f g = f (h⁻¹ * g) := rfl

variable {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]

/-- A complete family lists, up to equivalence, every finite-dimensional
irreducible complex representation. No coefficient or dimension identity is
part of this ordinary representation-theoretic completeness assumption. -/
def IsCompleteIrreducibleFamily (ρ : ∀ p, Representation ℂ G (D p → ℂ)) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ G V), Representation.IsIrreducible σ →
      ∃ p, Nonempty (Representation.Equiv (ρ p) σ)

/-- Representation label, multiplicity coordinate, and representation coordinate,
in that order. -/
abbrev FiniteGroupFourierIndex (D : P → Type u) := Σ p, D p × D p

/-- A matrix-coefficient vector at inverse group elements, with the counting
inner product. Its first matrix index will be the multiplicity coordinate. -/
def finiteGroupCoefficient [Fintype G]
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (t : FiniteGroupFourierIndex D) :
    EuclideanSpace ℂ G :=
  WithLp.toLp 2 (fun g => LinearMap.toMatrix' (ρ t.1 g⁻¹) t.2.1 t.2.2)

/-- The finite span of the actual matrix coefficients at inverse group elements. -/
def finiteGroupCoefficientSpan [Fintype G]
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) : Submodule ℂ (EuclideanSpace ℂ G) :=
  Submodule.span ℂ (Set.range (finiteGroupCoefficient ρ))

/-- The column Fourier matrix of normalized inverse-element coefficients. -/
def finiteGroupFourierMatrix [Fintype G]
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) :
    Matrix G (FiniteGroupFourierIndex D) ℂ :=
  fun g t => (Real.sqrt ((Fintype.card (D t.1) : ℝ) / Fintype.card G) : ℂ) *
    LinearMap.toMatrix' (ρ t.1 g⁻¹) t.2.1 t.2.2

/-- The normalized coefficient transform whose rows act on a circular complex
Gaussian coefficient vector. -/
def finiteGroupCoefficientTransform [Fintype G]
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) :
    Matrix (FiniteGroupFourierIndex D) G ℂ :=
  fun t g => (Real.sqrt ((Fintype.card (D t.1) : ℝ) / Fintype.card G) : ℂ) *
    LinearMap.toMatrix' (ρ t.1 g) t.2.1 t.2.2

/-- The actual permutation matrix of left translation on the finite group. -/
def finiteGroupRegularMatrix [Fintype G] [DecidableEq G] (h : G) : Matrix G G ℂ :=
  LinearMap.toMatrix' (finiteGroupLeftRegularRepresentation h)

/-- The Cayley convolution matrix for any complex coefficient vector. -/
def finiteGroupCayleyMatrix [Fintype G] [DecidableEq G] (z : G → ℂ) : Matrix G G ℂ :=
  ∑ g, z g • finiteGroupRegularMatrix g

/-- The unnormalized Fourier block associated with a representation. -/
def finiteGroupRepresentationBlock [Fintype G]
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (z : G → ℂ) (p : P) :
    Matrix (D p) (D p) ℂ := ∑ g, z g • LinearMap.toMatrix' (ρ p g)

/-- The Fourier block diagonal, with one copy for each multiplicity index. -/
def finiteGroupFourierBlocks [Fintype G] [DecidableEq P]
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (z : G → ℂ) :
    Matrix (FiniteGroupFourierIndex D) (FiniteGroupFourierIndex D) ℂ :=
  Matrix.blockDiagonal' (fun p =>
    (1 : Matrix (D p) (D p) ℂ) ⊗ₖ finiteGroupRepresentationBlock ρ z p)

end NLAlib
