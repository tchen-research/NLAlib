/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.UniformExactSCoupling
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Signed coordinate actions on exact sparse columns

Literal sign multiplication, coordinate permutations, and their inverse actions.
Ported from `SparseFockFormal.UniformExactSSymmetry` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseStackModel

noncomputable section

/-! ## The signed coordinate action -/

/-- Multiplication in the two-point sign group.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def signMul : Sign → Sign → Sign
  | .plus, e => e
  | .minus, .plus => .minus
  | .minus, .minus => .plus

/-- The positive sign is a left identity for sign multiplication.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_plus_left (e : Sign) : signMul .plus e = e := rfl

/-- The positive sign is a right identity for sign multiplication.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_plus_right (e : Sign) : signMul e .plus = e := by
  cases e <;> rfl

/-- Every sign multiplied by itself is positive.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_self (e : Sign) : signMul e e = .plus := by
  cases e <;> rfl

/-- Sign multiplication is associative.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_assoc (e f g : Sign) :
    signMul (signMul e f) g = signMul e (signMul f g) := by
  cases e <;> cases f <;> cases g <;> rfl

/-- Multiplying twice on the left by the same sign cancels.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_left_cancel_self (e f : Sign) :
    signMul e (signMul e f) = f := by
  cases e <;> cases f <;> rfl

/-- Multiplying twice on the right by the same sign cancels.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_right_cancel_self (e f : Sign) :
    signMul (signMul e f) f = e := by
  cases e <;> cases f <;> rfl

/-- The real value of sign multiplication is the product of real sign values.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem signMul_val (e f : Sign) :
    (signMul e f).val = e.val * f.val := by
  cases e <;> cases f <;> norm_num [signMul, Sign.val]

/-- The action of a sign on a ternary atom.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def actOutcome : Sign → EtaOutcome → EtaOutcome
  | .plus, z => z
  | .minus, z => negateOutcome z

/-- The positive sign acts trivially on ternary outcomes.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem actOutcome_plus (z : EtaOutcome) : actOutcome .plus z = z := rfl

/-- Acting twice by one sign returns the original ternary outcome.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem actOutcome_involutive (e : Sign) (z : EtaOutcome) :
    actOutcome e (actOutcome e z) = z := by
  cases e <;> simp [actOutcome]

/-- Ternary sign actions compose by sign multiplication.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem actOutcome_signMul (e f : Sign) (z : EtaOutcome) :
    actOutcome (signMul e f) z = actOutcome e (actOutcome f z) := by
  cases e <;> cases f <;> simp [signMul, actOutcome]

/-- A signed ternary outcome is zero precisely when the original outcome is zero.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem actOutcome_eq_zero_iff (e : Sign) (z : EtaOutcome) :
    actOutcome e z = .zero ↔ z = .zero := by
  cases e <;> cases z <;> simp [actOutcome, negateOutcome]

/-- A signed ternary outcome is nonzero precisely when the original outcome is nonzero.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem actOutcome_ne_zero_iff (e : Sign) (z : EtaOutcome) :
    actOutcome e z ≠ .zero ↔ z ≠ .zero := by
  rw [ne_eq, ne_eq, not_congr (actOutcome_eq_zero_iff e z)]

/-- A signed ternary action multiplies the real coordinate value by that sign.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem yValue_actOutcome (e : Sign) (z : EtaOutcome) :
    yValue (actOutcome e z) = e.val * yValue z := by
  cases e <;> cases z <;> norm_num [actOutcome, negateOutcome, yValue, Sign.val]

/-- Embedding a sign product agrees with acting on the embedded second sign.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem outcomeOfSign_signMul (e f : Sign) :
    outcomeOfSign (signMul e f) = actOutcome e (outcomeOfSign f) := by
  cases e <;> cases f <;> rfl

/-- Every ternary coordinate mass is invariant under sign action.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem mass_actOutcome (b : ℕ) (e : Sign) (z : EtaOutcome) :
    TernaryJacobi.mass b (actOutcome e z) = TernaryJacobi.mass b z := by
  cases e
  · rfl
  · exact mass_negateOutcome b z

/-! ## Simultaneous action on iid and exact columns -/

/-- Apply a signed coordinate permutation to a nested iid column.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def transformY {b s : ℕ} (pi : Equiv.Perm (Fin (s * b)))
    (eps : Fin (s * b) → Sign) (y : NestedY b s) : NestedY b s :=
  fun g a =>
    actOutcome (eps (finProdFinEquiv (g, a)))
      (flatOutcome y (pi.symm (finProdFinEquiv (g, a))))

/-- The transformed flattened iid coordinate is the permuted original coordinate with its sign action.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flatOutcome_transformY {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) (r : Fin (s * b)) :
    flatOutcome (transformY pi eps y) r =
      actOutcome (eps r) (flatOutcome y (pi.symm r)) := by
  obtain ⟨g, a⟩ := finProdFinEquiv.surjective r
  subst r
  rw [flatOutcome_pair]
  rfl

/-- The inverse mask for a signed coordinate permutation.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def inverseMask {m : ℕ} (pi : Equiv.Perm (Fin m))
    (eps : Fin m → Sign) : Fin m → Sign :=
  fun r => eps (pi r)

/-- Applying the inverse signed permutation after the forward iid transformation restores the vector.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transformY_inverse_left {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    transformY pi.symm (inverseMask pi eps) (transformY pi eps y) = y := by
  funext g a
  have h := flatOutcome_transformY pi.symm (inverseMask pi eps)
    (transformY pi eps y) (finProdFinEquiv (g, a))
  simpa [inverseMask] using h

/-- Applying the forward signed permutation after the inverse iid transformation restores the vector.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transformY_inverse_right {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    transformY pi eps (transformY pi.symm (inverseMask pi eps) y) = y := by
  funext g a
  have h := flatOutcome_transformY pi eps
    (transformY pi.symm (inverseMask pi eps) y) (finProdFinEquiv (g, a))
  simpa [inverseMask] using h

/-- Signed coordinate permutations are equivalences of iid outcomes.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def transformYEquiv {b s : ℕ} (pi : Equiv.Perm (Fin (s * b)))
    (eps : Fin (s * b) → Sign) : NestedY b s ≃ NestedY b s where
  toFun := transformY pi eps
  invFun := transformY pi.symm (inverseMask pi eps)
  left_inv := transformY_inverse_left pi eps
  right_inv := transformY_inverse_right pi eps

/-- Apply the underlying coordinate permutation to an exact support.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def transformSupport {m s : ℕ} (pi : Equiv.Perm (Fin m))
    (S : ExactSupport m s) : ExactSupport m s :=
  ⟨(S : Finset (Fin m)).map pi.toEmbedding, by simp⟩

/-- A coordinate belongs to transformed exact support precisely when its inverse image belongs to original support.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem mem_transformSupport {m s : ℕ} (pi : Equiv.Perm (Fin m))
    (S : ExactSupport m s) (r : Fin m) :
    r ∈ (transformSupport pi S : Finset (Fin m)) ↔ pi.symm r ∈ (S : Finset (Fin m)) := by
  simp [transformSupport]

/-- Apply a signed coordinate permutation to an exact column.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def transformColumn {m s : ℕ} (pi : Equiv.Perm (Fin m))
    (eps : Fin m → Sign) (x : ExactColumn m s) : ExactColumn m s :=
  (transformSupport pi x.1, fun r => signMul (eps r) (x.2 (pi.symm r)))

/-- A signed-permuted exact column evaluates as its signed-permuted original coordinate value.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem columnValue_transformColumn {m s : ℕ}
    (pi : Equiv.Perm (Fin m)) (eps : Fin m → Sign)
    (x : ExactColumn m s) (r : Fin m) :
    columnValue (transformColumn pi eps x) r =
      (eps r).val * columnValue x (pi.symm r) := by
  classical
  by_cases hr : pi.symm r ∈ x.1
  · have hrt : r ∈ (transformColumn pi eps x).1 := by
      exact Set.powersetCard.mem_coe_iff.mp
        ((mem_transformSupport pi x.1 r).mpr
          (Set.powersetCard.mem_coe_iff.mpr hr))
    rw [columnValue_of_mem _ hrt, columnValue_of_mem x hr]
    exact signMul_val _ _
  · have hrt : r ∉ (transformColumn pi eps x).1 := by
      intro h
      apply hr
      exact Set.powersetCard.mem_coe_iff.mp
        ((mem_transformSupport pi x.1 r).mp
          (Set.powersetCard.mem_coe_iff.mpr h))
    rw [columnValue_of_notMem _ hrt, columnValue_of_notMem x hr]
    ring

/-- Applying the inverse exact-column transformation after the forward one restores the column.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transformColumn_inverse_left {m s : ℕ}
    (pi : Equiv.Perm (Fin m)) (eps : Fin m → Sign)
    (x : ExactColumn m s) :
    transformColumn pi.symm (inverseMask pi eps) (transformColumn pi eps x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    ext r
    simp [transformColumn, transformSupport]
  · funext r
    simp [transformColumn, inverseMask]

/-- Applying the forward exact-column transformation after the inverse one restores the column.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transformColumn_inverse_right {m s : ℕ}
    (pi : Equiv.Perm (Fin m)) (eps : Fin m → Sign)
    (x : ExactColumn m s) :
    transformColumn pi eps
      (transformColumn pi.symm (inverseMask pi eps) x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    ext r
    simp [transformColumn, transformSupport]
  · funext r
    simp [transformColumn, inverseMask]

end

end NLAlib.SparseFock.UniformExactS
