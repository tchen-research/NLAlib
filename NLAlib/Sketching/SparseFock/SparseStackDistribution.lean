/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseStackModel
import NLAlib.ForMathlib.Probability.FiniteLaw
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Literal SparseStack finite distribution

Uniform signed hashes and coordinate independence define the actual finite sketch law and its sample transport.
Ported from `SparseFockFormal.SparseStackDistribution` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace SparseStackDistribution

open SparseStackModel

noncomputable section

/-- The positive and negative signed-basis choices have their literal finite enumeration.
Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
instance : Fintype Sign where
  elems := {.plus, .minus}
  complete x := by cases x <;> simp

/-- There are exactly two signed-basis sign values.
Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem card_sign : Fintype.card Sign = 2 := by decide

/-- One primitive, fully independent signed-hash selector.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev SignedHash (b : ℕ) := Fin b × Sign

/-- The primitive selector law: uniform row and independent Rademacher sign.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def selectorLaw (b : ℕ) (hb : 0 < b) : FiniteLaw (SignedHash b) where
  weight := fun _ => 1 / (2 * (b : ℝ))
  weight_nonneg := by
    intro _
    positivity
  sum_weight := by
    simp [Fintype.card_prod]
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    field_simp

/-- Literal sample space for all primitive selectors.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev RawSample (s b n : ℕ) := (Fin s × Fin n) → SignedHash b

/-- The actual product law.  Independence is supplied by the explicit product
weight, not by a proposition attached later.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rawSampleLaw (s b n : ℕ) (hb : 0 < b) : FiniteLaw (RawSample s b n) :=
  FiniteLaw.independentProduct (fun _ : Fin s × Fin n => selectorLaw b hb)

/-- Forget the paired presentation and obtain the exact `Sample` consumed by
the deterministic SparseStack matrix definitions.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def toSample {s b n : ℕ} (z : RawSample s b n) : Sample s b n where
  h := fun p => (z p).1
  sign := fun p => (z p).2

/-- Transporting a coordinate outcome to a SparseStack sample retains its hash coordinate.
Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem toSample_hash {s b n : ℕ} (z : RawSample s b n)
    (g : Fin s) (i : Fin n) :
    (toSample z).hash g i = (z (g, i)).1 := rfl

/-- Transporting a coordinate outcome to a SparseStack sample retains its sign coordinate.
Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem toSample_sign {s b n : ℕ} (z : RawSample s b n)
    (g : Fin s) (i : Fin n) :
    (toSample z).sgn g i = (z (g, i)).2 := rfl

/-- Each signed row choice has probability exactly `1/(2b)`.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selector_singleton {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    (selectorLaw b hb).prob {x} = 1 / (2 * (b : ℝ)) := by
  rw [FiniteLaw.prob_singleton]
  rfl

/-- Each primitive selector in the full sample has the prescribed marginal.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rawSample_coordinate_singleton {s b n : ℕ} (hb : 0 < b)
    (p : Fin s × Fin n) (x : SignedHash b) :
    (rawSampleLaw s b n hb).prob {z | z p = x} = 1 / (2 * (b : ℝ)) := by
  simpa [rawSampleLaw, selectorLaw] using
    (FiniteLaw.prob_independentProduct_eq
      (fun _ : Fin s × Fin n => selectorLaw b hb) p x)

/-- Exact factorization of arbitrary coordinate events for the SparseStack
primitive sample.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rawSample_cylinder {s b n : ℕ} (hb : 0 < b)
    (events : (Fin s × Fin n) → Set (SignedHash b)) :
    (rawSampleLaw s b n hb).prob (FiniteLaw.cylinder events) =
      ∏ p, (selectorLaw b hb).prob (events p) := by
  exact FiniteLaw.prob_independentProduct_cylinder
    (fun _ : Fin s × Fin n => selectorLaw b hb) events

/-- The hash marginal is uniform.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selector_hash_uniform {b : ℕ} (hb : 0 < b) (a : Fin b) :
    (selectorLaw b hb).prob {x | x.1 = a} = 1 / (b : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  simp only [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator, selectorLaw,
    Set.mem_ofPred_eq]
  rw [Fintype.sum_prod_type]
  simp
  field_simp

/-- The sign marginal is Rademacher.

Source: ported from `SparseFockFormal.SparseStackDistribution`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selector_sign_uniform {b : ℕ} (hb : 0 < b) (e : Sign) :
    (selectorLaw b hb).prob {x | x.2 = e} = 1 / 2 := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  cases e <;>
    simp only [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator, selectorLaw,
      Set.mem_ofPred_eq] <;>
    rw [Fintype.sum_prod_type] <;>
    simp <;>
    field_simp

end

end SparseStackDistribution

end NLAlib.SparseFock
