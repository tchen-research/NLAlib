/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactConditionalSupport

set_option autoImplicit false

/-!
# Exact-s conditional coordinate symmetries

Coordinate flips and compensating support swaps identify conditional coordinate moments.
Ported from `SparseFockFormal.UniformExactSBarycenter` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseStackModel

noncomputable section

/-! ## Exact disintegration -/

/-- Mask that flips exactly one physical row.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flipMask {m : ℕ} (q : Fin m) : Fin m → Sign := fun r =>
  if r = q then .minus else .plus

/-- A one-coordinate sign mask is negative at its marked coordinate.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flipMask_same {m : ℕ} (q : Fin m) :
    flipMask q q = .minus := by simp [flipMask]

/-- A one-coordinate sign mask is positive at every other coordinate.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem flipMask_of_ne {m : ℕ} {q r : Fin m} (hrq : r ≠ q) :
    flipMask q r = .plus := by simp [flipMask, hrq]

/-- The iid outcome transformation flips exactly one flattened coordinate sign.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flipYAt {b s : ℕ} (q : Fin (s * b)) (y : NestedY b s) : NestedY b s :=
  transformY (Equiv.refl _) (flipMask q) y

/-- A single flattened-coordinate sign flip is an equivalence of iid outcomes.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flipYAtEquiv {b s : ℕ} (q : Fin (s * b)) :
    NestedY b s ≃ NestedY b s :=
  transformYEquiv (Equiv.refl _) (flipMask q)

/-- A single-coordinate flip negates that flattened coordinate value.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flatYValue_flipYAt_same {b s : ℕ}
    (q : Fin (s * b)) (y : NestedY b s) :
    flatYValue (flipYAt q y) q = -flatYValue y q := by
  simp [flipYAt, flatYValue, flipMask, actOutcome, yValue_negateOutcome]

/-- Flipping outside exact support leaves all active column values unchanged.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transformColumn_flip_off_sameActive {b s : ℕ}
    (x : ExactColumn (s * b) s) (q : Fin (s * b))
    (hq : q ∉ (x.1 : Finset (Fin (s * b)))) :
    (x.1 : Finset (Fin (s * b))) =
        ((transformColumn (Equiv.refl _) (flipMask q) x).1 :
          Finset (Fin (s * b))) ∧
      ∀ r ∈ (x.1 : Finset (Fin (s * b))),
        x.2 r = (transformColumn (Equiv.refl _) (flipMask q) x).2 r := by
  classical
  constructor
  · simp [transformColumn, transformSupport]
  · intro r hr
    have hrq : r ≠ q := by
      intro h
      subst r
      exact hq hr
    simp [transformColumn, flipMask_of_ne hrq]

/-- Flipping an iid coordinate outside the exact-column support preserves joint-law mass.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumnLaw_weight_flipYAt_off {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (q : Fin (s * b))
    (hq : q ∉ (x.1 : Finset (Fin (s * b)))) (y : NestedY b s) :
    (jointColumnLaw hb hs).weight (flipYAt q y, x) =
      (jointColumnLaw hb hs).weight (y, x) := by
  let z := transformColumn (Equiv.refl _) (flipMask q) x
  have hz := transformColumn_flip_off_sameActive x q hq
  calc
    (jointColumnLaw hb hs).weight (flipYAt q y, x) =
        (jointColumnLaw hb hs).weight (flipYAt q y, z) :=
      jointColumnLaw_weight_congr_column hb hs (flipYAt q y) x z hz.1 hz.2
    _ = (jointColumnLaw hb hs).weight (y, x) := by
      exact jointColumnLaw_weight_transform hb hs
        (Equiv.refl _) (flipMask q) y x

/-- Unnormalized first moment of one physical iid coordinate in an X-fiber.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def coordinateFiberMoment {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r : Fin (s * b)) : ℝ :=
  ∑ y, (jointColumnLaw hb hs).weight (y, x) * flatYValue y r

/-- Every coordinate outside exact-column support has zero signed joint fiber moment.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinateFiberMoment_off {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (q : Fin (s * b))
    (hq : q ∉ (x.1 : Finset (Fin (s * b)))) :
    coordinateFiberMoment hb hs x q = 0 := by
  have hneg : coordinateFiberMoment hb hs x q =
      -coordinateFiberMoment hb hs x q := by
    calc
      coordinateFiberMoment hb hs x q =
          ∑ y, (jointColumnLaw hb hs).weight (flipYAt q y, x) *
            flatYValue (flipYAt q y) q := by
        exact ((flipYAtEquiv q).sum_comp
          (fun y => (jointColumnLaw hb hs).weight (y, x) *
            flatYValue y q)).symm
      _ = ∑ y, -((jointColumnLaw hb hs).weight (y, x) *
            flatYValue y q) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [jointColumnLaw_weight_flipYAt_off hb hs x q hq,
          flatYValue_flipYAt_same]
        ring
      _ = -coordinateFiberMoment hb hs x q := by
        simp [coordinateFiberMoment]
  linarith

/-- Mask which makes a row permutation fix every stored sign of a chosen
exact column.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def stabilizerMask {m s : ℕ} (x : ExactColumn m s)
    (pi : Equiv.Perm (Fin m)) : Fin m → Sign :=
  fun r => signMul (x.2 r) (x.2 (pi.symm r))

/-- The compensating signed permutation stabilizes the original exact column.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transformColumn_stabilizer {m s : ℕ}
    (x : ExactColumn m s) (pi : Equiv.Perm (Fin m))
    (hsupport : (x.1 : Finset (Fin m)).map pi.toEmbedding =
      (x.1 : Finset (Fin m))) :
    transformColumn pi (stabilizerMask x pi) x = x := by
  apply Prod.ext
  · apply Subtype.ext
    exact hsupport
  · funext r
    simp [transformColumn, stabilizerMask]

/-- Swapping two selected support coordinates preserves the support set.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem swap_maps_support_self {m s : ℕ} (x : ExactColumn m s)
    (r t : Fin m) (hr : r ∈ (x.1 : Finset (Fin m)))
    (ht : t ∈ (x.1 : Finset (Fin m))) :
    (x.1 : Finset (Fin m)).map (Equiv.swap r t).toEmbedding =
      (x.1 : Finset (Fin m)) := by
  ext u
  rw [show u ∈ (x.1 : Finset (Fin m)).map (Equiv.swap r t).toEmbedding ↔
      (Equiv.swap r t).symm u ∈ (x.1 : Finset (Fin m)) by simp]
  change Equiv.swap r t u ∈ (x.1 : Finset (Fin m)) ↔
    u ∈ (x.1 : Finset (Fin m))
  by_cases hur : u = r
  · subst u
    simp [hr, ht]
  · by_cases hut : u = t
    · subst u
      simp [hr, ht]
    · rw [Equiv.swap_apply_of_ne_of_ne hur hut]

/-- The compensated swap of two active coordinates leaves the exact column unchanged.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transformColumn_swap_eq {m s : ℕ} (x : ExactColumn m s)
    (r t : Fin m) (hr : r ∈ (x.1 : Finset (Fin m)))
    (ht : t ∈ (x.1 : Finset (Fin m))) :
    transformColumn (Equiv.swap r t)
      (stabilizerMask x (Equiv.swap r t)) x = x :=
  transformColumn_stabilizer x (Equiv.swap r t)
    (swap_maps_support_self x r t hr ht)

/-- A signed permutation transforms the flattened real iid values by the same coordinate action.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flatYValue_transformY {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) (r : Fin (s * b)) :
    flatYValue (transformY pi eps y) r =
      (eps r).val * flatYValue y (pi.symm r) := by
  simp [flatYValue]

/-- Active coordinate fiber moments transform under the compensated support swap.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinateFiberMoment_swap {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r t : Fin (s * b))
    (hr : r ∈ (x.1 : Finset (Fin (s * b))))
    (ht : t ∈ (x.1 : Finset (Fin (s * b)))) :
    coordinateFiberMoment hb hs x t =
      (stabilizerMask x (Equiv.swap r t) t).val *
        coordinateFiberMoment hb hs x r := by
  let pi : Equiv.Perm (Fin (s * b)) := Equiv.swap r t
  let eps : Fin (s * b) → Sign := stabilizerMask x pi
  have hfix : transformColumn pi eps x = x := by
    exact transformColumn_swap_eq x r t hr ht
  calc
    coordinateFiberMoment hb hs x t =
        ∑ y, (jointColumnLaw hb hs).weight (transformY pi eps y, x) *
          flatYValue (transformY pi eps y) t := by
      exact ((transformYEquiv pi eps).sum_comp
        (fun y => (jointColumnLaw hb hs).weight (y, x) *
          flatYValue y t)).symm
    _ = ∑ y, (jointColumnLaw hb hs).weight (y, x) *
          ((eps t).val * flatYValue y r) := by
      apply Finset.sum_congr rfl
      intro y _
      have hw := jointColumnLaw_weight_transform hb hs pi eps y x
      rw [hfix] at hw
      rw [hw, flatYValue_transformY]
      simp [pi]
    _ = (eps t).val * coordinateFiberMoment hb hs x r := by
      rw [coordinateFiberMoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (stabilizerMask x (Equiv.swap r t) t).val *
        coordinateFiberMoment hb hs x r := rfl

/-- Sign-aligned active coordinate fiber moments are equal.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem aligned_coordinateFiberMoment_eq {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r t : Fin (s * b))
    (hr : r ∈ (x.1 : Finset (Fin (s * b))))
    (ht : t ∈ (x.1 : Finset (Fin (s * b)))) :
    columnValue x r * coordinateFiberMoment hb hs x r =
      columnValue x t * coordinateFiberMoment hb hs x t := by
  have hr' : r ∈ x.1 := Set.powersetCard.mem_coe_iff.mp hr
  have ht' : t ∈ x.1 := Set.powersetCard.mem_coe_iff.mp ht
  rw [coordinateFiberMoment_swap hb hs x r t hr ht,
    columnValue_of_mem x hr', columnValue_of_mem x ht']
  simp [stabilizerMask]
  calc
    (x.2 r).val * coordinateFiberMoment hb hs x r =
        1 * ((x.2 r).val * coordinateFiberMoment hb hs x r) := by ring
    _ = (x.2 t).val ^ 2 *
        ((x.2 r).val * coordinateFiberMoment hb hs x r) := by
      rw [Sign.val_sq]
    _ = (x.2 t).val *
        ((x.2 t).val * (x.2 r).val * coordinateFiberMoment hb hs x r) := by
      ring

end

end NLAlib.SparseFock.UniformExactS
