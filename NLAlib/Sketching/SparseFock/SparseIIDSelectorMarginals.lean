/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseIIDSelectionKernel

set_option autoImplicit false

/-!
# Uniform selector marginal

Negation and coordinate-swap symmetries identify the true selector marginal.
Ported from `SparseFockFormal.SparseIIDCoupling` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace

namespace NLAlib.SparseFock

namespace SparseIIDCoupling

open ParsevalFrame SparseStackModel SparseStackDistribution

noncomputable section

/-- The joint selector/iid law is iid mass times conditional selector weight.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem jointColumnLaw_weight {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    (jointColumnLaw hb).weight (y, x) =
      (yVectorLaw b hb).weight y * kernelWeight hb y x := rfl

/-! ## Symmetry and the selector marginal -/

/-- Negating a ternary outcome preserves its coordinate mass.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem mass_negateOutcome (b : ℕ) (z : EtaOutcome) :
    TernaryJacobi.mass b (negateOutcome z) = TernaryJacobi.mass b z := by
  cases z <;> rfl

/-- Flip every nonzero sign in an iid vector.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def negateY {b : ℕ} (y : YVector b) : YVector b :=
  fun a => negateOutcome (y a)

/-- Negating every iid vector coordinate twice returns the original vector.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem negateY_involutive {b : ℕ} (y : YVector b) :
    negateY (negateY y) = y := by
  funext a
  simp [negateY]

/-- Coordinatewise outcome negation is an equivalence of the iid outcome type.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def negateYEquiv (b : ℕ) : YVector b ≃ YVector b where
  toFun := negateY
  invFun := negateY
  left_inv := negateY_involutive
  right_inv := negateY_involutive

/-- The iid vector law is invariant under coordinatewise negation.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yVectorLaw_weight_negateY {b : ℕ} (hb : 0 < b) (y : YVector b) :
    (yVectorLaw b hb).weight (negateY y) = (yVectorLaw b hb).weight y := by
  simp only [yVectorLaw_weight, negateY]
  apply Finset.prod_congr rfl
  intro a _ha
  exact mass_negateOutcome b (y a)

/-- Coordinatewise negation retains the iid support set.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem support_negateY {b : ℕ} (y : YVector b) : support (negateY y) = support y := by
  ext a
  rw [mem_support, mem_support]
  cases h : y a <;> simp [negateY, negateOutcome, h]

/-- Coordinatewise negation retains the iid support cardinality.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem supportSize_negateY {b : ℕ} (y : YVector b) :
    supportSize (negateY y) = supportSize y := by
  simp [supportSize, support_negateY]

/-- Simultaneously negating the iid vector and selector sign preserves the selection weight.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem kernelWeight_negateY {b : ℕ} (hb : 0 < b)
    (y : YVector b) (a : Fin b) (e : Sign) :
    kernelWeight hb (negateY y) (a, flipSign e) = kernelWeight hb y (a, e) := by
  classical
  cases e <;> cases h : y a <;>
    simp [kernelWeight, supportSize_negateY, selectorMatches, negateY,
      flipSign, outcomeOfSign, negateOutcome, h, selectorLaw]

/-- Permute two coordinate positions.  `Equiv.swap` is its own inverse.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def swapY {b : ℕ} (a c : Fin b) (y : YVector b) : YVector b :=
  fun k => y (Equiv.swap a c k)

/-- Swapping two iid coordinates twice returns the original vector.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem swapY_involutive {b : ℕ} (a c : Fin b) (y : YVector b) :
    swapY a c (swapY a c y) = y := by
  funext k
  simp [swapY]

/-- Swapping two iid coordinates is an equivalence of the outcome type.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def swapYEquiv {b : ℕ} (a c : Fin b) : YVector b ≃ YVector b where
  toFun := swapY a c
  invFun := swapY a c
  left_inv := swapY_involutive a c
  right_inv := swapY_involutive a c

/-- The iid vector law is invariant under coordinate swaps.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yVectorLaw_weight_swapY {b : ℕ} (hb : 0 < b)
    (a c : Fin b) (y : YVector b) :
    (yVectorLaw b hb).weight (swapY a c y) = (yVectorLaw b hb).weight y := by
  simp only [yVectorLaw_weight, swapY]
  exact Function.Bijective.prod_comp (Equiv.swap a c).bijective
    (fun k => TernaryJacobi.mass b (y k))

/-- The iid support cardinality is the sum of nonzero-coordinate indicators.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem supportSize_eq_sum {b : ℕ} (y : YVector b) :
    supportSize y = ∑ a, if y a = .zero then 0 else 1 := by
  classical
  rw [supportSize, support]
  symm
  simpa using
    (Finset.sum_boole (R := ℕ) (fun a : Fin b => y a ≠ .zero) Finset.univ)

/-- Swapping coordinates preserves iid support cardinality.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem supportSize_swapY {b : ℕ} (a c : Fin b) (y : YVector b) :
    supportSize (swapY a c y) = supportSize y := by
  rw [supportSize_eq_sum, supportSize_eq_sum]
  change (∑ k, if y (Equiv.swap a c k) = .zero then 0 else 1) =
    ∑ k, if y k = .zero then 0 else 1
  exact Function.Bijective.sum_comp (Equiv.swap a c).bijective
    (fun k => if y k = .zero then 0 else 1)

/-- Swapping iid coordinates and the selector label preserves the selection weight.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem kernelWeight_swapY {b : ℕ} (hb : 0 < b)
    (y : YVector b) (a c : Fin b) (e : Sign) :
    kernelWeight hb (swapY a c y) (c, e) = kernelWeight hb y (a, e) := by
  classical
  cases e <;> cases h : y a <;>
    simp [kernelWeight, supportSize_swapY, selectorMatches, swapY,
      outcomeOfSign, h, selectorLaw]

/-- The `X`-fiber mass of the one-column joint law.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def xMarginal {b : ℕ} (hb : 0 < b) (x : SignedHash b) : ℝ :=
  ∑ y, (jointColumnLaw hb).weight (y, x)

/-- The selector marginal is invariant under coordinate swaps.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_swap {b : ℕ} (hb : 0 < b)
    (a c : Fin b) (e : Sign) :
    xMarginal hb (c, e) = xMarginal hb (a, e) := by
  calc
    xMarginal hb (c, e) = ∑ y, (jointColumnLaw hb).weight (y, (c, e)) := rfl
    _ = ∑ y, (jointColumnLaw hb).weight (swapY a c y, (c, e)) := by
      exact ((swapYEquiv a c).sum_comp
        (fun y => (jointColumnLaw hb).weight (y, (c, e)))).symm
    _ = ∑ y, (jointColumnLaw hb).weight (y, (a, e)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [jointColumnLaw_weight, jointColumnLaw_weight,
        yVectorLaw_weight_swapY hb a c y, kernelWeight_swapY hb y a c e]
    _ = xMarginal hb (a, e) := rfl

/-- The selector marginal is invariant under sign reversal.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_flip {b : ℕ} (hb : 0 < b) (a : Fin b) (e : Sign) :
    xMarginal hb (a, flipSign e) = xMarginal hb (a, e) := by
  calc
    xMarginal hb (a, flipSign e) =
        ∑ y, (jointColumnLaw hb).weight (y, (a, flipSign e)) := rfl
    _ = ∑ y, (jointColumnLaw hb).weight (negateY y, (a, flipSign e)) := by
      exact ((negateYEquiv b).sum_comp
        (fun y => (jointColumnLaw hb).weight (y, (a, flipSign e)))).symm
    _ = ∑ y, (jointColumnLaw hb).weight (y, (a, e)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [jointColumnLaw_weight, jointColumnLaw_weight,
        yVectorLaw_weight_negateY hb y, kernelWeight_negateY hb y a e]
    _ = xMarginal hb (a, e) := rfl

/-- Every signed selector label has the same marginal mass.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_constant {b : ℕ} (hb : 0 < b) (x z : SignedHash b) :
    xMarginal hb x = xMarginal hb z := by
  rcases x with ⟨a, e⟩
  rcases z with ⟨c, f⟩
  cases e <;> cases f
  · exact (xMarginal_swap hb a c .plus).symm
  · exact (xMarginal_swap hb a c .plus).symm.trans
      (by simpa [flipSign] using (xMarginal_flip hb c .plus).symm)
  · exact (xMarginal_swap hb a c .minus).symm.trans
      (by simpa [flipSign] using xMarginal_flip hb c .plus)
  · exact (xMarginal_swap hb a c .minus).symm

/-- The selector marginal masses sum to one.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_xMarginal {b : ℕ} (hb : 0 < b) :
    ∑ x, xMarginal hb x = 1 := by
  calc
    (∑ x, xMarginal hb x) =
        ∑ y, ∑ x, (jointColumnLaw hb).weight (y, x) := by
      simp only [xMarginal]
      exact Finset.sum_comm
    _ = ∑ z : YVector b × SignedHash b, (jointColumnLaw hb).weight z := by
      rw [Fintype.sum_prod_type]
    _ = 1 := (jointColumnLaw hb).sum_weight

/-- The selected signed coordinate is exactly uniform on the `2b` selectors.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_eq_selectorWeight {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    xMarginal hb x = (selectorLaw b hb).weight x := by
  have hconst : ∀ z : SignedHash b, xMarginal hb z = xMarginal hb x :=
    fun z => xMarginal_constant hb z x
  have hcard : Fintype.card (SignedHash b) = 2 * b := by
    simp [SignedHash, Fintype.card_prod, SparseStackDistribution.card_sign,
      Nat.mul_comm]
  have hsum : (2 * (b : ℝ)) * xMarginal hb x = 1 := by
    calc
      (2 * (b : ℝ)) * xMarginal hb x =
          (Fintype.card (SignedHash b) : ℝ) * xMarginal hb x := by
        rw [hcard]
        push_cast
        ring
      _ = ∑ z : SignedHash b, xMarginal hb x := by simp
      _ = ∑ z : SignedHash b, xMarginal hb z := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact (hconst z).symm
      _ = 1 := sum_xMarginal hb
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  rw [selectorLaw]
  dsimp
  apply (eq_div_iff (by positivity : (2 * (b : ℝ)) ≠ 0)).2
  nlinarith

end

end SparseIIDCoupling

end NLAlib.SparseFock
