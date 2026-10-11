/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseIIDSelectorMarginals

set_option autoImplicit false

/-!
# Conditional iid selector barycenter

True conditional laws and coordinate-flip identities prove the corrected iid barycenter.
Ported from `SparseFockFormal.SparseIIDCoupling` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace

namespace NLAlib.SparseFock

namespace SparseIIDCoupling

open ParsevalFrame SparseStackModel SparseStackDistribution

noncomputable section

/-- The second marginal of the joint law is precisely `selectorLaw`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumn_x_marginal {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    (jointColumnLaw hb).prob {z | z.2 = x} = (selectorLaw b hb).weight x := by
  classical
  calc
    (jointColumnLaw hb).prob {z | z.2 = x} = xMarginal hb x := by
      rw [FiniteLaw.prob, FiniteLaw.expect, Fintype.sum_prod_type]
      change (∑ y, ∑ x', (jointColumnLaw hb).weight (y, x') *
        FiniteLaw.indicator {z : YVector b × SignedHash b | z.2 = x} (y, x')) =
          ∑ y, (jointColumnLaw hb).weight (y, x)
      apply Finset.sum_congr rfl
      intro y _hy
      simp [FiniteLaw.indicator]
    _ = (selectorLaw b hb).weight x := xMarginal_eq_selectorWeight hb x

/-! ## The exact conditional law `Y | X=x` and its barycenter -/

/-- Every selector label has positive mass at positive block size.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selectorWeight_pos {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    0 < (selectorLaw b hb).weight x := by
  rw [selectorLaw]
  dsimp
  positivity

/-- The normalized conditional law obtained from the explicit joint fiber.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def conditionalYLaw {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    FiniteLaw (YVector b) where
  weight y := (jointColumnLaw hb).weight (y, x) /
    (selectorLaw b hb).weight x
  weight_nonneg y := div_nonneg ((jointColumnLaw hb).weight_nonneg (y, x))
    (selectorWeight_pos hb x).le
  sum_weight := by
    rw [← Finset.sum_div]
    change xMarginal hb x / (selectorLaw b hb).weight x = 1
    rw [xMarginal_eq_selectorWeight hb x]
    exact div_self (ne_of_gt (selectorWeight_pos hb x))

/-- The conditional iid-vector law is the joint mass divided by positive selector mass.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem conditionalYLaw_weight {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (y : YVector b) :
    (conditionalYLaw hb x).weight y =
      (jointColumnLaw hb).weight (y, x) / (selectorLaw b hb).weight x := rfl

/-- Bayes/disintegration identity for the one-column joint law.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumn_disintegrates {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    (jointColumnLaw hb).weight (y, x) =
      (selectorLaw b hb).weight x * (conditionalYLaw hb x).weight y := by
  rw [conditionalYLaw_weight]
  field_simp [ne_of_gt (selectorWeight_pos hb x)]

/-- Flip one coordinate of an iid vector.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flipAt {b : ℕ} (a : Fin b) (y : YVector b) : YVector b :=
  by
    classical
    exact fun k => if k = a then negateOutcome (y k) else y k

/-- Flipping one iid coordinate negates the outcome at that coordinate.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flipAt_apply_same {b : ℕ} (a : Fin b) (y : YVector b) :
    flipAt a y a = negateOutcome (y a) := by
  simp [flipAt]

/-- Flipping one iid coordinate leaves each distinct coordinate unchanged.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem flipAt_apply_of_ne {b : ℕ} {a k : Fin b} (hka : k ≠ a) (y : YVector b) :
    flipAt a y k = y k := by
  simp [flipAt, hka]

/-- Flipping one iid coordinate twice returns the original vector.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flipAt_involutive {b : ℕ} (a : Fin b) (y : YVector b) :
    flipAt a (flipAt a y) = y := by
  classical
  funext k
  by_cases hka : k = a
  · subst k
    simp
  · simp [flipAt, hka]

/-- A single-coordinate outcome flip is an equivalence of the iid outcome type.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flipAtEquiv {b : ℕ} (a : Fin b) : YVector b ≃ YVector b where
  toFun := flipAt a
  invFun := flipAt a
  left_inv := flipAt_involutive a
  right_inv := flipAt_involutive a

/-- A single-coordinate sign flip preserves the iid law weight.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yVectorLaw_weight_flipAt {b : ℕ} (hb : 0 < b)
    (a : Fin b) (y : YVector b) :
    (yVectorLaw b hb).weight (flipAt a y) = (yVectorLaw b hb).weight y := by
  simp only [yVectorLaw_weight]
  apply Finset.prod_congr rfl
  intro k _hk
  by_cases hka : k = a
  · subst k
    simp [mass_negateOutcome]
  · simp [flipAt_apply_of_ne hka]

/-- A single-coordinate sign flip preserves support cardinality.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem supportSize_flipAt {b : ℕ} (a : Fin b) (y : YVector b) :
    supportSize (flipAt a y) = supportSize y := by
  rw [supportSize_eq_sum, supportSize_eq_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hka : k = a
  · subst k
    cases h : y a <;> simp [flipAt, negateOutcome, h]
  · simp [flipAt_apply_of_ne hka]

/-- Flipping an unselected iid coordinate preserves the selector kernel weight.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem kernelWeight_flipAt_of_ne {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) (a : Fin b) (ha : a ≠ x.1) :
    kernelWeight hb (flipAt a y) x = kernelWeight hb y x := by
  classical
  have hxa : x.1 ≠ a := Ne.symm ha
  simp [kernelWeight, supportSize_flipAt, selectorMatches,
    flipAt_apply_of_ne hxa]

/-- Unnormalized first moment of a conditional fiber.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def fiberMoment {b : ℕ} (hb : 0 < b) (x : SignedHash b) (a : Fin b) : ℝ :=
  ∑ y, (jointColumnLaw hb).weight (y, x) * yValue (y a)

/-- Every coordinate different from the selector has zero signed joint fiber moment.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fiberMoment_off {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (a : Fin b) (ha : a ≠ x.1) :
    fiberMoment hb x a = 0 := by
  have hsymm : fiberMoment hb x a = -fiberMoment hb x a := by
    calc
      fiberMoment hb x a =
          ∑ y, (jointColumnLaw hb).weight (flipAt a y, x) *
            yValue ((flipAt a y) a) := by
        exact ((flipAtEquiv a).sum_comp
          (fun y => (jointColumnLaw hb).weight (y, x) * yValue (y a))).symm
      _ = ∑ y, -((jointColumnLaw hb).weight (y, x) * yValue (y a)) := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [jointColumnLaw_weight, jointColumnLaw_weight,
          yVectorLaw_weight_flipAt hb a y,
          kernelWeight_flipAt_of_ne hb y x a ha]
        simp
      _ = -fiberMoment hb x a := by
        simp [fiberMoment]
  linarith

/-- The joint mass of zero-support iid outcomes equals the zero-support probability.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem zeroSupportMass {b : ℕ} (hb : 0 < b) :
    (∑ y, (yVectorLaw b hb).weight y *
      (if supportSize y = 0 then (1 : ℝ) else 0)) = p0 b := by
  classical
  calc
    (∑ y, (yVectorLaw b hb).weight y *
        (if supportSize y = 0 then (1 : ℝ) else 0)) =
        (yVectorLaw b hb).prob {zeroY b} := by
      rw [FiniteLaw.prob, FiniteLaw.expect]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hy : y = zeroY b
      · subst y
        simp [FiniteLaw.indicator, supportSize_eq_zero_iff]
      · have hs : supportSize y ≠ 0 := by
          simpa [supportSize_eq_zero_iff] using hy
        simp [FiniteLaw.indicator, hy, hs]
    _ = (yVectorLaw b hb).weight (zeroY b) :=
      FiniteLaw.prob_singleton (yVectorLaw b hb) (zeroY b)
    _ = p0 b := zeroY_weight hb

/-- Selection weight times its chosen coordinate value has the stated signed support-average formula.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem kernelWeight_mul_selectedValue {b : ℕ} (hb : 0 < b)
    (y : YVector b) (x : SignedHash b) :
    kernelWeight hb y x * yValue (y x.1) =
      x.2.val * kernelWeight hb y x -
        x.2.val * (selectorLaw b hb).weight x *
          (if supportSize y = 0 then (1 : ℝ) else 0) := by
  classical
  by_cases hzero : supportSize y = 0
  · have hy : y = zeroY b := (supportSize_eq_zero_iff y).mp hzero
    subst y
    simp [kernelWeight, hzero, zeroY, yValue]
  · by_cases hmatch : selectorMatches y x
    · have hyx : y x.1 = outcomeOfSign x.2 := hmatch
      simp [kernelWeight, hzero, hmatch, hyx]
      ring
    · simp [kernelWeight, hzero, hmatch]

/-- The selected coordinate joint fiber moment equals its explicit nonempty-support expression.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fiberMoment_selected {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    fiberMoment hb x x.1 =
      x.2.val * (selectorLaw b hb).weight x * (1 - p0 b) := by
  calc
    fiberMoment hb x x.1 =
        ∑ y, (yVectorLaw b hb).weight y *
          (kernelWeight hb y x * yValue (y x.1)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [jointColumnLaw_weight]
      ring
    _ = ∑ y, (yVectorLaw b hb).weight y *
        (x.2.val * kernelWeight hb y x -
          x.2.val * (selectorLaw b hb).weight x *
            (if supportSize y = 0 then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [kernelWeight_mul_selectedValue hb y x]
    _ = x.2.val * xMarginal hb x -
        x.2.val * (selectorLaw b hb).weight x *
          (∑ y, (yVectorLaw b hb).weight y *
            (if supportSize y = 0 then (1 : ℝ) else 0)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp only [xMarginal, jointColumnLaw_weight]
      simp_rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro y _hy
        ring
      · apply Finset.sum_congr rfl
        intro y _hy
        ring
    _ = x.2.val * (selectorLaw b hb).weight x * (1 - p0 b) := by
      rw [xMarginal_eq_selectorWeight hb x, zeroSupportMass hb]
      ring

/-- The reciprocal support correction times nonempty-support probability is one.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem cB_mul_one_sub_p0 {b : ℕ} (hb : 0 < b) :
    cB b * (1 - p0 b) = 1 := by
  rw [cB]
  exact inv_mul_cancel₀ (ne_of_gt (one_sub_p0_pos hb))

/-- The conditional iid coordinate mean is the support-corrected signed selector indicator.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_expect_yValue {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (a : Fin b) :
    (conditionalYLaw hb x).expect (fun y => yValue (y a)) =
      if a = x.1 then x.2.val * (1 - p0 b) else 0 := by
  by_cases ha : a = x.1
  · subst a
    rw [if_pos rfl, FiniteLaw.expect]
    simp only [conditionalYLaw_weight]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    change fiberMoment hb x x.1 / (selectorLaw b hb).weight x = _
    rw [fiberMoment_selected hb x]
    field_simp [ne_of_gt (selectorWeight_pos hb x)]
  · rw [if_neg ha, FiniteLaw.expect]
    simp only [conditionalYLaw_weight]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    change fiberMoment hb x a / (selectorLaw b hb).weight x = 0
    rw [fiberMoment_off hb x a ha, zero_div]

/-- Coordinatewise martingale identity `E[c_b Y | X=x] = X`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_barycenter_coordinate {b : ℕ} (hb : 0 < b)
    (x : SignedHash b) (a : Fin b) :
    (conditionalYLaw hb x).expect (fun y => cB b * yValue (y a)) =
      if a = x.1 then x.2.val else 0 := by
  rw [FiniteLaw.expect_smul, conditional_expect_yValue hb x a]
  by_cases ha : a = x.1
  · rw [if_pos ha, if_pos ha]
    calc
      cB b * (x.2.val * (1 - p0 b)) = x.2.val * (cB b * (1 - p0 b)) := by ring
      _ = x.2.val := by rw [cB_mul_one_sub_p0 hb, mul_one]
  · simp [ha]

/-- Signed basis vector attached directly to one selector.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def selectorVector {b : ℕ} (x : SignedHash b) : EVec b :=
  WithLp.toLp 2 fun a => if a = x.1 then x.2.val else 0

/-- The finite conditional barycenter as a Euclidean vector.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def conditionalBarycenter {b : ℕ} (hb : 0 < b) (x : SignedHash b) : EVec b :=
  WithLp.toLp 2 fun a =>
    (conditionalYLaw hb x).expect (fun y => cB b * yValue (y a))

/-- The conditional Euclidean iid barycenter equals the corrected signed selector vector.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_barycenter {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    conditionalBarycenter hb x = selectorVector x := by
  ext a
  exact conditional_barycenter_coordinate hb x a

end

end SparseIIDCoupling

end NLAlib.SparseFock
