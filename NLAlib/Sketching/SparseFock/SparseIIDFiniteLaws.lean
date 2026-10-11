/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.ForMathlib.Probability.FiniteLaw
import NLAlib.Sketching.SparseFock.SparseStackDistribution
import NLAlib.Sketching.SparseFock.TernaryJacobi
import NLAlib.Sketching.SparseFock.PaperParameters
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite iid sparse-coordinate laws

Literal ternary vector laws, support probability, and reciprocal support corrections.
Ported from `SparseFockFormal.SparseIIDCoupling` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace

namespace NLAlib.SparseFock

namespace SparseIIDCoupling

open ParsevalFrame SparseStackModel SparseStackDistribution

noncomputable section

/-- The unscaled value of one iid coordinate `Y_a`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def yValue : EtaOutcome → ℝ
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- The nonzero outcome associated with a Rademacher sign.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def outcomeOfSign : Sign → EtaOutcome
  | .plus => .pos
  | .minus => .neg

/-- Embedding a sign into the ternary outcomes retains its real signed value.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem yValue_outcomeOfSign (e : Sign) :
    yValue (outcomeOfSign e) = e.val := by
  cases e <;> rfl

/-- Negation of a ternary atom.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def negateOutcome : EtaOutcome → EtaOutcome
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

/-- Negating a ternary outcome twice returns the original outcome.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem negateOutcome_involutive (z : EtaOutcome) :
    negateOutcome (negateOutcome z) = z := by cases z <;> rfl

/-- Negating a ternary outcome negates its real coordinate value.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem yValue_negateOutcome (z : EtaOutcome) :
    yValue (negateOutcome z) = -yValue z := by cases z <;> norm_num [yValue, negateOutcome]

/-- Flip a Rademacher sign.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flipSign : Sign → Sign
  | .plus => .minus
  | .minus => .plus

/-- Flipping a sign twice returns the original sign.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flipSign_involutive (e : Sign) : flipSign (flipSign e) = e := by
  cases e <;> rfl

/-- Embedding a flipped sign is the negation of the embedded original sign.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem outcomeOfSign_flipSign (e : Sign) :
    outcomeOfSign (flipSign e) = negateOutcome (outcomeOfSign e) := by
  cases e <;> rfl

/-- One iid ternary coordinate with masses `1/(2b), 1-1/b, 1/(2b)`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def coordinateLaw (b : ℕ) (hb : 0 < b) : FiniteLaw EtaOutcome where
  weight := TernaryJacobi.mass b
  weight_nonneg := TernaryJacobi.mass_nonneg hb
  sum_weight := TernaryJacobi.sum_mass hb

/-- The coordinate law has exactly the prescribed ternary mass.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem coordinateLaw_weight (b : ℕ) (hb : 0 < b) (z : EtaOutcome) :
    (coordinateLaw b hb).weight z = TernaryJacobi.mass b z := rfl

/-- An iid vector `Y ∈ {-1,0,1}^b`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev YVector (b : ℕ) := Fin b → EtaOutcome

/-- The independent-coordinate law of `Y`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def yVectorLaw (b : ℕ) (hb : 0 < b) : FiniteLaw (YVector b) :=
  FiniteLaw.independentProduct (fun _ : Fin b => coordinateLaw b hb)

/-- The iid vector-law weight is the product of its coordinate masses.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem yVectorLaw_weight {b : ℕ} (hb : 0 < b) (y : YVector b) :
    (yVectorLaw b hb).weight y = ∏ a, TernaryJacobi.mass b (y a) := rfl

/-- The all-zero iid vector.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def zeroY (b : ℕ) : YVector b := fun _ => .zero

/-- The finite nonzero support.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def support {b : ℕ} (y : YVector b) : Finset (Fin b) :=
  Finset.univ.filter fun a => y a ≠ .zero

/-- A coordinate belongs to iid support precisely when its outcome is nonzero.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem mem_support {b : ℕ} (y : YVector b) (a : Fin b) :
    a ∈ support y ↔ y a ≠ .zero := by simp [support]

/-- Number of nonzero coordinates.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def supportSize {b : ℕ} (y : YVector b) : ℕ := (support y).card

/-- An iid vector has empty support precisely when it is the zero vector.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem supportSize_eq_zero_iff {b : ℕ} (y : YVector b) :
    supportSize y = 0 ↔ y = zeroY b := by
  constructor
  · intro h
    apply funext
    intro a
    have hempty : support y = ∅ := Finset.card_eq_zero.mp h
    have hnot : a ∉ support y := by simp [hempty]
    have : ¬y a ≠ .zero := by simpa [mem_support] using hnot
    simpa [zeroY] using not_ne_iff.mp this
  · rintro rfl
    simp [supportSize, support, zeroY]

/-- The zero-vector probability `p₀=(1-1/b)^b`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def p0 (b : ℕ) : ℝ := (1 - 1 / (b : ℝ)) ^ b

/-- The zero iid vector has the defined zero-support probability.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem zeroY_weight {b : ℕ} (hb : 0 < b) :
    (yVectorLaw b hb).weight (zeroY b) = p0 b := by
  simp [yVectorLaw_weight, zeroY, TernaryJacobi.mass, p0]

/-- The zero-support probability is nonnegative.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem p0_nonneg {b : ℕ} (hb : 0 < b) : 0 ≤ p0 b := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase : (0 : ℝ) ≤ 1 - 1 / (b : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : (0 : ℝ) < b)).2 hbR
  exact pow_nonneg hbase _

/-- The zero-support probability is strictly below one at positive block size.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem p0_lt_one {b : ℕ} (hb : 0 < b) : p0 b < 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (b : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hbR).2 (by exact_mod_cast hb)
  have hbase1 : (1 : ℝ) - 1 / (b : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / (b : ℝ) := one_div_pos.mpr hbR
    linarith
  exact pow_lt_one₀ hbase0 hbase1 (Nat.ne_of_gt hb)

/-- The elementary exponential estimate omitted in the prose proof.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem p0_le_exp_neg_one {b : ℕ} (hb : 0 < b) :
    p0 b ≤ Real.exp (-1) := by
  have h1b : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  simpa [p0] using
    (Real.one_sub_div_pow_le_exp_neg (n := b) (t := (1 : ℝ)) h1b)

/-- The exact coupling rescaling `c_b=(1-p₀)⁻¹`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def cB (b : ℕ) : ℝ := (1 - p0 b)⁻¹

/-- The nonempty-support probability is positive at positive block size.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_sub_p0_pos {b : ℕ} (hb : 0 < b) : 0 < 1 - p0 b := by
  linarith [p0_lt_one hb]

/-- The reciprocal nonempty-support correction is at least one.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_le_cB {b : ℕ} (hb : 0 < b) : 1 ≤ cB b := by
  rw [cB, one_le_inv₀ (one_sub_p0_pos hb)]
  linarith [p0_nonneg hb]

/-- The finite-block support correction is bounded by the universal support-gap constant.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem cB_le_cStar {b : ℕ} (hb : 0 < b) : cB b ≤ PaperParameters.cStar := by
  rw [cB, PaperParameters.cStar]
  apply inv_anti₀ PaperParameters.expGap_pos
  linarith [p0_le_exp_neg_one hb]

end

end SparseIIDCoupling

end NLAlib.SparseFock
