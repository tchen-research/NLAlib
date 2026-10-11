/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LocalOperators
import NLAlib.ForMathlib.Probability.FiniteL2
import NLAlib.ForMathlib.Probability.FiniteLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Ternary coordinate Jacobi matrix

The centered unit-variance sparse ternary law is represented by its three-level orthonormal-basis Jacobi multiplication matrix.
Ported from `SparseFockFormal.TernaryJacobi` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

/-- The three atoms in the normalized iid coordinate law.  This type indexes
outcomes; it is deliberately distinct from `Level`, which indexes the
orthogonal-polynomial basis.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
inductive EtaOutcome where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

/-- The negative, zero, and positive ternary outcomes have their literal finite enumeration.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
instance : Fintype EtaOutcome where
  elems := {.neg, .zero, .pos}
  complete x := by cases x <;> simp

/-- The ternary outcome enumeration consists exactly of negative, zero, and positive.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem univ_etaOutcome :
    (Finset.univ : Finset EtaOutcome) = {.neg, .zero, .pos} := by
  ext x
  cases x <;> simp

/-- The local Jacobi level enumeration consists exactly of zero, one, and two.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem univ_level_for_jacobi :
    (Finset.univ : Finset Level) = {.zero, .one, .two} := by
  ext x
  cases x <;> simp

namespace TernaryJacobi

open LocalOperator

/-- The normalized sparse coordinate `eta` from (3.1) of the paper.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def eta (b : ℕ) : EtaOutcome → ℝ
  | .neg => -Real.sqrt b
  | .zero => 0
  | .pos => Real.sqrt b

/-- Probability mass of the three-point law.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def mass (b : ℕ) : EtaOutcome → ℝ
  | .neg => 1 / (2 * (b : ℝ))
  | .zero => 1 - 1 / (b : ℝ)
  | .pos => 1 / (2 * (b : ℝ))

/-- The ternary sparse-coordinate masses sum to one at positive block size.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_mass {b : ℕ} (hb : 0 < b) :
    ∑ x, mass b x = 1 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  simp [mass, univ_etaOutcome]
  field_simp
  ring

/-- Every ternary sparse-coordinate mass is nonnegative at positive block size.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem mass_nonneg {b : ℕ} (hb : 0 < b) (x : EtaOutcome) :
    0 ≤ mass b x := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  cases x
  · exact div_nonneg zero_le_one (mul_nonneg (by norm_num) hbR.le)
  · simp only [mass]
    apply sub_nonneg.mpr
    exact (div_le_one hbR).2 (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  · exact div_nonneg zero_le_one (mul_nonneg (by norm_num) hbR.le)

/-- The ternary coordinate law as an explicit normalized finite probability
law.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def law (b : ℕ) (hb : 0 < b) : FiniteLaw EtaOutcome where
  weight := mass b
  weight_nonneg := mass_nonneg hb
  sum_weight := sum_mass hb

/-- Explicit finite expectation for the ternary law.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def expect (b : ℕ) (f : EtaOutcome → ℝ) : ℝ :=
  ∑ x, mass b x * f x

/-- The zero ternary outcome has zero coordinate value.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem eta_zero (b : ℕ) : eta b .zero = 0 := rfl

/-- The square of the square root of a natural block size is its real value.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sq_sqrt_nat (b : ℕ) : (Real.sqrt b) ^ 2 = (b : ℝ) := by
  exact Real.sq_sqrt (Nat.cast_nonneg b : (0 : ℝ) ≤ b)

/-- Cubing a ternary sparse coordinate multiplies it by the block size.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem eta_cube {b : ℕ} (x : EtaOutcome) :
    eta b x ^ 3 = (b : ℝ) * eta b x := by
  have hs := sq_sqrt_nat b
  cases x <;> simp [eta, pow_succ, hs]

/-- A ternary sparse coordinate is centered.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_eta {b : ℕ} (hb : 0 < b) : expect b (eta b) = 0 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  simp [expect, mass, eta, univ_etaOutcome]

/-- A ternary sparse coordinate has second moment one.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_eta_sq {b : ℕ} (hb : 0 < b) :
    expect b (fun x => eta b x ^ 2) = 1 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hs := sq_sqrt_nat b
  simp [expect, mass, eta, univ_etaOutcome, hs]
  field_simp
  norm_num

/-- The literal finite ternary law has zero coordinate mean.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem law_expect_eta {b : ℕ} (hb : 0 < b) :
    (law b hb).expect (eta b) = 0 := by
  change expect b (eta b) = 0
  exact expect_eta hb

/-- The literal finite ternary law has coordinate second moment one.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem law_expect_eta_sq {b : ℕ} (hb : 0 < b) :
    (law b hb).expect (fun x => eta b x ^ 2) = 1 := by
  change expect b (fun x => eta b x ^ 2) = 1
  exact expect_eta_sq hb

/-- The orthogonal-polynomial functions `e_0,e_1,e_2` in (3.4).

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def basisFun (b : ℕ) : Level → EtaOutcome → ℝ
  | .zero, _ => 1
  | .one, x => eta b x
  | .two, x => (eta b x ^ 2 - 1) / Real.sqrt ((b : ℝ) - 1)

/-- Weighted real inner product on functions of the ternary atom.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def weightedInner (b : ℕ) (f g : EtaOutcome → ℝ) : ℝ :=
  expect b (fun x => f x * g x)

/-- The heavy Jacobi coefficient is positive when the block size exceeds one.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sqrt_b_sub_one_pos {b : ℕ} (hb : 1 < b) :
    0 < Real.sqrt ((b : ℝ) - 1) := by
  rw [Real.sqrt_pos]
  exact sub_pos.mpr (by exact_mod_cast hb)

/-- The squared heavy Jacobi coefficient is the block size minus one.
Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sq_sqrt_b_sub_one {b : ℕ} (hb : 1 < b) :
    (Real.sqrt ((b : ℝ) - 1)) ^ 2 = (b : ℝ) - 1 := by
  apply Real.sq_sqrt
  exact sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt hb))

/-- The three polynomial functions are orthonormal in the exact weighted
`L₂` inner product of the ternary law.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem basis_orthonormal {b : ℕ} (hb : 1 < b) (i j : Level) :
    weightedInner b (basisFun b i) (basisFun b j) =
      if i = j then 1 else 0 := by
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb))
  have hs0 : Real.sqrt ((b : ℝ) - 1) ≠ 0 :=
    ne_of_gt (sqrt_b_sub_one_pos hb)
  have hsb := sq_sqrt_nat b
  have hsm := sq_sqrt_b_sub_one hb
  cases i <;> cases j <;>
    simp [weightedInner, expect, basisFun, mass, eta, univ_etaOutcome] <;>
    field_simp <;> nlinarith [hsb, hsm]

/-- Completeness of the polynomial basis, expressed as the exact Fourier
reconstruction formula on the three-point space.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem basis_reconstruction {b : ℕ} (hb : 1 < b)
    (f : EtaOutcome → ℝ) (x : EtaOutcome) :
    f x = ∑ i, weightedInner b (basisFun b i) f * basisFun b i x := by
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb))
  have hs0 : Real.sqrt ((b : ℝ) - 1) ≠ 0 :=
    ne_of_gt (sqrt_b_sub_one_pos hb)
  have hsb := sq_sqrt_nat b
  have hsm := sq_sqrt_b_sub_one hb
  cases x <;>
    simp [weightedInner, expect, basisFun, mass, eta, univ_etaOutcome,
      univ_level_for_jacobi] <;>
    field_simp
  all_goals simp only [hsb, hsm]
  all_goals ring

/-- Pointwise recurrence `eta * e_0 = e_1`.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem mul_e0 {b : ℕ} (x : EtaOutcome) :
    eta b x * basisFun b .zero x = basisFun b .one x := by
  simp [basisFun]

/-- Pointwise recurrence `eta * e_1 = e_0 + sqrt(b-1) e_2`.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem mul_e1 {b : ℕ} (hb : 1 < b) (x : EtaOutcome) :
    eta b x * basisFun b .one x =
      basisFun b .zero x + Real.sqrt ((b : ℝ) - 1) * basisFun b .two x := by
  have hspos := sqrt_b_sub_one_pos hb
  have hsne : Real.sqrt ((b : ℝ) - 1) ≠ 0 := ne_of_gt hspos
  have hsq := sq_sqrt_b_sub_one hb
  cases x <;> simp [basisFun, eta] <;>
    field_simp <;> nlinarith [hsq]

/-- Pointwise recurrence `eta * e_2 = sqrt(b-1) e_1`.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem mul_e2 {b : ℕ} (hb : 1 < b) (x : EtaOutcome) :
    eta b x * basisFun b .two x =
      Real.sqrt ((b : ℝ) - 1) * basisFun b .one x := by
  have hspos := sqrt_b_sub_one_pos hb
  have hsne : Real.sqrt ((b : ℝ) - 1) ≠ 0 := ne_of_gt hspos
  cases x <;> simp [basisFun, eta] <;> field_simp

/-- Multiplication by `eta`, expressed pointwise in the polynomial basis, is
exactly the Jacobi matrix from (3.5).

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem multiplication_recurrence {b : ℕ} (hb : 1 < b)
    (j : Level) (x : EtaOutcome) :
    eta b x * basisFun b j x =
      ∑ i, jacobi (Real.sqrt ((b : ℝ) - 1)) i j * basisFun b i x := by
  cases j
  · simpa [jacobi_apply, univ_level_for_jacobi] using mul_e0 (b := b) x
  · simpa [jacobi_apply, univ_level_for_jacobi, add_assoc, add_comm, add_left_comm] using mul_e1 hb x
  · simpa [jacobi_apply, univ_level_for_jacobi] using mul_e2 hb x

/-- Matrix coefficients of multiplication by `eta` in the orthonormal basis.
This is the precise finite `L₂(eta)` semantics of `LocalOperator.jacobi`.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem multiplication_matrix {b : ℕ} (hb : 1 < b) (i j : Level) :
    weightedInner b (basisFun b i)
        (fun x => eta b x * basisFun b j x) =
      jacobi (Real.sqrt ((b : ℝ) - 1)) i j := by
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb))
  have hs0 : Real.sqrt ((b : ℝ) - 1) ≠ 0 :=
    ne_of_gt (sqrt_b_sub_one_pos hb)
  have hsb := sq_sqrt_nat b
  have hsm := sq_sqrt_b_sub_one hb
  cases i <;> cases j <;>
    simp [weightedInner, expect, basisFun, mass, eta, univ_etaOutcome,
      jacobi_apply] <;>
    field_simp <;> nlinarith [hsb, hsm]

/-- The ternary probability space bundled as an explicit complete finite ON
basis.  This object can be tensored over sites without introducing an abstract
probability or Hilbert-space assumption.

Source: ported from `SparseFockFormal.TernaryJacobi`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def weightedONBasis (b : ℕ) (hb : 1 < b) :
    FiniteL2.WeightedONBasis EtaOutcome Level where
  weight := mass b
  weight_nonneg := mass_nonneg (lt_trans Nat.zero_lt_one hb)
  sum_weight := sum_mass (lt_trans Nat.zero_lt_one hb)
  basis := basisFun b
  orthonormal_same := by
    intro i
    simpa [weightedInner, expect, mul_assoc] using basis_orthonormal hb i i
  orthonormal_ne := by
    intro i j hij
    simpa [hij, weightedInner, expect, mul_assoc] using basis_orthonormal hb i j
  reconstruction := by
    intro f x
    simpa [weightedInner, expect, mul_assoc] using basis_reconstruction hb f x
  vacuum := .zero
  vacuum_eq_one := by
    intro x
    simp [basisFun]

end TernaryJacobi

end NLAlib.SparseFock
