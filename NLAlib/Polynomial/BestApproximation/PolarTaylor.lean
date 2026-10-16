import NLAlib.Polynomial.BestApproximation.OddUpdates
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Polynomial.Eval.Degree
/-!+# A finite polynomial competitor for polar minimax updates

The truncated inverse-square-root coefficients are defined by their finite
recurrence. Differentiating the resulting odd polynomial telescopes. Its
squared error bound follows from one change in the derivative's sign,
without infinite power series or a convolution identity.

Source: Polar Express, §3 and Appendix D; matrix-toolkit re-derivation §40.
Supports `polar-minimax-polynomial-iteration`.
-/
noncomputable section
open Finset Polynomial Set
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Finite inverse-square-root Taylor coefficients, given by their recurrence. -/
def polarTaylorCoeff : ℕ → ℝ
  | 0 => 1
  | j + 1 => ((2 * j + 1 : ℕ) : ℝ) / (2 * j + 2 : ℕ) * polarTaylorCoeff j

/-- Every finite inverse-square-root coefficient is strictly positive. -/
theorem polarTaylorCoeff_pos (j : ℕ) : 0 < polarTaylorCoeff j := by
  induction j with
  | zero => norm_num [polarTaylorCoeff]
  | succ j ih =>
    simp only [polarTaylorCoeff]
    exact mul_pos (div_pos (by positivity) (by positivity)) ih

/-- The coefficient recurrence without division. -/
theorem polarTaylorCoeff_recurrence (j : ℕ) :
    (2 * (j : ℝ) + 2) * polarTaylorCoeff (j + 1) =
      (2 * (j : ℝ) + 1) * polarTaylorCoeff j := by
  simp only [polarTaylorCoeff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp

/-- The finite Taylor polynomial in its nonnegative argument. -/
def polarTaylorSum (q : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ range (q + 1), polarTaylorCoeff j * u ^ j

/-- The actual odd polynomial competitor `x C_q(1-x²)`. -/
def polarTaylorUpdate (q : ℕ) (x : ℝ) : ℝ := x * polarTaylorSum q (1 - x ^ 2)

/-- Endpoint values of the finite competitor. -/
@[simp] theorem polarTaylorUpdate_zero (q : ℕ) : polarTaylorUpdate q 0 = 0 := by
  simp [polarTaylorUpdate]

@[simp] theorem polarTaylorUpdate_one (q : ℕ) : polarTaylorUpdate q 1 = 1 := by
  simp only [polarTaylorUpdate, polarTaylorSum, one_pow, sub_self, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp [polarTaylorCoeff]
  · intro j hj hj0
    rw [zero_pow hj0, mul_zero]
  · simp

/-- Adding the last retained term. -/
theorem polarTaylorUpdate_succ (q : ℕ) (x : ℝ) :
    polarTaylorUpdate (q + 1) x = polarTaylorUpdate q x +
      polarTaylorCoeff (q + 1) * x * (1 - x ^ 2) ^ (q + 1) := by
  simp only [polarTaylorUpdate, polarTaylorSum, Finset.sum_range_succ]
  ring

/-- The derivative telescopes to one nonnegative monomial on `[0,1]`. -/
theorem hasDerivAt_polarTaylorUpdate (q : ℕ) (x : ℝ) :
    HasDerivAt (polarTaylorUpdate q)
      ((2 * (q : ℝ) + 1) * polarTaylorCoeff q * (1 - x ^ 2) ^ q) x := by
  induction q with
  | zero =>
    have hf : polarTaylorUpdate 0 = id := by
      funext y
      simp [polarTaylorUpdate, polarTaylorSum, polarTaylorCoeff, Finset.sum_range_succ]
    rw [hf]
    simpa [polarTaylorCoeff] using! hasDerivAt_id x
  | succ q ih =>
    have hu : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa using! (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have ht := (((hasDerivAt_id x).mul (hu.pow (q + 1))).const_mul (polarTaylorCoeff (q + 1)))
    have hh := ih.add ht
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq, Nat.add_sub_cancel,
      one_mul] at hh
    have hf : polarTaylorUpdate q + (fun y => polarTaylorCoeff (q + 1) *
        (y * (1 - y ^ 2) ^ (q + 1))) = polarTaylorUpdate (q + 1) := by
      funext y
      change polarTaylorUpdate q y + polarTaylorCoeff (q + 1) *
        (y * (1 - y ^ 2) ^ (q + 1)) = polarTaylorUpdate (q + 1) y
      rw [polarTaylorUpdate_succ]
      ring
    rw [hf] at hh
    convert! hh using 1
    rw [pow_succ]
    push_cast
    have hc := polarTaylorCoeff_recurrence q
    linear_combination (1 - x ^ 2) ^ q * hc

/-- Continuity of the finite competitor follows from its checked derivative. -/
theorem continuous_polarTaylorUpdate (q : ℕ) : Continuous (polarTaylorUpdate q) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_polarTaylorUpdate q x).continuousAt

/-- The finite Taylor sum is monotone for nonnegative arguments. -/
theorem polarTaylorSum_monotoneOn (q : ℕ) : MonotoneOn (polarTaylorSum q) (Ici 0) := by
  intro u hu v hv huv
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv j) (polarTaylorCoeff_pos j).le

/-- The Taylor competitor is positive and at most one on the positive
unit interval. -/
theorem polarTaylorUpdate_pos_le_one (q : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < polarTaylorUpdate q x ∧ polarTaylorUpdate q x ≤ 1 := by
  have hu : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hs : 1 ≤ polarTaylorSum q (1 - x ^ 2) := by
    calc
      1 = polarTaylorCoeff 0 * (1 - x ^ 2) ^ 0 := by simp [polarTaylorCoeff]
      _ ≤ polarTaylorSum q (1 - x ^ 2) :=
        Finset.single_le_sum (fun j hj => mul_nonneg (polarTaylorCoeff_pos j).le (pow_nonneg hu j))
          (by simp)
  have hmono : MonotoneOn (polarTaylorUpdate q) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_polarTaylorUpdate q).continuousOn
    · intro y hy; exact (hasDerivAt_polarTaylorUpdate q y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_polarTaylorUpdate q y).deriv]
      have hyI : y ∈ Icc (0 : ℝ) 1 := interior_subset hy
      have hnon : 0 ≤ 1 - y ^ 2 := by nlinarith [hyI.1, hyI.2]
      exact mul_nonneg (mul_nonneg (by positivity) (polarTaylorCoeff_pos q).le) (pow_nonneg hnon q)
  refine ⟨mul_pos hx (lt_of_lt_of_le zero_lt_one hs), ?_⟩
  simpa only [polarTaylorUpdate_one] using hmono ⟨hx.le, hx1⟩ (by simp) hx1

/-- The squared finite Taylor competitor loses at most the `(q+1)`st
power of the input squared gap. This is the scalar contraction needed
for the sharp polar minimax iteration rate.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem one_sub_pow_le_polarTaylorUpdate_sq (q : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    1 - (1 - x ^ 2) ^ (q + 1) ≤ polarTaylorUpdate q x ^ 2 := by
  let K := (2 * (q : ℝ) + 1) * polarTaylorCoeff q
  let B := fun y : ℝ => K * polarTaylorSum q (1 - y ^ 2) - (q + 1)
  let F := fun y : ℝ => polarTaylorUpdate q y ^ 2 - 1 + (1 - y ^ 2) ^ (q + 1)
  have hK : 0 ≤ K := mul_nonneg (by positivity) (polarTaylorCoeff_pos q).le
  have hB : AntitoneOn B (Icc 0 1) := by
    intro u hu v hv huv
    have hu' : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    have hv' : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    have he : 1 - v ^ 2 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hv.1]
    dsimp only [B]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left
      (polarTaylorSum_monotoneOn q hv' hu' he) hK) _
  have hF (y : ℝ) : HasDerivAt F (2 * y * (1 - y ^ 2) ^ q * B y) y := by
    have hu : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
      simpa using! (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).pow 2)
    have hh := (((hasDerivAt_polarTaylorUpdate q y).pow 2).sub_const 1).add (hu.pow (q + 1))
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.add_sub_cancel, pow_one] at hh
    convert! hh using 1
    dsimp only [B, K, polarTaylorUpdate]
    rw [pow_succ]
    push_cast
    ring
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun y => (hF y).continuousAt
  have hFzero : F 0 = 0 := by simp [F]
  have hFone : F 1 = 0 := by simp [F]
  have hnon : 0 ≤ F x := by
    by_cases hBx : 0 ≤ B x
    · have hm : MonotoneOn F (Icc 0 x) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hFcont.continuousOn
        · intro y hy; exact (hF y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [(hF y).deriv]
          have hyI : y ∈ Icc (0 : ℝ) x := interior_subset hy
          have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hyI.1, hyI.2.trans hx.2⟩
          have hby : 0 ≤ B y := hBx.trans (hB hy1 hx hyI.2)
          have hu : 0 ≤ 1 - y ^ 2 := by nlinarith [hy1.1, hy1.2]
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hyI.1) (pow_nonneg hu q)) hby
      have hh := hm ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
      rwa [hFzero] at hh
    · have hm : AntitoneOn F (Icc x 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc x 1) hFcont.continuousOn
        · intro y hy; exact (hF y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [(hF y).deriv]
          have hyI : y ∈ Icc x (1 : ℝ) := interior_subset hy
          have hy0 : y ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hyI.1, hyI.2⟩
          have hby : B y ≤ 0 := (hB hx hy0 hyI.1).trans (le_of_not_ge hBx)
          have hu : 0 ≤ 1 - y ^ 2 := by nlinarith [hy0.1, hy0.2]
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (mul_nonneg (by norm_num) hy0.1) (pow_nonneg hu q)) hby
      have hh := hm ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2
      rwa [hFone] at hh
  dsimp only [F] at hnon
  linarith

end NLAlib
