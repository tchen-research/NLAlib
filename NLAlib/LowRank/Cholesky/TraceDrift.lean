import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite Jensen for the relative trace drift

Weighted Cauchy--Schwarz proves the finite Jensen inequality for the scalar
RPCholesky drift, including the absorbing zero trace.
Source: manuscript `sa:rp-recursion`.
-/

noncomputable section
namespace NLAlib

/-- The nonnegative relative trace drift, with totalized zero-trace value zero.
Source: manuscript `sa:rp-recursion`, its convex scalar function `f`. -/
def traceExcessDrift (τ x : ℝ) : ℝ := (max (x - τ) 0) ^ 2 / x

/-- The scalar trace drift is nonnegative at nonnegative trace.
Source: manuscript `sa:rp-recursion`, nonnegative drift. -/
theorem traceExcessDrift_nonneg {τ x : ℝ} (hx : 0 ≤ x) : 0 ≤ traceExcessDrift τ x :=
  div_nonneg (sq_nonneg _) hx

/-- Finite Jensen for the RPCholesky trace drift follows directly from weighted
Cauchy--Schwarz. Source: manuscript `sa:rp-recursion`; this avoids differentiating
the piecewise function while retaining its exact drift and zero branch. -/
theorem traceExcessDrift_sum_le_sum {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hwSum : ∑ i, w i = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    traceExcessDrift τ (∑ i, w i * x i) ≤ ∑ i, w i * traceExcessDrift τ (x i) := by
  let u := ∑ i, w i * x i
  have hu : 0 ≤ u := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hx i)
  have hg : 0 ≤ ∑ i, w i * traceExcessDrift τ (x i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (traceExcessDrift_nonneg (hx i))
  by_cases hut : u ≤ τ
  · change traceExcessDrift τ u ≤ _
    simpa only [traceExcessDrift, max_eq_right (by linarith : u - τ ≤ 0),
      zero_pow two_ne_zero, zero_div] using hg
  · have huτ : τ < u := lt_of_not_ge hut
    have hu0 : 0 < u := hτ.trans_lt huτ
    have hlow : u - τ ≤ ∑ i, w i * max (x i - τ) 0 := by
      have h := Finset.sum_le_sum (s := Finset.univ) (f := fun i => w i * (x i - τ))
        (g := fun i => w i * max (x i - τ) 0)
        (fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hw i))
      simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hwSum, one_mul] using h
    have hCS : (∑ i, w i * max (x i - τ) 0) ^ 2 ≤
        (∑ i, w i * traceExcessDrift τ (x i)) * u := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · intro i _; exact mul_nonneg (hw i) (traceExcessDrift_nonneg (hx i))
      · intro i _; exact mul_nonneg (hw i) (hx i)
      · intro i _
        by_cases hi : x i = 0
        · simp only [hi, traceExcessDrift, zero_sub, max_eq_right (neg_nonpos.mpr hτ),
            mul_zero, zero_pow two_ne_zero, div_zero]
          exact le_rfl
        · dsimp only [traceExcessDrift]
          have he : (w i * max (x i - τ) 0) ^ 2 =
              (w i * ((max (x i - τ) 0) ^ 2 / x i)) * (w i * x i) := by
            field_simp
          exact he.le
    change traceExcessDrift τ u ≤ _
    rw [traceExcessDrift, max_eq_left (sub_nonneg.mpr huτ.le), div_le_iff₀ hu0]
    exact (pow_le_pow_left₀ (sub_nonneg.mpr huτ.le) hlow 2).trans hCS

end NLAlib
