import NLAlib.Probability.Gaussian.Moments.Hermite
import NLAlib.Matrix.Structured.HermiteIndices

/-! # Normalized finite Hermite recurrence

Multiplication by a Gaussian coordinate is raising plus lowering with exact
square-root coefficients. This is the scalar identity used by the finite
matrix compression, with no infinite series or unbounded operators.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace NLAlib

/-- The square root of the next factorial has the normalized raising factor. -/
theorem sqrt_factorial_succ (n : ℕ) :
    Real.sqrt ((n + 1).factorial : ℝ) =
      Real.sqrt ((n : ℝ) + 1) * Real.sqrt (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

private theorem sqrt_factorial_ne_zero (n : ℕ) : Real.sqrt (n.factorial : ℝ) ≠ 0 := by
  positivity

private theorem sqrt_succ_ne_zero (n : ℕ) : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
  positivity

/-- The first Gaussian coordinate identity includes the vacuum. -/
theorem mul_hermiteFunction_zero (x : ℝ) : x * hermiteFunction 0 x = hermiteFunction 1 x := by
  simp [hermiteFunction, realHermite, Polynomial.hermite_one]

/-- The normalized Hermite three-term recurrence, with its exact creation
and annihilation square-root coefficients. -/
theorem mul_hermiteFunction_succ (n : ℕ) (x : ℝ) :
    x * hermiteFunction (n + 1) x =
      Real.sqrt ((n : ℝ) + 2) * hermiteFunction (n + 2) x +
        Real.sqrt ((n : ℝ) + 1) * hermiteFunction n x := by
  have hrec : x * (realHermite (n + 1)).eval x =
      (realHermite (n + 2)).eval x + ((n : ℝ) + 1) * (realHermite n).eval x := by
    have hh := congrArg (fun P : ℝ[X] => P.eval x) (realHermite_succ (n + 1))
    rw [derivative_realHermite_succ] at hh
    simp only [eval_sub, eval_mul, eval_X, eval_smul, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, eval_add, eval_natCast, eval_one, Nat.add_assoc] at hh
    linarith
  have hf₁ := sqrt_factorial_succ n
  have hf₂ := sqrt_factorial_succ (n + 1)
  have h₁ := sqrt_succ_ne_zero n
  have h₂ : Real.sqrt ((n : ℝ) + 2) ≠ 0 := by positivity
  have hf := sqrt_factorial_ne_zero n
  have hs : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  unfold hermiteFunction
  rw [show n + 2 = (n + 1) + 1 by omega, hf₂, hf₁]
  simp only [Nat.cast_add, Nat.cast_one] at *
  rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
  field_simp
  nlinarith [congrArg (fun y : ℝ => y * (realHermite n).eval x) hs]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A tensor Hermite product splits at any chosen coordinate, so no
nonvanishing division by other Hermite factors is needed. -/
theorem productHermite_update (a : ι → ℕ) (i : ι) (n : ℕ) (x : ι → ℝ) :
    productHermite (Function.update a i n) x =
      hermiteFunction n (x i) *
        ∏ j ∈ Finset.univ \ {i}, hermiteFunction (a j) (x j) := by
  unfold productHermite
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by simpa only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ,
    true_and] using hj
  simp [Function.update_of_ne hji]

/-- Multiplication by one coordinate in the finite total-degree Hermite
basis is exactly creation plus annihilation at interior degrees. -/
theorem coordinate_mul_productHermite {p : ℕ} (a : HermiteIndex ι p) (i : ι)
    (h : a.degree < p) (x : ι → ℝ) :
    x i * productHermite a.val x =
      Real.sqrt ((a.val i : ℝ) + 1) * productHermite (a.raise i h).val x +
        if 0 < a.val i then Real.sqrt (a.val i : ℝ) *
          productHermite (a.lower i).val x else 0 := by
  have hsplit : productHermite a.val x = hermiteFunction (a.val i) (x i) *
      ∏ j ∈ Finset.univ \ {i}, hermiteFunction (a.val j) (x j) := by
    unfold productHermite
    exact Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) _
  have hraise : productHermite (a.raise i h).val x =
      hermiteFunction (a.val i + 1) (x i) *
        ∏ j ∈ Finset.univ \ {i}, hermiteFunction (a.val j) (x j) :=
    productHermite_update a.val i (a.val i + 1) x
  have hlower : productHermite (a.lower i).val x =
      hermiteFunction (a.val i - 1) (x i) *
        ∏ j ∈ Finset.univ \ {i}, hermiteFunction (a.val j) (x j) :=
    productHermite_update a.val i (a.val i - 1) x
  rw [hsplit, hraise, hlower]
  cases hn : a.val i with
  | zero =>
    have hh : x i = hermiteFunction 1 (x i) := by
      simpa only [hermiteFunction_zero, mul_one] using mul_hermiteFunction_zero (x i)
    simp [← hh]
  | succ n =>
    simp only [hn, Nat.succ_pos, if_true, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hh := mul_hermiteFunction_succ n (x i)
    have he := congrArg (fun y : ℝ => y *
      ∏ j ∈ Finset.univ \ {i}, hermiteFunction (a.val j) (x j)) hh
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    convert he using 1 <;> ring

end NLAlib
