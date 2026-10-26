/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Kaczmarz.MeanContraction

/-!
# Sums of actual Kaczmarz iterates

`runSum` adds the iterates before each update, so a length-`k` path gives
`x₀ + ⋯ + xₖ₋₁`. Its last row choice is immaterial. The mean and second-moment
recurrences below use the same product row weights as `kaczmarzRowPathPMF`.
Source: Epperly–Goldshlager–Webber, arXiv:2411.19877v3, Theorems 2–3.
Atlas: `tail-averaged-kaczmarz` (finite-path sum kernel).
-/

noncomputable section
open scoped Matrix
namespace NLAlib.Kaczmarz
variable {m n : Type*} [Fintype m] [Fintype n]

/-- The sum of the first `k` actual iterates, including the starting point and excluding
the iterate after the final update. The last row choice is therefore unused. -/
def runSum (A : Matrix m n ℝ) (b : m → ℝ) :
    (k : ℕ) → (Fin k → m) → (n → ℝ) → (n → ℝ)
  | 0, _, _ => 0
  | k + 1, ω, x => x + runSum A b k (Fin.tail ω) (step A b x (ω 0))

omit [Fintype m] in
/-- The recursive sum is literally the sum of the native iterates along every prefix of
the sampled row path. In particular, it contains exactly `k` terms.
atlas: tail-averaged-kaczmarz (partial) -/
theorem runSum_eq_sum_prefix_run (A : Matrix m n ℝ) (b : m → ℝ)
    (k : ℕ) (ω : Fin k → m) (x : n → ℝ) :
    runSum A b k ω x = ∑ t : Fin k,
      run A b t (fun j => ω ⟨j.val, lt_trans j.isLt t.isLt⟩) x := by
  induction k generalizing x with
  | zero => simp [runSum]
  | succ k ih =>
    rw [runSum, Fin.sum_univ_succ]
    change x + runSum A b k (Fin.tail ω) (step A b x (ω 0)) = x + _
    rw [ih]
    congr 1

/-- The sum of the first `k` errors relative to a fixed reference point. -/
def runSumError (A : Matrix m n ℝ) (b : m → ℝ) (xs : n → ℝ)
    (k : ℕ) (ω : Fin k → m) (x : n → ℝ) : n → ℝ :=
  runSum A b k ω x - (k : ℝ) • xs

omit [Fintype m] in
@[simp] theorem runSumError_zero (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (ω : Fin 0 → m) : runSumError A b xs 0 ω x = 0 := by simp [runSumError, runSum]

omit [Fintype m] in
/-- First-step recursion of the sum of errors. -/
theorem runSumError_succ (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (k : ℕ) (ω : Fin (k + 1) → m) :
    runSumError A b xs (k + 1) ω x =
      (x - xs) + runSumError A b xs k (Fin.tail ω) (step A b x (ω 0)) := by
  simp only [runSumError, runSum, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  abel

/-- Exact expectation of the sum of errors under the independent row product weights. -/
theorem sum_paths_smul_runSumError_eq_sum_pow_mulVec [DecidableEq n]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) (x : n → ℝ) (k : ℕ) :
    (∑ ω : Fin k → m, (∏ j, prob A (ω j)) • runSumError A b xs k ω x) =
      ∑ t ∈ Finset.range k, (1 - (frobSq A)⁻¹ • (Aᵀ * A)) ^ t *ᵥ (x - xs) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ => m).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Fin.prod_univ_succ, Equiv.coe_fn_mk, Fin.cons_zero,
      Fin.cons_succ, runSumError_succ, Fin.tail_cons, mul_smul, smul_add]
    simp_rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul,
      sum_prod_prob A hA, one_smul, ih]
    rw [sum_prob A hA, one_smul, Finset.sum_range_succ']
    simp only [pow_zero, Matrix.one_mulVec]
    rw [add_comm]
    congr 1
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum, sum_prob_smul_step_sub_eq_mulVec A hA b xs x hxs,
      Matrix.mulVec_mulVec, pow_succ]

/-- Second-moment first-step identity. The cross term is the mean of the same correlated
trajectory; no independence of successive iterates is asserted. -/
theorem sum_paths_norm_runSumError_sq_succ (A : Matrix m n ℝ) (hA : A ≠ 0)
    (b : m → ℝ) (xs x : n → ℝ) (k : ℕ) :
    (∑ ω : Fin (k + 1) → m, (∏ j, prob A (ω j)) *
      ‖WithLp.toLp 2 (runSumError A b xs (k + 1) ω x)‖ ^ 2) =
      -‖WithLp.toLp 2 (x - xs)‖ ^ 2 +
      2 * ((x - xs) ⬝ᵥ (∑ ω : Fin (k + 1) → m,
        (∏ j, prob A (ω j)) • runSumError A b xs (k + 1) ω x)) +
      ∑ i, prob A i * (∑ ω : Fin k → m, (∏ j, prob A (ω j)) *
        ‖WithLp.toLp 2 (runSumError A b xs k ω (step A b x i))‖ ^ 2) := by
  simp only [norm_toLp_sq_eq_dotProduct_self]
  have he (ω : Fin (k + 1) → m) :
      runSumError A b xs (k + 1) ω x ⬝ᵥ runSumError A b xs (k + 1) ω x =
      -((x - xs) ⬝ᵥ (x - xs)) + 2 * ((x - xs) ⬝ᵥ runSumError A b xs (k + 1) ω x) +
      (runSumError A b xs k (Fin.tail ω) (step A b x (ω 0)) ⬝ᵥ
        runSumError A b xs k (Fin.tail ω) (step A b x (ω 0))) := by
    rw [runSumError_succ]
    simp only [add_dotProduct, dotProduct_add]
    rw [dotProduct_comm (runSumError A b xs k (Fin.tail ω) (step A b x (ω 0))) (x - xs)]
    ring
  simp_rw [he, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_mul, sum_prod_prob A hA, one_mul,
      dotProduct_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    rw [dotProduct_smul, smul_eq_mul]
    ring
  · rw [← (Fin.consEquiv fun _ => m).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [Fin.consEquiv, Fin.prod_univ_succ, Equiv.coe_fn_mk, Fin.cons_zero,
      Fin.cons_succ, Fin.tail_cons, mul_assoc]

end NLAlib.Kaczmarz
