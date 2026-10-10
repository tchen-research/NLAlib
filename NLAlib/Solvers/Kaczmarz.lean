import NLAlib.Matrix.Norms
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Randomized Kaczmarz

Strohmer–Vershynin 2009, *A randomized Kaczmarz algorithm with exponential convergence*,
Theorem 2 (atlas `randomized-kaczmarz`).

Let `A` be a real matrix with rows `A i`, `b` a right-hand side and `xs` a solution,
`A *ᵥ xs = b`. One Kaczmarz step on row `i` projects the iterate onto the hyperplane
`{y | A i ⬝ᵥ y = b i}`:
`step A b x i = x + ((b i - A i ⬝ᵥ x) / (A i ⬝ᵥ A i)) • A i`.
Row `i` is drawn with probability `prob A i = ‖A i‖² / ‖A‖_F²`.

To avoid measure theory, expectations are finite weighted sums: `expErr A b xs x k` is the
expected squared error `E‖x_k - xs‖²` after `k` i.i.d. randomized steps started at `x`, defined
by first-step recursion, and `expErr_eq_sum_paths` identifies it with the explicit sum over all
row sequences `ω : Fin k → m` weighted by `∏ j, prob A (ω j)`.

Squared Euclidean norms are written `v ⬝ᵥ v`. The row identities `‖A‖_F² = ∑ᵢ ‖Aᵢ‖²`
(`NLAlib.frobSq_eq_sum_dotProduct_self`), `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`
(`NLAlib.mulVec_dotProduct_mulVec_eq_sum_sq`) and `v ⬝ v ≥ 0` (`NLAlib.dotProduct_self_nonneg`)
are in `NLAlib.Matrix.Norms`.

## Main results

* `Kaczmarz.step_sub_solution`, `Kaczmarz.sqErr_step`: the error recursion and Pythagoras.
* `Kaczmarz.expected_sqErr_step_eq`: `E‖x₁ - xs‖² = ‖x - xs‖² - ‖A (x - xs)‖² / ‖A‖_F²`.
* `Kaczmarz.expected_sqErr_step_le`: one-step contraction by `1 - σ² / ‖A‖_F²`.
* `Kaczmarz.expErr_le`: **SV09 Thm 2**, `E‖x_k - xs‖² ≤ (1 - σ² / ‖A‖_F²)^k ‖x₀ - xs‖²`.

The smallest singular value enters through the hypothesis
`hσ : ∀ v, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)` (any lower bound on `σ_min(A)²`, atlas
`courant-fischer`); SV09 write the rate as `1 - κ(A)⁻²` with `κ(A) = ‖A‖_F ‖A⁻¹‖`, i.e.
`σ = ‖A⁻¹‖⁻¹`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

namespace Kaczmarz

variable {m n : Type*} [Fintype m] [Fintype n]

/-- One Kaczmarz step on row `i`: the orthogonal projection of `x` onto the hyperplane
`{y | A i ⬝ᵥ y = b i}`. For a zero row the step is the identity (real division by zero is `0`).
Strohmer–Vershynin 2009, Algorithm (eq. (2)); atlas `randomized-kaczmarz`.
atlas: kaczmarz-def -/
def step (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) (i : m) : n → ℝ :=
  x + ((b i - A i ⬝ᵥ x) / (A i ⬝ᵥ A i)) • A i

/-- Row-selection probability `‖A i‖² / ‖A‖_F²` of randomized Kaczmarz.
Strohmer–Vershynin 2009, Algorithm; atlas `randomized-kaczmarz`.
atlas: kaczmarz-def -/
def prob (A : Matrix m n ℝ) (i : m) : ℝ :=
  (A i ⬝ᵥ A i) / frobSq A

/-- Expected squared error `E‖x_k - xs‖²` after `k` randomized Kaczmarz steps started at `x`,
rows drawn i.i.d. with probabilities `prob A`. Defined by first-step recursion:
`expErr 0 x = ‖x - xs‖²`, `expErr (k+1) x = ∑ i, prob A i * expErr k (step A b x i)`.
See `expErr_eq_sum_paths` for the path-sum form. Atlas `randomized-kaczmarz`.
atlas: kaczmarz-def -/
def expErr (A : Matrix m n ℝ) (b : m → ℝ) (xs : n → ℝ) : (n → ℝ) → ℕ → ℝ
  | x, 0 => (x - xs) ⬝ᵥ (x - xs)
  | x, k + 1 => ∑ i, prob A i * expErr A b xs (step A b x i) k

/-- The iterate after applying the steps with rows `ω 0, ω 1, …, ω (k-1)` in that order,
starting from `x`. Atlas `randomized-kaczmarz`.
atlas: kaczmarz-def -/
def run (A : Matrix m n ℝ) (b : m → ℝ) : (k : ℕ) → (Fin k → m) → (n → ℝ) → (n → ℝ)
  | 0, _, x => x
  | k + 1, ω, x => run A b k (Fin.tail ω) (step A b x (ω 0))

/-- Selection probabilities are nonnegative. Atlas `randomized-kaczmarz`. -/
theorem prob_nonneg (A : Matrix m n ℝ) (i : m) : 0 ≤ prob A i :=
  div_nonneg (dotProduct_self_nonneg _) (frobSq_nonneg A)

/-- The selection probabilities sum to one when `A ≠ 0`. Atlas `randomized-kaczmarz`. -/
theorem sum_prob (A : Matrix m n ℝ) (hA : A ≠ 0) : ∑ i, prob A i = 1 := by
  have hF : frobSq A ≠ 0 := (frobSq_eq_zero_iff A).not.mpr hA
  unfold prob
  rw [← Finset.sum_div, ← frobSq_eq_sum_dotProduct_self, div_self hF]

omit [Fintype m] in
/-- Error recursion of one Kaczmarz step when `A *ᵥ xs = b`:
`step A b x i - xs = (x - xs) - ((A i ⬝ᵥ (x - xs)) / ‖A i‖²) • A i`.
Strohmer–Vershynin 2009, proof of Thm 2; atlas `randomized-kaczmarz`. -/
theorem step_sub_solution (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ) (hxs : A *ᵥ xs = b)
    (i : m) :
    step A b x i - xs = (x - xs) - ((A i ⬝ᵥ (x - xs)) / (A i ⬝ᵥ A i)) • A i := by
  have hb : b i = A i ⬝ᵥ xs := by rw [← hxs]; rfl
  rw [step, hb, dotProduct_sub, ← neg_sub (A i ⬝ᵥ x), neg_div, neg_smul]
  abel

omit [Fintype m] in
/-- Pythagoras for one Kaczmarz step (the step is an orthogonal projection onto a hyperplane
containing `xs`): `‖step A b x i - xs‖² = ‖x - xs‖² - (A i ⬝ᵥ (x - xs))² / ‖A i‖²`.
Holds for every row; for a zero row both sides equal `‖x - xs‖²`.
Strohmer–Vershynin 2009, proof of Thm 2; atlas `randomized-kaczmarz`. -/
theorem sqErr_step (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ) (hxs : A *ᵥ xs = b) (i : m) :
    (step A b x i - xs) ⬝ᵥ (step A b x i - xs) =
      (x - xs) ⬝ᵥ (x - xs) - (A i ⬝ᵥ (x - xs)) ^ 2 / (A i ⬝ᵥ A i) := by
  rw [step_sub_solution A b xs x hxs i]
  set e := x - xs
  set a := A i
  set t := (a ⬝ᵥ e) / (a ⬝ᵥ a)
  have hae : e ⬝ᵥ a = a ⬝ᵥ e := dotProduct_comm _ _
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hae]
  by_cases ha : a ⬝ᵥ a = 0
  · simp [t, ha]
  · simp only [t]
    field_simp
    ring

/-- One-step expected error identity:
`∑ i, prob A i * ‖step A b x i - xs‖² = ‖x - xs‖² - ‖A (x - xs)‖² / ‖A‖_F²` for `A ≠ 0`.
Strohmer–Vershynin 2009, proof of Thm 2; atlas `randomized-kaczmarz`. -/
theorem expected_sqErr_step_eq (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (hxs : A *ᵥ xs = b) (hA : A ≠ 0) :
    ∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs)) =
      (x - xs) ⬝ᵥ (x - xs) - (A *ᵥ (x - xs)) ⬝ᵥ (A *ᵥ (x - xs)) / frobSq A := by
  simp_rw [sqErr_step A b xs x hxs, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_prob A hA, one_mul, mulVec_dotProduct_mulVec_eq_sum_sq, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prob]
  by_cases ha : A i ⬝ᵥ A i = 0
  · have : A i = 0 := dotProduct_self_eq_zero.mp ha
    simp [this]
  · field_simp

/-- One-step contraction of randomized Kaczmarz: if `σ² ‖v‖² ≤ ‖A v‖²` for all `v`
(`σ` a lower bound on the smallest singular value, atlas `courant-fischer`), then
`∑ i, prob A i * ‖step A b x i - xs‖² ≤ (1 - σ² / ‖A‖_F²) ‖x - xs‖²`.
No hypothesis on `A` (for `A = 0` the left side is `0` and the rate is `1`).
Strohmer–Vershynin 2009, proof of Thm 2; atlas `randomized-kaczmarz`. -/
theorem expected_sqErr_step_le (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (hxs : A *ᵥ xs = b) (σ : ℝ) (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) :
    ∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs)) ≤
      (1 - σ ^ 2 / frobSq A) * ((x - xs) ⬝ᵥ (x - xs)) := by
  by_cases hA : A = 0
  · subst hA
    simp only [prob, frobSq_zero, div_zero, zero_mul, Finset.sum_const_zero, sub_zero, one_mul]
    exact dotProduct_self_nonneg _
  rw [expected_sqErr_step_eq A b xs x hxs hA]
  have hF : 0 < frobSq A :=
    lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have h := div_le_div_of_nonneg_right (hσ (x - xs)) hF.le
  rw [sub_mul, one_mul, div_mul_eq_mul_div]
  linarith

/-- The contraction factor is nonnegative when `n` is nonempty: `σ² ≤ ‖A‖_F²`.
Atlas `randomized-kaczmarz`. -/
theorem rate_nonneg [Nonempty n] (A : Matrix m n ℝ) (σ : ℝ)
    (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) :
    0 ≤ 1 - σ ^ 2 / frobSq A := by
  classical
  obtain ⟨j⟩ := ‹Nonempty n›
  set e : n → ℝ := Pi.single j 1
  have he : e ⬝ᵥ e = 1 := by simp [e]
  have h := expected_sqErr_step_le A 0 0 e (by simp) σ hσ
  simp only [sub_zero, he, mul_one] at h
  refine le_trans ?_ h
  exact Finset.sum_nonneg fun i _ => mul_nonneg (prob_nonneg A i) (dotProduct_self_nonneg _)

/-- Unfolding `expErr` at `0` steps. Atlas `randomized-kaczmarz`. -/
theorem expErr_zero (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ) :
    expErr A b xs x 0 = (x - xs) ⬝ᵥ (x - xs) := rfl

/-- Unfolding `expErr` at `k + 1` steps (first-step analysis). Atlas `randomized-kaczmarz`. -/
theorem expErr_succ (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ) (k : ℕ) :
    expErr A b xs x (k + 1) = ∑ i, prob A i * expErr A b xs (step A b x i) k := rfl

/-- **Randomized Kaczmarz converges linearly in expectation.**
Strohmer–Vershynin 2009, Thm 2; atlas `randomized-kaczmarz`.
If `A *ᵥ xs = b` and `σ² ‖v‖² ≤ ‖A v‖²` for all `v`, then after `k` steps with rows drawn
i.i.d. with probability `‖A i‖² / ‖A‖_F²`,
`E‖x_k - xs‖² ≤ (1 - σ² / ‖A‖_F²)^k ‖x₀ - xs‖²`.
Deviations from the printed statement: SV09 take `A` of full column rank and `σ = ‖A⁻¹‖⁻¹`
(rate `1 - κ(A)⁻²`); here `σ` is any constant satisfying `hσ` (the sharp choice is
`σ_min(A)`, atlas `courant-fischer`), and no rank or nonzero-row assumption is needed.
atlas: randomized-kaczmarz -/
theorem expErr_le (A : Matrix m n ℝ) (b : m → ℝ) (xs : n → ℝ) (hxs : A *ᵥ xs = b) (σ : ℝ)
    (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) (x : n → ℝ) (k : ℕ) :
    expErr A b xs x k ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · -- all vectors vanish
    have h0 : ∀ v : n → ℝ, v ⬝ᵥ v = 0 := fun v => by simp [dotProduct]
    have : ∀ k (x : n → ℝ), expErr A b xs x k = 0 := by
      intro k
      induction k with
      | zero => intro x; exact h0 _
      | succ k ih => intro x; simp [expErr_succ, ih]
    rw [this, h0, mul_zero]
  · have hρ := rate_nonneg A σ hσ
    induction k generalizing x with
    | zero => simp [expErr_zero]
    | succ k ih =>
      rw [expErr_succ]
      calc ∑ i, prob A i * expErr A b xs (step A b x i) k
          ≤ ∑ i, prob A i * ((1 - σ ^ 2 / frobSq A) ^ k *
              ((step A b x i - xs) ⬝ᵥ (step A b x i - xs))) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih _) (prob_nonneg A i)
        _ = (1 - σ ^ 2 / frobSq A) ^ k *
              ∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs)) := by
            rw [Finset.mul_sum]; congr 1; ext i; ring
        _ ≤ (1 - σ ^ 2 / frobSq A) ^ k *
              ((1 - σ ^ 2 / frobSq A) * ((x - xs) ⬝ᵥ (x - xs))) :=
            mul_le_mul_of_nonneg_left (expected_sqErr_step_le A b xs x hxs σ hσ)
              (pow_nonneg hρ k)
        _ = (1 - σ ^ 2 / frobSq A) ^ (k + 1) * ((x - xs) ⬝ᵥ (x - xs)) := by ring

/-- `expErr` is the expectation over i.i.d. row sequences: the sum over all `ω : Fin k → m` of
`(∏ j, prob A (ω j)) * ‖run A b k ω x - xs‖²`. Atlas `randomized-kaczmarz`. -/
theorem expErr_eq_sum_paths (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ) (k : ℕ) :
    expErr A b xs x k = ∑ ω : Fin k → m,
      (∏ j, prob A (ω j)) * ((run A b k ω x - xs) ⬝ᵥ (run A b k ω x - xs)) := by
  induction k generalizing x with
  | zero => simp [expErr_zero, run]
  | succ k ih =>
    rw [expErr_succ, ← (Fin.consEquiv fun _ => m).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp [Fin.consEquiv, run, Fin.prod_univ_succ, mul_assoc]

/-- Path-sum form of SV09 Thm 2: the weighted average over all row sequences of length `k` of
the squared error is at most `(1 - σ² / ‖A‖_F²)^k ‖x - xs‖²`.
Strohmer–Vershynin 2009, Thm 2; atlas `randomized-kaczmarz`. -/
theorem sum_paths_le (A : Matrix m n ℝ) (b : m → ℝ) (xs : n → ℝ) (hxs : A *ᵥ xs = b) (σ : ℝ)
    (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) (x : n → ℝ) (k : ℕ) :
    ∑ ω : Fin k → m,
      (∏ j, prob A (ω j)) * ((run A b k ω x - xs) ⬝ᵥ (run A b k ω x - xs)) ≤
      (1 - σ ^ 2 / frobSq A) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  rw [← expErr_eq_sum_paths]
  exact expErr_le A b xs hxs σ hσ x k

end Kaczmarz

end NLAlib

