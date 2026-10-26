/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Kaczmarz.KaczmarzRowSpace
import NLAlib.Matrix.Basic.LeastSquares

/-!
# Mean propagation for randomized Kaczmarz

The expected error of the actual independently sampled row iterates propagates by
`I - Aᵀ A / ‖A‖F²` around any least-squares solution. Zero rows cause no exception:
their probability and their contribution to the normal-equations mean both vanish.
The resulting finite-path identity is a building block for tail averaging.

Source: Epperly–Goldshlager–Webber 2024, tail-averaged randomized Kaczmarz, conditional-mean argument.
Atlas: `tail-averaged-kaczmarz` (mean kernel).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib.Kaczmarz

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The mean one-step error is the normal-equations update. This formula also holds for
inconsistent systems and rank-deficient matrices. -/
theorem sum_prob_smul_step_sub_eq (A : Matrix m n ℝ) (hA : A ≠ 0)
    (b : m → ℝ) (xs x : n → ℝ) :
    (∑ i, prob A i • (step A b x i - xs)) =
      (x - xs) + (frobSq A)⁻¹ • (Aᵀ *ᵥ (b - A *ᵥ x)) := by
  classical
  have hrow (i : m) :
      prob A i • (((b i - A i ⬝ᵥ x) / (A i ⬝ᵥ A i)) • A i) =
        ((frobSq A)⁻¹ * (b i - A i ⬝ᵥ x)) • A i := by
    by_cases hi : A i ⬝ᵥ A i = 0
    · simp [dotProduct_self_eq_zero.mp hi]
    · rw [smul_smul, prob]
      congr 1
      field_simp
  have hs (i : m) : step A b x i - xs =
      (x - xs) + ((b i - A i ⬝ᵥ x) / (A i ⬝ᵥ A i)) • A i := by
    rw [step]
    abel
  simp_rw [hs, smul_add, hrow]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, sum_prob A hA, one_smul]
  congr 1
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Pi.sub_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Around a least-squares solution the one-step expected error is multiplication by
the symmetric mean error operator. -/
theorem sum_prob_smul_step_sub_eq_mulVec [DecidableEq n]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs x : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) :
    (∑ i, prob A i • (step A b x i - xs)) =
      (1 - (frobSq A)⁻¹ • (Aᵀ * A)) *ᵥ (x - xs) := by
  rw [sum_prob_smul_step_sub_eq A hA b xs x, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  have he : Aᵀ *ᵥ (b - A *ᵥ x) = -(Aᵀ *ᵥ (A *ᵥ (x - xs))) := by
    have hn := (isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq A b xs).mp hxs
    simp only [Matrix.mulVec_sub]
    rw [← hn]
    abel
  rw [he, smul_neg]
  abel

/-- The product weights on row paths sum to one for every path length. -/
theorem sum_prod_prob (A : Matrix m n ℝ) (hA : A ≠ 0) (k : ℕ) :
    (∑ ω : Fin k → m, ∏ j, prob A (ω j)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [sum_prob A hA, Finset.prod_const_one]

/-- **Exact finite-path mean.** No independence between iterates is assumed: the independent
row choices are encoded by the product weights of the actual `run` recurrence. -/
theorem sum_paths_smul_run_sub_eq_pow_mulVec [DecidableEq n]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) (x : n → ℝ) (k : ℕ) :
    (∑ ω : Fin k → m, (∏ j, prob A (ω j)) • (run A b k ω x - xs)) =
      (1 - (frobSq A)⁻¹ • (Aᵀ * A)) ^ k *ᵥ (x - xs) := by
  induction k generalizing x with
  | zero => simp [run]
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ => m).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Fin.prod_univ_succ, Equiv.coe_fn_mk, Fin.cons_zero,
      Fin.cons_succ, run, Fin.tail_cons, mul_smul]
    simp_rw [← Finset.smul_sum, ih]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum, sum_prob_smul_step_sub_eq_mulVec A hA b xs x hxs]
    rw [Matrix.mulVec_mulVec, pow_succ]

/-- The exact mean formula is an integral under the native iid row-path law. -/
theorem integral_run_sub_eq_pow_mulVec [DecidableEq n]
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) (x : n → ℝ) (k : ℕ) :
    (∫ ω : Fin k → m, run A b k ω x - xs ∂(kaczmarzRowPathPMF A hA k).toMeasure) =
      (1 - (frobSq A)⁻¹ • (Aᵀ * A)) ^ k *ᵥ (x - xs) := by
  classical
  rw [PMF.integral_eq_sum]
  have hw (ω : Fin k → m) : (kaczmarzRowPathPMF A hA k ω).toReal =
      ∏ j, prob A (ω j) := by
    simp only [kaczmarzRowPathPMF, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => prob_nonneg A (ω j))
  simp_rw [hw]
  exact sum_paths_smul_run_sub_eq_pow_mulVec A hA b xs hxs x k

end NLAlib.Kaczmarz
