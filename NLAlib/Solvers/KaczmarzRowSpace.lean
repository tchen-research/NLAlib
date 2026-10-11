import NLAlib.Solvers.KaczmarzExtensions
import NLAlib.Solvers.KaczmarzProbability

/-!
# Inconsistent randomized Kaczmarz on the row space

The initial error must lie in `range Aᵀ` when the lower singular bound is assumed only
there. Every affine row update preserves this error membership, including inconsistent
right-hand sides. The exact geometric noise sum and its horizon bound therefore require
no full-column-rank assumption. The final corollaries identify the finite recurrence with
the expectation of the actual iid row-path distribution for nonzero inputs.

Needell 2010, Theorem 2.1; Zouzias–Freris 2013, equation (5).
Atlas: `kaczmarz-inconsistent`.
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix
open Matrix MeasureTheory

namespace NLAlib

namespace Kaczmarz

variable {m n : Type*} [Fintype m] [Fintype n]

/-- An arbitrary affine Kaczmarz update preserves row-space error membership.
No consistency assumption on the right-hand side or reference point is needed.
Needell 2010, proof of Theorem 2.1; atlas `kaczmarz-inconsistent` (invariant helper). -/
theorem step_sub_mem_range_of_sub_mem_range [DecidableEq m]
    (A : Matrix m n ℝ) (b : m → ℝ) (xh x : n → ℝ)
    (hx : x - xh ∈ LinearMap.range Aᵀ.mulVecLin) (i : m) :
    step A b x i - xh ∈ LinearMap.range Aᵀ.mulVecLin := by
  have hstep : step A b x i - xh =
      (x - xh) + ((b i - A i ⬝ᵥ x) / (A i ⬝ᵥ A i)) • A i := by
    simp only [step]
    abel
  rw [hstep]
  refine Submodule.add_mem _ hx (Submodule.smul_mem _ _ ⟨Pi.single i 1, ?_⟩)
  ext j
  simp

/-- A lower singular bound on the row space makes the Kaczmarz contraction
factor nonnegative, including a zero matrix and empty index types.
Zouzias–Freris 2013, equation (5); atlas `kaczmarz-inconsistent` (rate helper). -/
theorem rate_nonneg_of_lower_bound_on_range [DecidableEq m]
    (A : Matrix m n ℝ) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) :
    0 ≤ 1 - σ ^ 2 / frobSq A := by
  classical
  by_cases hA : A = 0
  · subst hA
    simp
  have hF : 0 < frobSq A :=
    lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  obtain ⟨i, hi⟩ : ∃ i, A i ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.ext fun i j => by simp [h i])
  have hmem : A i ∈ LinearMap.range Aᵀ.mulVecLin := ⟨Pi.single i 1, by
    ext j
    simp⟩
  have hpos : 0 < A i ⬝ᵥ A i := lt_of_le_of_ne (dotProduct_self_nonneg _)
    (Ne.symm fun h => hi (dotProduct_self_eq_zero.mp h))
  have hbound : σ ^ 2 ≤ frobSq A := le_of_mul_le_mul_right
    ((hσ _ hmem).trans (mulVec_dotProduct_mulVec_le_frobSq_mul A (A i))) hpos
  rw [sub_nonneg, div_le_one hF]
  exact hbound

/-- One inconsistent-system Kaczmarz step contracts a row-space error, with
additive noise `‖b-A*xh‖²/‖A‖F²`. The lower singular bound is needed only on
the row space. Needell 2010, proof of Theorem 2.1;
atlas `kaczmarz-inconsistent` (one-step helper). -/
theorem expected_sqErr_step_le_add_of_sub_mem_range [DecidableEq m]
    (A : Matrix m n ℝ) (b : m → ℝ) (xh x : n → ℝ) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (hx : x - xh ∈ LinearMap.range Aᵀ.mulVecLin) :
    ∑ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) ≤
      (1 - σ ^ 2 / frobSq A) * ((x - xh) ⬝ᵥ (x - xh)) +
        (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A := by
  by_cases hA : A = 0
  · subst hA
    simp only [prob, frobSq_zero, div_zero, zero_mul, Finset.sum_const_zero, sub_zero,
      one_mul, add_zero]
    exact dotProduct_self_nonneg _
  have hF : 0 < frobSq A :=
    lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hterm : ∀ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) ≤
      prob A i * ((x - xh) ⬝ᵥ (x - xh)) - (A i ⬝ᵥ (x - xh)) ^ 2 / frobSq A +
        (b - A *ᵥ xh) i ^ 2 / frobSq A := fun i => by
    rw [sqErr_step_eq_add A b xh x i]
    have hei : (b - A *ᵥ xh) i = b i - A i ⬝ᵥ xh := rfl
    rw [hei]
    by_cases ha : A i ⬝ᵥ A i = 0
    · have h0 : A i = 0 := dotProduct_self_eq_zero.mp ha
      have hp : prob A i = 0 := by simp [prob, h0]
      rw [hp, h0]
      simp only [zero_mul, zero_dotProduct, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div, zero_add]
      exact div_nonneg (sq_nonneg _) (frobSq_nonneg A)
    · rw [prob]
      apply le_of_eq
      field_simp
  set d := x - xh
  set e := b - A *ᵥ xh
  calc ∑ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh))
      ≤ ∑ i, (prob A i * (d ⬝ᵥ d) - (A i ⬝ᵥ d) ^ 2 / frobSq A + e i ^ 2 / frobSq A) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = d ⬝ᵥ d - (A *ᵥ d) ⬝ᵥ (A *ᵥ d) / frobSq A + e ⬝ᵥ e / frobSq A := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_prob A hA,
          one_mul, ← Finset.sum_div, ← Finset.sum_div, mulVec_dotProduct_mulVec_eq_sum_sq]
        simp only [dotProduct, sq]
    _ ≤ (1 - σ ^ 2 / frobSq A) * (d ⬝ᵥ d) + e ⬝ᵥ e / frobSq A := by
        have h := div_le_div_of_nonneg_right (hσ _ hx) hF.le
        rw [sub_mul, one_mul, div_mul_eq_mul_div]
        linarith

/-- Inconsistent randomized Kaczmarz obeys the exact geometric-noise bound
when the initial error lies in the row space and the lower singular bound holds
only there. The reference point is arbitrary, and no rank assumption is needed.
Needell 2010, Theorem 2.1; Zouzias–Freris 2013, equation (5).
atlas: kaczmarz-inconsistent -/
theorem expErr_le_add_of_sub_mem_range [DecidableEq m]
    (A : Matrix m n ℝ) (b : m → ℝ) (xh : n → ℝ) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (x : n → ℝ) (hx : x - xh ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    expErr A b xh x k ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((x - xh) ⬝ᵥ (x - xh)) +
      (∑ j ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ j) *
        ((b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A) := by
  classical
  set ρ := 1 - σ ^ 2 / frobSq A
  set c := (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A
  have hc : 0 ≤ c := div_nonneg (dotProduct_self_nonneg _) (frobSq_nonneg A)
  have hρ : 0 ≤ ρ := rate_nonneg_of_lower_bound_on_range A σ hσ
  have hsum1 : ∑ i, prob A i ≤ 1 := by
    by_cases hA : A = 0
    · subst hA
      simp [prob]
    · rw [sum_prob A hA]
  induction k generalizing x with
  | zero => simp [expErr_zero]
  | succ k ih =>
    rw [expErr_succ, Finset.sum_range_succ]
    have hS : 0 ≤ ∑ j ∈ Finset.range k, ρ ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg hρ j
    generalize ∑ j ∈ Finset.range k, ρ ^ j = T at ih hS ⊢
    calc ∑ i, prob A i * expErr A b xh (step A b x i) k
        ≤ ∑ i, prob A i * (ρ ^ k * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) + T * c) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (ih _ (step_sub_mem_range_of_sub_mem_range A b xh x hx i)) (prob_nonneg A i)
      _ = ρ ^ k * ∑ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) +
          (∑ i, prob A i) * (T * c) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ρ ^ k * (ρ * ((x - xh) ⬝ᵥ (x - xh)) + c) + 1 * (T * c) := by
          gcongr
          exact expected_sqErr_step_le_add_of_sub_mem_range A b xh x σ hσ hx
      _ = ρ ^ (k + 1) * ((x - xh) ⬝ᵥ (x - xh)) + (T + ρ ^ k) * c := by ring

/-- The row-space inconsistent Kaczmarz bound has noise horizon
`‖b-A*xh‖²/σ²` when `σ>0`. No full-column-rank assumption is required.
Needell 2010, Theorem 2.1; Zouzias–Freris 2013, equation (5).
atlas: kaczmarz-inconsistent -/
theorem expErr_le_add_div_sq_of_sub_mem_range [DecidableEq m]
    (A : Matrix m n ℝ) (b : m → ℝ) (xh : n → ℝ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (x : n → ℝ) (hx : x - xh ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    expErr A b xh x k ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((x - xh) ⬝ᵥ (x - xh)) +
      (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / σ ^ 2 := by
  classical
  refine (expErr_le_add_of_sub_mem_range A b xh σ hσ x hx k).trans
    (add_le_add le_rfl ?_)
  set c := (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh)
  have hc : 0 ≤ c := dotProduct_self_nonneg _
  by_cases hA : A = 0
  · subst hA
    simp only [frobSq_zero, div_zero, mul_zero]
    positivity
  have hF : 0 < frobSq A :=
    lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hρ0 := rate_nonneg_of_lower_bound_on_range A σ hσ
  have hρ1 : 1 - σ ^ 2 / frobSq A < 1 := by
    have : 0 < σ ^ 2 / frobSq A := div_pos (by positivity) hF
    linarith
  have hgeom : ∑ i ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ i ≤ frobSq A / σ ^ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hρ0 hρ1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  calc (∑ i ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ i) * (c / frobSq A)
      ≤ frobSq A / σ ^ 2 * (c / frobSq A) :=
        mul_le_mul_of_nonneg_right hgeom (div_nonneg hc hF.le)
    _ = c / σ ^ 2 := by field_simp

end Kaczmarz

/-- The exact row-space geometric-noise bound holds for the actual iid row-path
probability expectation of inconsistent Kaczmarz. Nonzero input makes the row
weights a probability distribution. Needell 2010, Theorem 2.1;
Zouzias–Freris 2013, equation (5).
atlas: kaczmarz-inconsistent -/
theorem integral_sqErr_kaczmarz_le_add_of_sub_mem_range
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xh : n → ℝ) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (x : n → ℝ) (hx : x - xh ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    (∫ ω : Fin k → m, (Kaczmarz.run A b k ω x - xh) ⬝ᵥ (Kaczmarz.run A b k ω x - xh)
      ∂(kaczmarzRowPathPMF A hA k).toMeasure) ≤
      (1 - σ ^ 2 / frobSq A) ^ k * ((x - xh) ⬝ᵥ (x - xh)) +
        (∑ j ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ j) *
          ((b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A) := by
  rw [integral_sqErr_kaczmarzRowPathPMF A hA b xh x k]
  exact Kaczmarz.expErr_le_add_of_sub_mem_range A b xh σ hσ x hx k

/-- The row-space horizon bound holds for the actual iid row-path probability
expectation, with an arbitrary reference point, `σ>0`, and no rank assumption.
Needell 2010, Theorem 2.1; Zouzias–Freris 2013, equation (5).
atlas: kaczmarz-inconsistent -/
theorem integral_sqErr_kaczmarz_le_add_div_sq_of_sub_mem_range
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xh : n → ℝ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (x : n → ℝ) (hx : x - xh ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    (∫ ω : Fin k → m, (Kaczmarz.run A b k ω x - xh) ⬝ᵥ (Kaczmarz.run A b k ω x - xh)
      ∂(kaczmarzRowPathPMF A hA k).toMeasure) ≤
      (1 - σ ^ 2 / frobSq A) ^ k * ((x - xh) ⬝ᵥ (x - xh)) +
        (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / σ ^ 2 := by
  rw [integral_sqErr_kaczmarzRowPathPMF A hA b xh x k]
  exact Kaczmarz.expErr_le_add_div_sq_of_sub_mem_range A b xh hσ0 hσ x hx k

end NLAlib
