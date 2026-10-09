import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import NLAlib.Estimation.Basic
import NLAlib.Matrix.Norms

/-!
# Hutchinson's trace estimator: unbiasedness and variance

Hutchinson's estimator is the quadratic form `zᵀ A z` (`NLAlib.quadForm`) at an isotropic random
vector `z`.

## Main results

* `NLAlib.integral_quadForm_eq_trace` (`hutchinson-unbiased`): if the coordinates of `z` are
  pairwise independent, centred, with unit second moment, then `𝔼[zᵀ A z] = tr A`.
* `NLAlib.variance_quadForm` (`hutchinson-variance`): if the coordinates are (mutually)
  independent, centred, with unit variance and common fourth moment `m₄`, then
  `Var[zᵀ A z] = ∑ᵢⱼ A_ij² + ∑ᵢⱼ A_ij A_ji + (m₄ − 3) ∑ᵢ A_ii²`.
  Specialisations: symmetric `A` (`variance_quadForm_of_isSymm`), Gaussian-like `m₄ = 3`
  (`variance_quadForm_of_isSymm_of_fourth_moment_eq_three`, `= 2‖A‖_F²`) and Rademacher-like
  `m₄ = 1` (`variance_quadForm_of_isSymm_of_fourth_moment_eq_one`, `= 2(‖A‖_F² − ∑ A_ii²)`).

Helpers: second and fourth mixed moments of the coordinates
(`integral_coord_mul_coord`, `integral_coord_mul_coord_mul_coord_mul_coord`) and the index
contraction `sum_fourth_moment_contraction`.

Atlas: `hutchinson-unbiased`, `hutchinson-variance`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- Expansion `(zᵀ A z)² = ∑ᵢⱼₖₗ A_ij A_kl z_i z_j z_k z_l`. Atlas: `hutchinson-variance`
(helper). -/
theorem quadForm_sq_eq_sum (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (z i * z j * z k * z l) := by
  rw [sq, quadForm_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ### Elementary inequalities used for integrability -/

private lemma abs_mul_le_sq_add_sq (a b : ℝ) : |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b, sq_nonneg (|a| - |b|)]

private lemma abs_mul_mul_mul_le_sum_pow_four (a b c d : ℝ) :
    |a * b * c * d| ≤ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b, sq_nonneg (|a| - |b|)]
  have h2 : |c * d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_abs c, sq_abs d, abs_nonneg c, abs_nonneg d, sq_nonneg (|c| - |d|)]
  have e : |a * b * c * d| = |a * b| * |c * d| := by rw [mul_assoc, abs_mul]
  rw [e]
  have h3 : |a * b| * |c * d| ≤ (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + d ^ 2) / 2) :=
    mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (c ^ 2 - d ^ 2)]

private lemma abs_sq_le_one_add_pow_four (a : ℝ) : |a ^ 2| ≤ 1 + a ^ 4 := by
  rw [abs_of_nonneg (sq_nonneg a)]
  nlinarith [sq_nonneg (a ^ 2 - 1)]

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [Fintype n] in
/-- Products of two square-integrable real random variables are integrable. -/
private lemma integrable_coord_mul_coord {z : Ω → n → ℝ} (hz : ∀ i, MemLp (fun ω => z ω i) 2 μ)
    (i j : n) : Integrable (fun ω => z ω i * z ω j) μ := by
  refine Integrable.mono' ((hz i).integrable_sq.add (hz j).integrable_sq)
    ((hz i).aestronglyMeasurable.mul (hz j).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using abs_mul_le_sq_add_sq (z ω i) (z ω j)

omit [Fintype n] in
/-- Second moments of an isotropic vector with pairwise independent coordinates:
`𝔼[z_i z_j] = δ_ij`. Atlas: `hutchinson-unbiased` (helper). -/
theorem integral_coord_mul_coord [DecidableEq n] {z : Ω → n → ℝ}
    (hz : ∀ i, MemLp (fun ω => z ω i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (fun ω => z ω i) (fun ω => z ω j) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1) (i j : n) :
    ∫ ω, z ω i * z ω j ∂μ = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    simpa [sq] using hsq i
  · rw [(hind i j h).integral_fun_mul_eq_mul_integral (hz i).aestronglyMeasurable
      (hz j).aestronglyMeasurable]
    rw [hmean i, zero_mul]

/-- **Hutchinson's estimator is unbiased.** If the coordinates `z_i` of a random vector are
square-integrable, pairwise independent, centred and have unit second moment, then
`𝔼[zᵀ A z] = tr A`.
Source: Hutchinson (1989) [`hutch89`]; Avron–Toledo (2011) [`at11`].
Atlas: `hutchinson-unbiased`.
Deviation: stated for any isotropic vector with pairwise independent coordinates (only
`𝔼[z_i z_j] = δ_ij` is used); the source states it for Rademacher `z`. -/
theorem integral_quadForm_eq_trace [IsProbabilityMeasure μ] (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hz : ∀ i, MemLp (fun ω => z ω i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (fun ω => z ω i) (fun ω => z ω j) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1) :
    ∫ ω, quadForm A (z ω) ∂μ = A.trace := by
  classical
  simp_rw [quadForm_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_coord_mul_coord hz i j).const_mul (A i j)]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (integrable_coord_mul_coord hz i j).const_mul (A i j)]
  simp_rw [integral_const_mul, integral_coord_mul_coord hz hind hmean hsq]
  simp

/-! ### Fourth moments and the variance identity -/

omit [Fintype n] in
private lemma integrable_coord_mul_coord_mul_coord_mul_coord {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ) (i j k l : n) :
    Integrable (fun ω => z ω i * z ω j * z ω k * z ω l) μ := by
  refine Integrable.mono' ((((h4 i).add (h4 j)).add (h4 k)).add (h4 l))
    ((((hmeas i).aestronglyMeasurable.mul (hmeas j).aestronglyMeasurable).mul
      (hmeas k).aestronglyMeasurable).mul (hmeas l).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using abs_mul_mul_mul_le_sum_pow_four (z ω i) (z ω j) (z ω k) (z ω l)

omit [Fintype n] in
private lemma integrable_coord_sq [IsProbabilityMeasure μ] {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ) (i : n) :
    Integrable (fun ω => z ω i ^ 2) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (h4 i))
    ((hmeas i).aestronglyMeasurable.pow 2) ?_
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using abs_sq_le_one_add_pow_four (z ω i)

/-- A monomial `z_i z_j z_k z_l` as a product `∏ₘ z_m ^ c_m` of coordinate powers. -/
private lemma mul_mul_mul_eq_prod_pow [DecidableEq n] (x : n → ℝ) (i j k l : n) :
    x i * x j * x k * x l =
      ∏ m, x m ^ ((if m = i then 1 else 0) + (if m = j then 1 else 0) +
        (if m = k then 1 else 0) + (if m = l then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true]

/-- Fourth mixed moments of a vector with independent, centred coordinates of unit variance and
common fourth moment `m₄`:
`𝔼[z_i z_j z_k z_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk + (m₄ − 3) δ_ijkl`.
Atlas: `hutchinson-variance` (helper). -/
theorem integral_coord_mul_coord_mul_coord_mul_coord [IsProbabilityMeasure μ] [DecidableEq n]
    {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    {m₄ : ℝ} (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = m₄) (i j k l : n) :
    ∫ ω, z ω i * z ω j * z ω k * z ω l ∂μ =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0) +
      (if i = l then 1 else 0) * (if j = k then 1 else 0) +
      (m₄ - 3) * ((if i = j then 1 else 0) * (if i = k then 1 else 0) *
        (if i = l then 1 else 0)) := by
  have hprod : ∀ c : n → ℕ, ∫ ω, ∏ m, z ω m ^ c m ∂μ = ∏ m, ∫ ω, z ω m ^ c m ∂μ := fun c =>
    hindep.integral_fun_prod_comp hmeas fun m => (continuous_pow (c m)).aestronglyMeasurable
  simp_rw [mul_mul_mul_eq_prod_pow (z _) i j k l]
  rw [hprod]
  -- an index occurring exactly once kills the product
  have hzero : ∀ a, (∫ ω, z ω a ^ ((if a = i then 1 else 0) + (if a = j then 1 else 0) +
      (if a = k then 1 else 0) + (if a = l then 1 else 0)) ∂μ) = 0 →
      (∏ m, ∫ ω, z ω m ^ ((if m = i then 1 else 0) + (if m = j then 1 else 0) +
        (if m = k then 1 else 0) + (if m = l then 1 else 0)) ∂μ) = 0 := fun a ha =>
    Finset.prod_eq_zero (Finset.mem_univ a) ha
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        rw [Finset.prod_eq_single i (fun m _ hm => by simp [hm]) (by simp)]
        norm_num [hm4]
      · rw [Finset.prod_eq_mul i k hik (fun m _ hm => by simp [hm.1, hm.2])
          (by simp) (by simp)]
        simp [hik, Ne.symm hik, hsq]
    · by_cases hik : i = k
      · subst hik
        rw [hzero l (by simp [Ne.symm hkl, hmean])]
        simp [hkl]
      · rw [hzero k (by simp [hkl, Ne.symm hik, hmean])]
        simp [hkl, hik]
  · by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · subst hjl
        rw [Finset.prod_eq_mul i j hij (fun m _ hm => by simp [hm.1, hm.2])
          (by simp) (by simp)]
        simp [hij, Ne.symm hij, hsq]
      · rw [hzero j (by simp [Ne.symm hij, hjl, hmean])]
        simp [hij, Ne.symm hij, hjl]
    · by_cases hil : i = l
      · subst hil
        by_cases hjk : j = k
        · subst hjk
          rw [Finset.prod_eq_mul i j hij (fun m _ hm => by simp [hm.1, hm.2])
            (by simp) (by simp)]
          simp [hij, Ne.symm hij, hsq]
        · rw [hzero j (by simp [Ne.symm hij, hjk, hmean])]
          simp [hij, Ne.symm hij, hjk, hik]
      · rw [hzero i (by simp [hij, hik, hil, hmean])]
        simp [hij, hik, hil]

end Probability

/-- The index sum behind the Hutchinson variance:
`∑ᵢⱼₖₗ A_ij A_kl (δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk + (m₄ − 3) δ_ijkl)
  = (tr A)² + ∑ᵢⱼ A_ij² + ∑ᵢⱼ A_ij A_ji + (m₄ − 3) ∑ᵢ A_ii²`.
Atlas: `hutchinson-variance` (helper). -/
theorem sum_fourth_moment_contraction [DecidableEq n] (A : Matrix n n ℝ) (m₄ : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l *
      ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0) +
        (m₄ - 3) * ((if i = j then 1 else 0) * (if i = k then 1 else 0) *
          (if i = l then 1 else 0))) =
      A.trace ^ 2 + ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i +
        (m₄ - 3) * ∑ i, A i i ^ 2 := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  congr 1
  congr 1
  · simp [Matrix.trace, sq, Finset.sum_mul_sum]
  · simp [sq]
  · simp
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Second moment of Hutchinson's estimator: for a random vector with independent, centred
coordinates of unit variance and common fourth moment `m₄`,
`𝔼[(zᵀ A z)²] = (tr A)² + ∑ᵢⱼ A_ij² + ∑ᵢⱼ A_ij A_ji + (m₄ − 3) ∑ᵢ A_ii²`.
Source: Avron–Toledo (2011) [`at11`], proofs of Lem 5, 6; Hutchinson (1989) [`hutch89`].
Atlas: `hutchinson-variance`. -/
theorem integral_quadForm_sq [DecidableEq n] (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ) {m₄ : ℝ}
    (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = m₄) :
    ∫ ω, quadForm A (z ω) ^ 2 ∂μ =
      A.trace ^ 2 + ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i +
        (m₄ - 3) * ∑ i, A i i ^ 2 := by
  have hP := integrable_coord_mul_coord_mul_coord_mul_coord hmeas h4
  simp_rw [quadForm_sq_eq_sum]
  rw [← sum_fourth_moment_contraction A m₄]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hP i j k l).const_mul (A i j * A k l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => (hP i j k l).const_mul (A i j * A k l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (hP i j k l).const_mul (A i j * A k l)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hP i j k l).const_mul (A i j * A k l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_coord_mul_coord_mul_coord_mul_coord hmeas hindep hmean hsq hm4]

/-- **Variance of Hutchinson's estimator** (general form). If the coordinates of `z` are
independent, centred, of unit variance and common fourth moment `m₄ = 𝔼[z_i⁴]`, then
`Var[zᵀ A z] = ∑ᵢⱼ A_ij² + ∑ᵢⱼ A_ij A_ji + (m₄ − 3) ∑ᵢ A_ii²` (mathematically the same as
`∑_{i≠j} (A_ij² + A_ij A_ji) + (m₄ − 1) ∑ᵢ A_ii²`; that form is not stated separately).
Source: Hutchinson (1989) [`hutch89`] (Rademacher case); Avron–Toledo (2011) [`at11`],
Lem 5 (Gaussian), Lem 6 (Rademacher). Atlas: `hutchinson-variance`.
Deviation: no symmetry of `A` assumed; general fourth moment `m₄` (`m₄ = 1` Rademacher,
`m₄ = 3` Gaussian). -/
theorem variance_quadForm [DecidableEq n] (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ) {m₄ : ℝ}
    (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = m₄) :
    Var[fun ω => quadForm A (z ω); μ] =
      ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i + (m₄ - 3) * ∑ i, A i i ^ 2 := by
  have hL2 : ∀ i, MemLp (fun ω => z ω i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).2
      (integrable_coord_sq hmeas h4 i)
  have hQ : Integrable (fun ω => quadForm A (z ω)) μ := by
    simp_rw [quadForm_eq_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_coord_mul_coord hL2 i j).const_mul (A i j)
  have hQ2 : Integrable (fun ω => quadForm A (z ω) ^ 2) μ := by
    have hP := integrable_coord_mul_coord_mul_coord_mul_coord hmeas h4
    simp_rw [quadForm_sq_eq_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
        (hP i j k l).const_mul (A i j * A k l)
  have hind2 : ∀ i j, i ≠ j → IndepFun (fun ω => z ω i) (fun ω => z ω j) μ :=
    fun i j h => hindep.indepFun h
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq hQ.aestronglyMeasurable).2 hQ2)]
  simp only [Pi.pow_apply]
  rw [integral_quadForm_sq A hmeas hindep hmean hsq h4 hm4,
    integral_quadForm_eq_trace A hL2 hind2 hmean hsq]
  ring

/-- **Variance of Hutchinson's estimator, symmetric `A`.**
`Var[zᵀ A z] = 2‖A‖_F² + (m₄ − 3) ∑ᵢ A_ii² = 2(‖A‖_F² − ∑ᵢ A_ii²) + (m₄ − 1) ∑ᵢ A_ii²`.
Source: Avron–Toledo (2011) [`at11`], Lem 5, 6; Hutchinson (1989) [`hutch89`].
Atlas: `hutchinson-variance`. -/
theorem variance_quadForm_of_isSymm [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsSymm)
    {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ) {m₄ : ℝ}
    (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = m₄) :
    Var[fun ω => quadForm A (z ω); μ] =
      2 * (frobSq A - ∑ i, A i i ^ 2) + (m₄ - 1) * ∑ i, A i i ^ 2 := by
  rw [variance_quadForm A hmeas hindep hmean hsq h4 hm4]
  have h1 : ∑ i, ∑ j, A i j * A j i = ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hA.apply, sq]
  have h2 : frobSq A = ∑ i, ∑ j, A i j ^ 2 := by
    simp only [frobSq, frobInner, sq]
  rw [h1, h2]
  ring

/-- Hutchinson variance for symmetric `A` and Gaussian-like coordinates (`m₄ = 3`):
`Var[zᵀ A z] = 2‖A‖_F²`. Source: Avron–Toledo (2011) [`at11`], Lem 5.
Deviation: only `m₄ = 3` is assumed of the coordinates, not Gaussianity.
Atlas: `hutchinson-variance`. -/
theorem variance_quadForm_of_isSymm_of_fourth_moment_eq_three [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsSymm) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ)
    (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = 3) :
    Var[fun ω => quadForm A (z ω); μ] = 2 * frobSq A := by
  rw [variance_quadForm_of_isSymm hA hmeas hindep hmean hsq h4 hm4]
  ring

/-- Hutchinson variance for symmetric `A` and Rademacher-like coordinates (`m₄ = 1`):
`Var[zᵀ A z] = 2(‖A‖_F² − ∑ᵢ A_ii²)`. Source: Hutchinson (1989) [`hutch89`];
Avron–Toledo (2011) [`at11`], Lem 6.
Deviation: only `m₄ = 1` is assumed of the coordinates, not the Rademacher law.
Atlas: `hutchinson-variance`. -/
theorem variance_quadForm_of_isSymm_of_fourth_moment_eq_one [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsSymm) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ)
    (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = 1) :
    Var[fun ω => quadForm A (z ω); μ] = 2 * (frobSq A - ∑ i, A i i ^ 2) := by
  rw [variance_quadForm_of_isSymm hA hmeas hindep hmean hsq h4 hm4]
  ring

end Variance

end NLAlib
