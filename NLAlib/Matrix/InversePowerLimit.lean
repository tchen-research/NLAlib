import NLAlib.Matrix.InversePowerConcavity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Field.GeomSum

/-!
# Limits of inverse-power spectral probes

Normalized finite power sums concentrate at the unique largest inverse
eigenvalue. The exponentially small remainder also vanishes after
multiplication by the moment order, which controls the cancelling Hessian
terms in the Gram soft minimum.

Source: operator hard-edge derivation; atlas `wishart-lambda-min-tail`.
-/

noncomputable section

open Filter
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- A weighted finite power sum with a unique unit ratio converges to the
weight of that ratio. Source: normalized inverse-eigenvalue powers in the
operator hard-edge proof; atlas `wishart-lambda-min-tail` (limit helper). -/
theorem tendsto_sum_mul_pow_of_unique_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1) :
    Tendsto (fun n : ℕ => ∑ i, w i * ρ i ^ n) atTop (𝓝 (w i₀)) := by
  have hi (i : ι) : Tendsto (fun n : ℕ => w i * ρ i ^ n) atTop
      (𝓝 (if i = i₀ then w i₀ else 0)) := by
    by_cases h : i = i₀
    · subst i
      simpa only [hρ₀, one_pow, mul_one, if_pos rfl, if_true] using tendsto_const_nhds
    · simpa only [if_neg h, mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (hρ i h).1 (hρ i h).2).const_mul (w i)
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using tendsto_finsetSum Finset.univ (fun i _ => hi i)

/-- The remainder of a unique-top weighted power sum decays faster than the
reciprocal moment order. Source: exponential decay of normalized inverse
eigenvalues; atlas `wishart-lambda-min-tail` (Hessian limit helper). -/
theorem tendsto_natCast_mul_sub_sum_mul_pow_of_unique_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((∑ i, w i * ρ i ^ n) - w i₀)) atTop (𝓝 0) := by
  have hi (i : ι) : Tendsto (fun n : ℕ =>
      (n : ℝ) * (w i * ρ i ^ n - if i = i₀ then w i₀ else 0)) atTop (𝓝 0) := by
    by_cases h : i = i₀
    · subst i
      simpa only [hρ₀, one_pow, mul_one, if_pos rfl, if_true, sub_self, mul_zero] using
        (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have ht := (tendsto_self_mul_const_pow_of_lt_one (hρ i h).1 (hρ i h).2).const_mul (w i)
      convert ht using 1
      · funext n
        simp only [if_neg h, sub_zero]
        ring
      · simp
  have ht := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, mul_ite, mul_zero] using ht

/-- Every bounded real inverse power of a unique-top normalized power sum
converges to one, including the inverse-root factor. Source: continuity
at the limiting base one; atlas `wishart-lambda-min-tail` (limit helper). -/
theorem tendsto_sum_pow_rpow_neg_inv_sub_of_unique_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1) (a : ℝ) :
    Tendsto (fun n : ℕ => (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - a)) atTop (𝓝 1) := by
  have hsum : Tendsto (fun n : ℕ => ∑ i, ρ i ^ n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul] using tendsto_sum_mul_pow_of_unique_one ρ (fun _ => 1) i₀ hρ₀ hρ
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [neg_zero, zero_sub, Real.one_rpow] using
    hsum.rpow (hinv.neg.sub_const a) (Or.inl one_ne_zero)

/-- Normalized inverse-power weights converge to the unique top projector
coordinate. Source: inverse-power soft minimum gradient; atlas
`wishart-lambda-min-tail` (limit helper). -/
theorem tendsto_sum_pow_rpow_mul_pow_succ_of_unique_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1) (i : ι) :
    Tendsto (fun n : ℕ => (∑ j, ρ j ^ n) ^ (-(n : ℝ)⁻¹ - 1) * ρ i ^ (n + 1))
      atTop (𝓝 (if i = i₀ then 1 else 0)) := by
  have hfactor := tendsto_sum_pow_rpow_neg_inv_sub_of_unique_one ρ i₀ hρ₀ hρ 1
  by_cases hi : i = i₀
  · subst i
    simpa only [hρ₀, one_pow, mul_one, if_pos rfl, if_true] using hfactor
  · have hpow : Tendsto (fun n : ℕ => ρ i ^ (n + 1)) atTop (𝓝 0) := by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (hρ i hi).1 (hρ i hi).2).mul_const (ρ i)
    simpa only [if_neg hi, mul_zero] using hfactor.mul hpow

private lemma sum_pow_eq_mul_sum_div_pow {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (i₀ : ι) (h₀ : b i₀ ≠ 0) (n : ℕ) :
    (∑ i, b i ^ n) = b i₀ ^ n * ∑ i, (b i / b i₀) ^ n := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ h₀)]

/-- The inverse-root of a positive finite power sum tends to the reciprocal
of its unique maximal base. Source: inverse-power soft minimum; atlas
`wishart-lambda-min-tail` (value limit helper). -/
theorem tendsto_sum_pow_rpow_neg_inv_of_unique_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (i₀ : ι) (hb₀ : 0 < b i₀) (hb : ∀ i, 0 ≤ b i)
    (hmax : ∀ i, i ≠ i₀ → b i < b i₀) :
    Tendsto (fun n : ℕ => (∑ i, b i ^ n) ^ (-(n : ℝ)⁻¹)) atTop (𝓝 (b i₀)⁻¹) := by
  let ρ : ι → ℝ := fun i => b i / b i₀
  have hρ₀ : ρ i₀ = 1 := div_self hb₀.ne'
  have hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1 := fun i hi =>
    ⟨div_nonneg (hb i) hb₀.le, (div_lt_one hb₀).2 (hmax i hi)⟩
  have hSpos (n : ℕ) : 0 < ∑ i, ρ i ^ n := by
    have hsingle : ρ i₀ ^ n ≤ ∑ i, ρ i ^ n :=
      Finset.single_le_sum (fun i _ => pow_nonneg (div_nonneg (hb i) hb₀.le) n) (Finset.mem_univ _)
    rw [hρ₀, one_pow] at hsingle
    linarith
  have hfactor := tendsto_sum_pow_rpow_neg_inv_sub_of_unique_one ρ i₀ hρ₀ hρ 0
  have ht : Tendsto (fun n : ℕ => (b i₀)⁻¹ * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹))
      atTop (𝓝 (b i₀)⁻¹) := by simpa only [sub_zero, mul_one] using hfactor.const_mul (b i₀)⁻¹
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  rw [sum_pow_eq_mul_sum_div_pow b i₀ hb₀.ne' n,
    Real.mul_rpow (pow_nonneg hb₀.le _) (hSpos n).le,
    ← Real.rpow_natCast, ← Real.rpow_mul hb₀.le]
  have he : (n : ℝ) * (-(n : ℝ)⁻¹) = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hnR]
  rw [he, Real.rpow_neg_one]

private lemma sum_pow_rpow_mul_pow_succ_eq_normalized {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (i₀ : ι) (hb₀ : 0 < b i₀) (hb : ∀ i, 0 ≤ b i)
    (n : ℕ) (hn : 0 < n) (i : ι) :
    (∑ j, b j ^ n) ^ (-(n : ℝ)⁻¹ - 1) * b i ^ (n + 1)
      = (∑ j, (b j / b i₀) ^ n) ^ (-(n : ℝ)⁻¹ - 1) * (b i / b i₀) ^ (n + 1) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hSn : 0 ≤ ∑ j, (b j / b i₀) ^ n :=
    Finset.sum_nonneg fun j _ => pow_nonneg (div_nonneg (hb j) hb₀.le) n
  rw [sum_pow_eq_mul_sum_div_pow b i₀ hb₀.ne' n,
    Real.mul_rpow (pow_nonneg hb₀.le _) hSn,
    ← Real.rpow_natCast, ← Real.rpow_mul hb₀.le]
  have hbi : b i = b i₀ * (b i / b i₀) := by field_simp
  nth_rw 1 [hbi]
  rw [mul_pow]
  rw [show b i₀ ^ ((n : ℝ) * (-(n : ℝ)⁻¹ - 1)) *
      (∑ j, (b j / b i₀) ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
      (b i₀ ^ (n + 1) * (b i / b i₀) ^ (n + 1)) =
      (b i₀ ^ ((n : ℝ) * (-(n : ℝ)⁻¹ - 1)) * b i₀ ^ (n + 1)) *
      (∑ j, (b j / b i₀) ^ n) ^ (-(n : ℝ)⁻¹ - 1) * (b i / b i₀) ^ (n + 1) by ring]
  rw [← Real.rpow_natCast, ← Real.rpow_add hb₀]
  have he : (n : ℝ) * (-(n : ℝ)⁻¹ - 1) + (n + 1 : ℕ) = 0 := by
    push_cast
    field_simp
    ring
  rw [he, Real.rpow_zero, one_mul]

/-- Each inverse-power spectral gradient weight converges to the unique
maximal inverse-eigenvalue coordinate. Source: operator soft minimum;
atlas `wishart-lambda-min-tail` (projector limit helper). -/
theorem tendsto_sum_pow_rpow_mul_pow_succ_of_unique_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (i₀ : ι) (hb₀ : 0 < b i₀) (hb : ∀ i, 0 ≤ b i)
    (hmax : ∀ i, i ≠ i₀ → b i < b i₀) (i : ι) :
    Tendsto (fun n : ℕ => (∑ j, b j ^ n) ^ (-(n : ℝ)⁻¹ - 1) * b i ^ (n + 1))
      atTop (𝓝 (if i = i₀ then 1 else 0)) := by
  have hρ₀ : b i₀ / b i₀ = 1 := div_self hb₀.ne'
  have hρ : ∀ i, i ≠ i₀ → 0 ≤ b i / b i₀ ∧ b i / b i₀ < 1 := fun i hi =>
    ⟨div_nonneg (hb i) hb₀.le, (div_lt_one hb₀).2 (hmax i hi)⟩
  have ht := tendsto_sum_pow_rpow_mul_pow_succ_of_unique_one
    (fun i => b i / b i₀) i₀ hρ₀ hρ i
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (sum_pow_rpow_mul_pow_succ_eq_normalized b i₀ hb₀ hb n hn i).symm

/-- Natural trace powers of a Hermitian real matrix are the power sums of
its eigenvalues. Source: finite spectral theorem and unitary trace
invariance; atlas `wishart-lambda-min-tail` (limit helper). -/
theorem trace_pow_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.IsHermitian) (n : ℕ) :
    Matrix.trace (R ^ n) = ∑ i, hR.eigenvalues i ^ n := by
  conv_lhs => rw [hR.spectral_theorem, ← map_pow]
  rw [trace_conjStarAlgAut,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

/-- A positive definite inverse-power soft minimum converges to the
reciprocal largest inverse eigenvalue, hence the smallest eigenvalue.
Source: operator soft minimum limit; atlas `wishart-lambda-min-tail`.
The unique-max hypothesis is supplied by almost-sure simple spectrum. -/
theorem tendsto_inversePowerSoftMin_of_unique_max
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (i₀ : ι)
    (hmax : ∀ i, i ≠ i₀ → hA.inv.isHermitian.eigenvalues i < hA.inv.isHermitian.eigenvalues i₀) :
    Tendsto (fun n : ℕ => inversePowerSoftMin n A) atTop
      (𝓝 (hA.inv.isHermitian.eigenvalues i₀)⁻¹) := by
  unfold inversePowerSoftMin
  simp_rw [trace_pow_eq_sum_eigenvalues hA.inv.isHermitian]
  exact tendsto_sum_pow_rpow_neg_inv_of_unique_max hA.inv.isHermitian.eigenvalues i₀
    (hA.inv.eigenvalues_pos i₀) (fun i => (hA.inv.eigenvalues_pos i).le) hmax

/-- Every entry of the inverse-power gradient weight converges to the
rank-one projector on the unique maximal inverse eigenvector.
Source: operator soft minimum gradient limit; atlas `wishart-lambda-min-tail`.
The eigenvector is fixed for a deterministic matrix. -/
theorem tendsto_inversePowerSoftMinWeight_of_unique_max
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (i₀ : ι)
    (hmax : ∀ i, i ≠ i₀ → hA.inv.isHermitian.eigenvalues i < hA.inv.isHermitian.eigenvalues i₀)
    (a b : ι) :
    Tendsto (fun n : ℕ => inversePowerSoftMinWeight n A a b) atTop
      (𝓝 ((Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.inv.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (fun i => if i = i₀ then (1 : ℝ) else 0))) a b)) := by
  let ev := hA.inv.isHermitian.eigenvalues
  let U := hA.inv.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hPn (n : ℕ) : inversePowerSoftMinWeight n A = φ (Matrix.diagonal
      (fun i => (∑ j, ev j ^ n) ^ (-(n : ℝ)⁻¹ - 1) * ev i ^ (n + 1))) := by
    have hpow : A⁻¹ ^ (n + 1) = φ ((Matrix.diagonal ev) ^ (n + 1)) := by
      calc A⁻¹ ^ (n + 1) = (φ (Matrix.diagonal ev)) ^ (n + 1) :=
        congrArg (fun M : Matrix ι ι ℝ => M ^ (n + 1)) hA.inv.isHermitian.spectral_theorem
        _ = _ := (map_pow φ _ _).symm
    unfold inversePowerSoftMinWeight
    rw [trace_pow_eq_sum_eigenvalues hA.inv.isHermitian]
    rw [hpow, ← map_smul, Matrix.diagonal_pow, ← Matrix.diagonal_smul]
    rfl
  have hi (i : ι) : Tendsto (fun n : ℕ =>
      (∑ j, ev j ^ n) ^ (-(n : ℝ)⁻¹ - 1) * ev i ^ (n + 1))
      atTop (𝓝 (if i = i₀ then 1 else 0)) :=
    tendsto_sum_pow_rpow_mul_pow_succ_of_unique_max ev i₀
      (hA.inv.eigenvalues_pos i₀) (fun i => (hA.inv.eigenvalues_pos i).le) hmax i
  have hentry (d : ι → ℝ) : φ (Matrix.diagonal d) a b = ∑ i, U a i * d i * U b i := by
    simp only [φ, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rfl
  change Tendsto (fun n : ℕ => inversePowerSoftMinWeight n A a b) atTop
    (𝓝 (φ (Matrix.diagonal (fun i => if i = i₀ then (1 : ℝ) else 0)) a b))
  simp_rw [hPn, hentry]
  apply tendsto_finsetSum
  intro i _
  simpa only [Pi.pow_apply, star_trivial] using
    ((tendsto_const_nhds (x := U a i)).mul (hi i)).mul_const (U b i)

/-- A finite mixed geometric power sum has its exact divided-difference
formula. Source: inverse-power Hessian kernel; atlas
`wishart-lambda-min-tail` (off-diagonal limit helper). -/
theorem sum_range_pow_mul_pow_eq_div (x y : ℝ) (hxy : x ≠ y) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), x ^ (n - a + 1) * y ^ (a + 1))
      = x * y * ((y ^ (n + 1) - x ^ (n + 1)) / (y - x)) := by
  rw [← geom₂_sum (Ne.symm hxy) (n + 1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  rw [show n + 1 - 1 - a = n - a by omega, pow_succ, pow_succ]
  ring

/-- Off-diagonal mixed inverse-power sums converge to the exact spectral
gap coefficients. Source: geometric Hessian kernel; atlas
`wishart-lambda-min-tail` (off-diagonal limit helper). -/
theorem tendsto_sum_range_pow_mul_pow_of_unique_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1)
    (i j : ι) (hij : ρ i ≠ ρ j) :
    Tendsto (fun n : ℕ => ∑ a ∈ Finset.range (n + 1),
      ρ i ^ (n - a + 1) * ρ j ^ (a + 1)) atTop
      (𝓝 (ρ i * ρ j * (((if j = i₀ then 1 else 0) -
        (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))) := by
  have hp (a : ι) : Tendsto (fun n : ℕ => ρ a ^ (n + 1)) atTop
      (𝓝 (if a = i₀ then 1 else 0)) := by
    by_cases ha : a = i₀
    · subst a
      simpa only [hρ₀, one_pow, if_pos rfl, if_true] using tendsto_const_nhds
    · simpa only [pow_succ, if_neg ha, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (hρ a ha).1 (hρ a ha).2).mul_const (ρ a)
  simp_rw [sum_range_pow_mul_pow_eq_div _ _ hij]
  exact ((hp j).sub (hp i)).div_const (ρ j - ρ i) |>.const_mul (ρ i * ρ j)

/-- The diagonal cancellation in the inverse-power Hessian vanishes after
multiplication by the moment order. Source: exponentially small normalized
power remainders; atlas `wishart-lambda-min-tail` (Hessian limit helper). -/
theorem tendsto_natCast_add_one_mul_power_sum_difference_of_unique_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      ((∑ i, w i * ρ i ^ (2 * n + 2)) / (∑ i, ρ i ^ n) -
        ∑ i, w i * ρ i ^ (n + 2))) atTop (𝓝 0) := by
  let S : ℕ → ℝ := fun n => ∑ i, ρ i ^ n
  let U : ℕ → ℝ := fun n => ∑ i, w i * ρ i ^ (2 * n + 2)
  let V : ℕ → ℝ := fun n => ∑ i, w i * ρ i ^ (n + 2)
  let w' : ι → ℝ := fun i => w i * ρ i ^ 2
  have hw' : w' i₀ = w i₀ := by simp [w', hρ₀]
  have hρsq : ∀ i, i ≠ i₀ → 0 ≤ ρ i ^ 2 ∧ ρ i ^ 2 < 1 := by
    intro i hi
    constructor
    · positivity
    · nlinarith [(hρ i hi).1, (hρ i hi).2]
  have hρ₀sq : ρ i₀ ^ 2 = 1 := by simp [hρ₀]
  have hUeq : U = fun n => ∑ i, w' i * (ρ i ^ 2) ^ n := by
    funext n
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [w']
    rw [← pow_mul, pow_add]
    ring
  have hVeq : V = fun n => ∑ i, w' i * ρ i ^ n := by
    funext n
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [w']
    rw [pow_add]
    ring
  have hS : Tendsto S atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul] using tendsto_sum_mul_pow_of_unique_one ρ (fun _ => 1) i₀ hρ₀ hρ
  have hSr : Tendsto (fun n : ℕ => (n : ℝ) * (S n - 1)) atTop (𝓝 0) := by
    simpa only [one_mul] using tendsto_natCast_mul_sub_sum_mul_pow_of_unique_one
      ρ (fun _ => 1) i₀ hρ₀ hρ
  have hU : Tendsto U atTop (𝓝 (w i₀)) := by
    rw [hUeq, ← hw']
    exact tendsto_sum_mul_pow_of_unique_one (fun i => ρ i ^ 2) w' i₀ hρ₀sq hρsq
  have hV : Tendsto V atTop (𝓝 (w i₀)) := by
    rw [hVeq, ← hw']
    exact tendsto_sum_mul_pow_of_unique_one ρ w' i₀ hρ₀ hρ
  have hUr : Tendsto (fun n : ℕ => (n : ℝ) * (U n - w i₀)) atTop (𝓝 0) := by
    simp_rw [hUeq, ← hw']
    exact tendsto_natCast_mul_sub_sum_mul_pow_of_unique_one (fun i => ρ i ^ 2) w' i₀ hρ₀sq hρsq
  have hVr : Tendsto (fun n : ℕ => (n : ℝ) * (V n - w i₀)) atTop (𝓝 0) := by
    simp_rw [hVeq, ← hw']
    exact tendsto_natCast_mul_sub_sum_mul_pow_of_unique_one ρ w' i₀ hρ₀ hρ
  have hSn (n : ℕ) : S n ≠ 0 := by
    have hnn (i : ι) : 0 ≤ ρ i := by
      by_cases hi : i = i₀
      · simpa only [hi, hρ₀] using (zero_le_one : (0 : ℝ) ≤ 1)
      · exact (hρ i hi).1
    have hsingle : 1 ≤ S n := by
      have h := Finset.single_le_sum (fun i _ => pow_nonneg (hnn i) n) (Finset.mem_univ i₀)
      simpa only [S, hρ₀, one_pow] using h
    linarith
  have hdiff : Tendsto (fun n => U n / S n - V n) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, div_one, sub_self] using (hU.div hS one_ne_zero).sub hV
  have hrate : Tendsto (fun n : ℕ => (n : ℝ) * (U n / S n - V n)) atTop (𝓝 0) := by
    have ht := ((hUr.sub hVr).sub (hV.mul hSr)).div hS one_ne_zero
    convert ht using 1
    · funext n
      dsimp
      field_simp [hSn n]
      ring
    · simp
  simpa only [add_mul, one_mul, add_zero] using hrate.add hdiff

/-- The normalized closed Gram Laplacian converges with the diagonal
Hessian cancellation and exact off-diagonal gap terms. Source: operator
hard-edge proof; atlas `wishart-lambda-min-tail` (Laplacian limit helper).
The coefficients `w` are the unregularized Gram eigenvalues. -/
theorem tendsto_normalized_inverse_power_laplacian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1)
    (hinj : Function.Injective ρ) (b₀ k : ℝ) :
    Tendsto (fun n : ℕ =>
      2 * k * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - 1) * (∑ i, ρ i ^ (n + 1)) +
      4 * ((n : ℝ) + 1) * b₀ * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        ((∑ i, w i * ρ i ^ (2 * n + 2)) / (∑ i, ρ i ^ n) -
          ∑ i, w i * ρ i ^ (n + 2)) -
      2 * b₀ * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ i, ∑ j, if i = j then 0 else w j *
          ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1))
      atTop (𝓝 (2 * k - 2 * b₀ *
        ∑ i, ∑ j, if i = j then 0 else w j * ρ i * ρ j *
          (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))) := by
  have hfactor := tendsto_sum_pow_rpow_neg_inv_sub_of_unique_one ρ i₀ hρ₀ hρ 1
  have hnext : Tendsto (fun n : ℕ => ∑ i, ρ i ^ (n + 1)) atTop (𝓝 (1 : ℝ)) := by
    have h := tendsto_sum_mul_pow_of_unique_one ρ ρ i₀ hρ₀ hρ
    simpa only [hρ₀, pow_succ, mul_comm] using h
  have hdiag := tendsto_natCast_add_one_mul_power_sum_difference_of_unique_one ρ w i₀ hρ₀ hρ
  have hoff (i j : ι) : Tendsto (fun n : ℕ => if i = j then 0 else w j *
      ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1)) atTop
      (𝓝 (if i = j then 0 else w j * ρ i * ρ j *
        (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))) := by
    by_cases hij : i = j
    · simp only [if_pos hij]
      exact tendsto_const_nhds
    · have ht := (tendsto_sum_range_pow_mul_pow_of_unique_one ρ i₀ hρ₀ hρ i j
        (fun h => hij (hinj h))).const_mul (w j)
      simpa only [if_neg hij, mul_assoc] using ht
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hoff i j
  have hfirst := (hfactor.const_mul (2 * k)).mul hnext
  have hsecond := (hdiag.mul hfactor).const_mul (4 * b₀)
  have hlast := (hfactor.const_mul (2 * b₀)).mul hsum
  convert (hfirst.add hsecond).sub hlast using 1
  · funext n
    ring
  · simp

/-- The limiting double off-diagonal kernel reduces to the pairs involving
the unique top coordinate. Source: operator soft minimum Hessian limit;
atlas `wishart-lambda-min-tail` (exact gap sum helper). -/
theorem sum_offDiagonal_inverse_power_limit_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ w : ι → ℝ) (i₀ : ι)
    (hρ₀ : ρ i₀ = 1) :
    (∑ i, ∑ j, if i = j then 0 else w j * ρ i * ρ j *
      (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
      = ∑ j, if j = i₀ then 0 else (w i₀ + w j) * ρ j / (1 - ρ j) := by
  have he (i j : ι) :
      (if i = j then 0 else w j * ρ i * ρ j *
        (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
        = (if i = i₀ then (if j = i₀ then 0 else w j * ρ j / (1 - ρ j)) else 0) +
          (if j = i₀ then (if i = i₀ then 0 else w i₀ * ρ i / (1 - ρ i)) else 0) := by
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · subst i
      subst j
      simp
    · subst i
      have hne : i₀ ≠ j := Ne.symm hj
      simp only [hρ₀, if_true, if_neg hj, if_neg hne, mul_one,
        zero_sub, add_zero]
      rw [show ρ j - 1 = -(1 - ρ j) by ring, neg_div_neg_eq]
      ring
    · subst j
      simp only [hρ₀, if_true, if_neg hi, mul_one, sub_zero, zero_add]
      ring
    · by_cases hij : i = j <;> simp [hi, hj, hij]
  have hsumA : (∑ i : ι, ∑ j : ι,
      if i = i₀ then (if j = i₀ then (0 : ℝ) else w j * ρ j / (1 - ρ j)) else 0)
      = ∑ j, if j = i₀ then 0 else w j * ρ j / (1 - ρ j) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsumB : (∑ i : ι, ∑ j : ι,
      if j = i₀ then (if i = i₀ then (0 : ℝ) else w i₀ * ρ i / (1 - ρ i)) else 0)
      = ∑ i, if i = i₀ then 0 else w i₀ * ρ i / (1 - ρ i) := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc (∑ i, ∑ j, if i = j then 0 else w j * ρ i * ρ j *
      (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
      = (∑ i : ι, ∑ j : ι,
          if i = i₀ then (if j = i₀ then (0 : ℝ) else w j * ρ j / (1 - ρ j)) else 0) +
        (∑ i : ι, ∑ j : ι,
          if j = i₀ then (if i = i₀ then (0 : ℝ) else w i₀ * ρ i / (1 - ρ i)) else 0) := by
          simp_rw [he, Finset.sum_add_distrib]
    _ = _ := by rw [hsumA, hsumB, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring

/-- The limiting Gram Laplacian is at most the hard-edge coefficient
`2(k-r+1)`. Source: operator soft minimum gap correction; atlas
`wishart-lambda-min-tail` (sharp limiting coefficient helper).
The algebraic ratio identity holds for `ρj=(λmin+ε)/(λj+ε)` and
`b₀=1/(λmin+ε)`, with `w` the Gram eigenvalues. -/
theorem normalized_inverse_power_laplacian_limit_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1)
    (b₀ k : ℝ) (hb₀ : 0 ≤ b₀) (hw₀ : 0 ≤ w i₀)
    (hrel : ∀ j, j ≠ i₀ → b₀ * ρ j * (w j - w i₀) = 1 - ρ j) :
    2 * k - 2 * b₀ *
      (∑ i, ∑ j, if i = j then 0 else w j * ρ i * ρ j *
        (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
      ≤ 2 * (k - Fintype.card ι + 1) := by
  rw [sum_offDiagonal_inverse_power_limit_eq ρ w i₀ hρ₀]
  have hcount : (∑ j : ι, if j = i₀ then (0 : ℝ) else 1) = Fintype.card ι - 1 := by
    have he (j : ι) : (if j = i₀ then (0 : ℝ) else 1) =
        1 - (if j = i₀ then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [he, Finset.sum_sub_distrib]
    simp
  have hsum : (Fintype.card ι : ℝ) - 1 ≤
      b₀ * ∑ j, if j = i₀ then 0 else (w i₀ + w j) * ρ j / (1 - ρ j) := by
    rw [← hcount, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = i₀
    · simp only [if_pos hj, mul_zero, le_refl]
    · simp only [if_neg hj]
      have hden : 0 < 1 - ρ j := by linarith [(hρ j hj).2]
      rw [← mul_div_assoc, one_le_div hden]
      have hpos : 0 ≤ b₀ * ρ j * w i₀ :=
        mul_nonneg (mul_nonneg hb₀ (hρ j hj).1) hw₀
      nlinarith [hrel j hj]
  nlinarith

end NLAlib
