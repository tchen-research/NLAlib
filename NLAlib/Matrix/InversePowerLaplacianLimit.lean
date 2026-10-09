import NLAlib.Matrix.InversePowerLimit

/-!
# Symmetric gap form of the inverse-power Gram Laplacian limit

This interface matches the finite spectral Laplacian formula exactly.
Atlas: `wishart-lambda-min-tail` (operator hard-edge proof).
-/

noncomputable section

open Filter
open scoped Topology

namespace NLAlib

/-- The symmetric off-diagonal form of the normalized Gram Laplacian has
the exact inverse-eigenvalue gap limit. Source: resolvent operator
hard-edge proof; atlas `wishart-lambda-min-tail` (Laplacian limit helper). -/
theorem tendsto_normalized_inverse_power_laplacian_symmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1)
    (hinj : Function.Injective ρ) (b₀ k : ℝ) :
    Tendsto (fun n : ℕ =>
      2 * k * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - 1) * (∑ i, ρ i ^ (n + 1)) +
      4 * ((n : ℝ) + 1) * b₀ * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        ((∑ i, w i * ρ i ^ (2 * n + 2)) / (∑ i, ρ i ^ n) -
          ∑ i, w i * ρ i ^ (n + 2)) -
      b₀ * (∑ i, ρ i ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ i, ∑ j ∈ Finset.univ.erase i, (w i + w j) *
          ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1))
      atTop (𝓝 (2 * k - b₀ *
        ∑ i, ∑ j ∈ Finset.univ.erase i, (w i + w j) * ρ i * ρ j *
          (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))) := by
  have hfactor := tendsto_sum_pow_rpow_neg_inv_sub_of_unique_one ρ i₀ hρ₀ hρ 1
  have hnext : Tendsto (fun n : ℕ => ∑ i, ρ i ^ (n + 1)) atTop (𝓝 (1 : ℝ)) := by
    have h := tendsto_sum_mul_pow_of_unique_one ρ ρ i₀ hρ₀ hρ
    simpa only [hρ₀, pow_succ, mul_comm] using h
  have hdiag := tendsto_natCast_add_one_mul_power_sum_difference_of_unique_one ρ w i₀ hρ₀ hρ
  have hoff (i j : ι) (hij : j ∈ Finset.univ.erase i) :
      Tendsto (fun n : ℕ => (w i + w j) *
        ∑ a ∈ Finset.range (n + 1), ρ i ^ (n - a + 1) * ρ j ^ (a + 1)) atTop
        (𝓝 ((w i + w j) * ρ i * ρ j *
          (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))) := by
    have hne : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hij)
    have ht := (tendsto_sum_range_pow_mul_pow_of_unique_one ρ i₀ hρ₀ hρ i j
      (fun h => hne (hinj h))).const_mul (w i + w j)
    simpa only [mul_assoc] using ht
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum (Finset.univ.erase i) fun j hj => hoff i j hj
  have hfirst := (hfactor.const_mul (2 * k)).mul hnext
  have hsecond := (hdiag.mul hfactor).const_mul (4 * b₀)
  have hlast := (hfactor.const_mul b₀).mul hsum
  convert (hfirst.add hsecond).sub hlast using 1
  · funext n
    ring
  · simp

/-- Symmetry combines the ordered off-diagonal gap terms into twice one
directed sum. Source: scalar divided differences of the inverse-power
Hessian; atlas `wishart-lambda-min-tail` (limit constant helper). -/
theorem sum_erase_symmetric_inverse_power_limit_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ w : ι → ℝ) (i₀ : ι) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, (w i + w j) * ρ i * ρ j *
      (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
      = 2 * ∑ i, ∑ j, if i = j then 0 else w j * ρ i * ρ j *
        (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)) := by
  let K : ι → ι → ℝ := fun i j => ρ i * ρ j *
    (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i))
  have hdiag (i : ι) : K i i = 0 := by simp [K]
  have hsym (i j : ι) : K i j = K j i := by
    dsimp only [K]
    rw [show ρ i - ρ j = -(ρ j - ρ i) by ring,
      show (if i = i₀ then (1 : ℝ) else 0) - (if j = i₀ then 1 else 0) =
        -((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) by ring,
      neg_div_neg_eq]
    ring
  have herase (i : ι) : (∑ j ∈ Finset.univ.erase i, (w i + w j) * K i j)
      = ∑ j, (w i + w j) * K i j := by
    have hh := Finset.sum_erase_add Finset.univ (fun j => (w i + w j) * K i j) (Finset.mem_univ i)
    simpa only [hdiag, mul_zero, add_zero] using hh
  have hswap : (∑ i, ∑ j, w i * K i j) = ∑ i, ∑ j, w j * K i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym]
  have hif (i j : ι) : (if i = j then 0 else w j * ρ i * ρ j *
      (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
      = w j * K i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp only [if_neg hij, K]
      ring
  have hleft (i j : ι) : (w i + w j) * ρ i * ρ j *
      (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i))
      = (w i + w j) * K i j := by dsimp [K]; ring
  simp_rw [hleft, hif, herase, add_mul, Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- The symmetric limiting Gram Laplacian is bounded by the exact
hard-edge coefficient. Source: inverse spectral gap correction; atlas
`wishart-lambda-min-tail` (sharp limiting bound helper). -/
theorem normalized_inverse_power_laplacian_symmetric_limit_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ w : ι → ℝ) (i₀ : ι) (hρ₀ : ρ i₀ = 1)
    (hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1)
    (b₀ k : ℝ) (hb₀ : 0 ≤ b₀) (hw₀ : 0 ≤ w i₀)
    (hrel : ∀ j, j ≠ i₀ → b₀ * ρ j * (w j - w i₀) = 1 - ρ j) :
    2 * k - b₀ *
      (∑ i, ∑ j ∈ Finset.univ.erase i, (w i + w j) * ρ i * ρ j *
        (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i)))
      ≤ 2 * (k - Fintype.card ι + 1) := by
  rw [sum_erase_symmetric_inverse_power_limit_eq]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    normalized_inverse_power_laplacian_limit_le ρ w i₀ hρ₀ hρ b₀ k hb₀ hw₀ hrel

end NLAlib
