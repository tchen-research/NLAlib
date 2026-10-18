import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite Bessel inequality for real integral coefficients

An orthonormal family of real functions satisfies Bessel's inequality for
every finite coefficient set. The proof integrates a finite residual square;
no completeness or infinite-series representation is required.
-/

noncomputable section

open MeasureTheory Finset

namespace MeasureTheory

/-- Coordinate orthogonality multiplies to orthogonality of finite tensor
products, including an empty coordinate family. -/
theorem integral_prod_mul_prod_eq_ite
    {ι κ X : Type*} [Fintype ι] [DecidableEq κ] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)]
    (φ : ι → κ → X → ℝ) (α β : ι → κ)
    (horth : ∀ i, (∫ x, φ i (α i) x * φ i (β i) x ∂μ i) =
      if α i = β i then 1 else 0) :
    (∫ x, (∏ i, φ i (α i) (x i)) * (∏ i, φ i (β i) (x i)) ∂Measure.pi μ) =
      if α = β then 1 else 0 := by
  classical
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i x => φ i (α i) x * φ i (β i) x)]
  simp_rw [horth]
  by_cases h : α = β
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

set_option backward.isDefEq.respectTransparency false in
/-- A finite orthonormal family bounds its real integral coefficients by the
square integral of the original function. Only the displayed integrability
conditions are needed; the underlying measure need not be finite. -/
theorem sum_sq_integral_mul_le_integral_sq_of_orthonormal
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] {μ : Measure Ω}
    (s : Finset ι) (φ : ι → Ω → ℝ) {v : Ω → ℝ}
    (hv2 : Integrable (fun x => v x ^ 2) μ)
    (hvφ : ∀ i ∈ s, Integrable (fun x => v x * φ i x) μ)
    (hφφ : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x => φ i x * φ j x) μ)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0) :
    (∑ i ∈ s, (∫ x, v x * φ i x ∂μ) ^ 2) ≤ ∫ x, v x ^ 2 ∂μ := by
  classical
  let c (i : ι) := ∫ x, v x * φ i x ∂μ
  let q (x : Ω) := ∑ i ∈ s, c i * φ i x
  have hqφ (j : ι) (hj : j ∈ s) :
      Integrable (fun x => q x * φ j x) μ := by
    simp only [q, sum_mul, mul_assoc]
    exact integrable_finsetSum s (fun i hi => (hφφ i hi j hj).const_mul (c i))
  have hqφeq (j : ι) (hj : j ∈ s) :
      (∫ x, q x * φ j x ∂μ) = c j := by
    simp only [q, sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun i hi => (hφφ i hi j hj).const_mul (c i))]
    simp_rw [integral_const_mul]
    rw [sum_congr rfl (fun i hi => congrArg (fun a => c i * a) (horth i hi j hj))]
    simp [hj, mul_ite]
  have heq (x : Ω) : q x ^ 2 = ∑ i ∈ s, c i * (q x * φ i x) := by
    calc
      q x ^ 2 = q x * (∑ i ∈ s, c i * φ i x) := by change q x ^ 2 = q x * q x; ring
      _ = ∑ i ∈ s, q x * (c i * φ i x) := mul_sum ..
      _ = _ := sum_congr rfl (fun i _ => by ring)
  have hq2 : Integrable (fun x => q x ^ 2) μ := by
    simp_rw [heq]
    exact integrable_finsetSum s (fun i hi => (hqφ i hi).const_mul (c i))
  have hq2eq : (∫ x, q x ^ 2 ∂μ) = ∑ i ∈ s, c i ^ 2 := by
    simp_rw [heq]
    rw [integral_finsetSum _ (fun i hi => (hqφ i hi).const_mul (c i))]
    simp_rw [integral_const_mul]
    exact sum_congr rfl (fun i hi => by rw [hqφeq i hi]; ring)
  have hvq : Integrable (fun x => v x * q x) μ := by
    simp only [q, mul_sum]
    exact integrable_finsetSum s (fun i hi => by
      simpa only [mul_left_comm] using (hvφ i hi).const_mul (c i))
  have hvqeq : (∫ x, v x * q x ∂μ) = ∑ i ∈ s, c i ^ 2 := by
    have h (x : Ω) : v x * q x = ∑ i ∈ s, c i * (v x * φ i x) := by
      simp only [q, mul_sum]
      exact sum_congr rfl (fun i _ => by ring)
    simp_rw [h]
    rw [integral_finsetSum _ (fun i hi => (hvφ i hi).const_mul (c i))]
    simp_rw [integral_const_mul]
    exact sum_congr rfl (fun i _ => by dsimp [c]; ring)
  have hn : 0 ≤ ∫ x, (v x - q x) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (v x - q x))
  have he (x : Ω) : (v x - q x) ^ 2 = v x ^ 2 - 2 * (v x * q x) + q x ^ 2 := by ring
  simp_rw [he] at hn
  have hsub : Integrable (fun x => v x ^ 2 - 2 * (v x * q x)) μ :=
    hv2.sub (hvq.const_mul 2)
  rw [integral_add hsub hq2,
    integral_sub hv2 (hvq.const_mul 2), integral_const_mul, hvqeq, hq2eq] at hn
  change (∑ i ∈ s, c i ^ 2) ≤ _
  linarith

end MeasureTheory
