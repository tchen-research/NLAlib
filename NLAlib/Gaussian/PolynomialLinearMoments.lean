import NLAlib.Gaussian.Basic
import NLAlib.Gaussian.Concentration.Stein
import NLAlib.Gaussian.ProductIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Polynomial products of Gaussian linear forms

Every product is genuinely integrable. Coordinate Stein proves the covariance
recursion for arbitrary products, including repeated factors.
Source: operator re-derivation `pg:polynomial-stein`, `pg:wick-recursion`.
Supports atlas `isserlis`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib

/-- A finite linear form has an explicit polynomial-growth bound.
Source: finite coordinate norm comparison; supports `isserlis`. -/
theorem abs_dotProduct_le_sum_abs_mul_one_add_norm {n : ℕ} (a x : Fin n → ℝ) :
    |a ⬝ᵥ x| ≤ (∑ i, |a i|) * (1 + ‖x‖) := by
  rw [dotProduct, Finset.sum_mul]
  calc _ ≤ ∑ i, |a i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      gcongr
      have hh := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at hh
      linarith

/-- A finite product of linear forms is explicitly bounded by a polynomial
in the ambient coordinate norm. Source: operator re-derivation `pg:polynomial-stein`. -/
theorem abs_prod_dotProduct_le_polynomial
    {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    |∏ j ∈ s, a j ⬝ᵥ x| ≤ (∏ j ∈ s, ∑ i, |a j i|) * (1 + ‖x‖) ^ s.card := by
  rw [Finset.abs_prod]
  calc
    _ ≤ (∏ j ∈ s, (∑ i, |a j i|) * (1 + ‖x‖)) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro j _
      exact abs_dotProduct_le_sum_abs_mul_one_add_norm (a j) x
    _ = _ := (Finset.prod_mul_pow_card).symm

/-- Every finite product of Gaussian linear forms has finite absolute first
moment. Source: operator re-derivation `pg:polynomial-stein`; supports `isserlis`. -/
theorem integrable_prod_dotProduct_pi_gaussianReal
    {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => ∏ j ∈ s, a j ⬝ᵥ x)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  apply integrable_pi_gaussianReal_of_polynomial_growth
    (Measurable.aemeasurable (by simp only [dotProduct]; fun_prop)) _ s.card
  exact abs_prod_dotProduct_le_polynomial s a

/-- Multiplying such a product by any one linear form remains integrable.
Source: operator re-derivation `pg:polynomial-stein`; supports `isserlis`. -/
theorem integrable_dotProduct_mul_prod_pi_gaussianReal
    {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → Fin n → ℝ) (b : Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => (b ⬝ᵥ x) * ∏ j ∈ s, a j ⬝ᵥ x)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  apply integrable_pi_gaussianReal_of_polynomial_growth
    (Measurable.aemeasurable (by simp only [dotProduct]; fun_prop))
    ((∑ i, |b i|) * ∏ j ∈ s, ∑ i, |a j i|) (s.card + 1)
  intro x
  rw [abs_mul, pow_succ]
  calc _ ≤ ((∑ i, |b i|) * (1 + ‖x‖)) *
      ((∏ j ∈ s, ∑ i, |a j i|) * (1 + ‖x‖) ^ s.card) :=
        mul_le_mul (abs_dotProduct_le_sum_abs_mul_one_add_norm b x)
          (abs_prod_dotProduct_le_polynomial s a x) (abs_nonneg _)
          (by positivity)
    _ = _ := by ring

/-- Updating one Gaussian coordinate differentiates a linear form by its
coefficient in that coordinate. Source: operator re-derivation `pg:polynomial-stein`. -/
theorem hasDerivAt_dotProduct_update {n : ℕ} (a x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun y => a ⬝ᵥ Function.update x i y) (a i) t := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ j, (a j) • ContinuousLinearMap.proj j
  have hh := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)
  have hf : (fun y => a ⬝ᵥ Function.update x i y) = L ∘ Function.update x i := by
    funext y
    simp [L, dotProduct]
  rw [hf]
  exact hh.congr_deriv (by simp [L, Pi.single_apply])

/-- Coordinate Stein for an arbitrary product of linear forms. All derivatives
and Gaussian products are proved integrable; repeated factors are counted by
their separate positions. Source: operator re-derivation `pg:polynomial-stein`. -/
theorem integral_coordinate_mul_prod_dotProduct_pi_gaussianReal
    {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    (a : ι → Fin n → ℝ) (i : Fin n) :
    ∫ x : Fin n → ℝ, x i * ∏ j ∈ s, a j ⬝ᵥ x
        ∂Measure.pi (fun _ => gaussianReal 0 1) =
      ∑ j ∈ s, a j i * ∫ x : Fin n → ℝ, ∏ k ∈ s.erase j, a k ⬝ᵥ x
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let f : (Fin n → ℝ) → ℝ := fun x => ∏ j ∈ s, a j ⬝ᵥ x
  let df : (Fin n → ℝ) → ℝ := fun x =>
    ∑ j ∈ s, a j i * ∏ k ∈ s.erase j, a k ⬝ᵥ x
  have hupdate : ∀ x t, HasDerivAt (fun y => f (Function.update x i y))
      (df (Function.update x i t)) t := by
    intro x t
    have hh := HasDerivAt.fun_finsetProd (u := s)
      (fun j (_ : j ∈ s) => hasDerivAt_dotProduct_update (a j) x i t)
    exact hh.congr_deriv (by
      dsimp only [df]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_eq_mul, mul_comm])
  have hfi := integrable_prod_dotProduct_pi_gaussianReal s a
  have hxfi : Integrable (fun x : Fin n → ℝ => x i * f x)
      (Measure.pi fun _ => gaussianReal 0 1) := by
    have hh := integrable_dotProduct_mul_prod_pi_gaussianReal s a (Pi.single i 1)
    simpa only [single_dotProduct, one_mul, f] using hh
  have hdfi : Integrable df (Measure.pi fun _ => gaussianReal 0 1) :=
    integrable_finsetSum s (fun j _ =>
      (integrable_prod_dotProduct_pi_gaussianReal (s.erase j) a).const_mul (a j i))
  have hh := integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update f df i
    hupdate hfi hxfi hdfi
  rw [hh]
  dsimp only [df]
  rw [integral_finsetSum s (fun j _ =>
    (integrable_prod_dotProduct_pi_gaussianReal (s.erase j) a).const_mul (a j i))]
  simp only [integral_const_mul]

/-- Covariance Stein recursion for products of arbitrary standard-Gaussian
linear forms. It includes repeated coefficient vectors and every finite
product length. Source: operator re-derivation `pg:wick-recursion`; supports `isserlis`. -/
theorem integral_dotProduct_mul_prod_pi_gaussianReal
    {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    (a : ι → Fin n → ℝ) (b : Fin n → ℝ) :
    ∫ x : Fin n → ℝ, (b ⬝ᵥ x) * ∏ j ∈ s, a j ⬝ᵥ x
        ∂Measure.pi (fun _ => gaussianReal 0 1) =
      ∑ j ∈ s, (b ⬝ᵥ a j) * ∫ x : Fin n → ℝ, ∏ k ∈ s.erase j, a k ⬝ᵥ x
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hcoord : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => x i * ∏ j ∈ s, a j ⬝ᵥ x)
      (Measure.pi fun _ => gaussianReal 0 1) := by
    intro i
    have hh := integrable_dotProduct_mul_prod_pi_gaussianReal s a (Pi.single i 1)
    simpa only [single_dotProduct, one_mul] using hh
  have hexpand : ∀ x : Fin n → ℝ, (b ⬝ᵥ x) * ∏ j ∈ s, a j ⬝ᵥ x =
      ∑ i, b i * (x i * ∏ j ∈ s, a j ⬝ᵥ x) := by
    intro x
    simp only [dotProduct, Finset.sum_mul, mul_assoc]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => (hcoord i).const_mul (b i))]
  simp_rw [integral_const_mul, integral_coordinate_mul_prod_dotProduct_pi_gaussianReal]
  simp only [Finset.mul_sum, dotProduct, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end NLAlib
