import NLAlib.Probability.Gaussian.Moments.PositiveMoments
import NLAlib.Probability.Gaussian.Basic.StandardVector
import NLAlib.Matrix.Norms.Core
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! # Natural Gaussian radial moments

Exact product forms and elementary upper and lower bounds for Gaussian
scalar and radial moments. Source: Gaussian integration, used in Heidary,
*The Sharp Logarithmic Cost of Khatri--Rao Subspace Embeddings*.
Atlas: `khatri-rao-sharp-growth`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset Matrix

namespace NLAlib

/-- The scalar standard Gaussian even moment, written as a product of odd integers.
Source: the Gaussian Gamma integral. Atlas: `khatri-rao-sharp-growth`. -/
def gaussianEvenMoment (p : ℕ) : ℝ := ∏ k ∈ range p, (2 * (k : ℝ) + 1)

/-- The natural moment of a squared standard Gaussian radius.
Source: the chi-square Gamma integral. Atlas: `khatri-rao-sharp-growth`. -/
def gaussianRadialMoment (r p : ℕ) : ℝ := ∏ k ∈ range p, ((r : ℝ) + 2 * k)

/-- Scalar Gaussian even moments are positive.
Source: their product form. Atlas: `khatri-rao-sharp-growth`. -/
theorem gaussianEvenMoment_pos (p : ℕ) : 0 < gaussianEvenMoment p := by
  unfold gaussianEvenMoment
  exact prod_pos fun k _ => by positivity

/-- The scalar Gaussian even moment has the Gamma closed form.
Source: the Gaussian Gamma recurrence. Atlas: `khatri-rao-sharp-growth`. -/
theorem gaussianEvenMoment_eq_gamma (p : ℕ) :
    gaussianEvenMoment p = 2 ^ p * Real.Gamma ((p : ℝ) + 1 / 2) / Real.sqrt Real.pi := by
  induction p with
  | zero =>
    simp only [gaussianEvenMoment, range_zero, prod_empty, Nat.cast_zero,
      zero_add, pow_zero, one_mul]
    rw [Real.Gamma_one_half_eq, div_self (Real.sqrt_pos.2 Real.pi_pos).ne']
  | succ p ih =>
    rw [gaussianEvenMoment, prod_range_succ]
    change gaussianEvenMoment p * (2 * (p : ℝ) + 1) = _
    rw [ih, pow_succ, Nat.cast_add, Nat.cast_one,
      show (p : ℝ) + 1 + 1 / 2 = ((p : ℝ) + 1 / 2) + 1 by ring,
      Real.Gamma_add_one (by positivity : (p : ℝ) + 1 / 2 ≠ 0)]
    ring

/-- The Gaussian radial moment has the Gamma closed form.
Source: the chi-square Gamma recurrence. Atlas: `khatri-rao-sharp-growth`. -/
theorem gaussianRadialMoment_eq_gamma {r : ℕ} (hr : 1 ≤ r) (p : ℕ) :
    gaussianRadialMoment r p =
      2 ^ p * Real.Gamma ((r : ℝ) / 2 + p) / Real.Gamma ((r : ℝ) / 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hG : Real.Gamma ((r : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  induction p with
  | zero => simp [gaussianRadialMoment, hG]
  | succ p ih =>
    rw [gaussianRadialMoment, prod_range_succ]
    change gaussianRadialMoment r p * ((r : ℝ) + 2 * p) = _
    rw [ih, pow_succ, Nat.cast_add, Nat.cast_one,
      show (r : ℝ) / 2 + ((p : ℝ) + 1) = ((r : ℝ) / 2 + p) + 1 by ring,
      Real.Gamma_add_one (by positivity : (r : ℝ) / 2 + p ≠ 0)]
    ring

/-- Scalar Gaussian even moments dominate the ordinary factorial.
Source: comparison of the product factors. Atlas: `khatri-rao-sharp-growth`. -/
theorem factorial_le_gaussianEvenMoment (p : ℕ) : (p.factorial : ℝ) ≤ gaussianEvenMoment p := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  exact prod_le_prod (fun _ _ => by positivity) fun k _ => by push_cast; linarith

/-- The squared Gaussian radius has its exact natural product moment.
Source: Gaussian polar integration. Atlas: `khatri-rao-sharp-growth`. -/
theorem integral_pow_sum_sq_gaussianVector {r : ℕ} (hr : 1 ≤ r) (p : ℕ) :
    (∫ z : Fin r → ℝ, (∑ i, z i ^ 2) ^ p ∂gaussianVector (Fin r)) =
      gaussianRadialMoment r p := by
  rw [gaussianRadialMoment_eq_gamma hr]
  simpa only [Real.rpow_natCast] using
    integral_rpow_sum_sq_gaussianVector r hr (p : ℝ) (by positivity)

/-- The scalar Gaussian has its exact even natural moment.
Source: the scalar Gaussian Gamma integral. Atlas: `khatri-rao-sharp-growth`. -/
theorem integral_pow_two_mul_gaussianReal (p : ℕ) :
    (∫ z : ℝ, z ^ (2 * p) ∂gaussianReal 0 1) = gaussianEvenMoment p := by
  rw [gaussianEvenMoment_eq_gamma]
  have h := integral_abs_rpow_gaussianReal (p : ℝ) (by positivity)
  simp only [show (2 : ℝ) * (p : ℝ) = ((2 * p : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast] at h
  simpa only [abs_pow, even_two_mul, Even.pow_abs] using h

/-- A radial Gaussian product moment is bounded by its largest possible factor.
Source: monotonicity of finite products. Atlas: `khatri-rao-sharp-growth`. -/
theorem gaussianRadialMoment_le_pow (r p : ℕ) :
    gaussianRadialMoment r p ≤ ((r : ℝ) + 2 * p) ^ p := by
  unfold gaussianRadialMoment
  calc
    (∏ k ∈ range p, ((r : ℝ) + 2 * k)) ≤
        ∏ _k ∈ range p, ((r : ℝ) + 2 * p) := by
      apply prod_le_prod (fun _ _ => by positivity)
      intro k hk
      have hkp : (k : ℝ) ≤ p := by exact_mod_cast (mem_range.mp hk).le
      linarith
    _ = _ := by simp

/-- Every linear form of a Gaussian vector has its exact even natural moment.
Source: Gaussian rotational invariance and the scalar moment formula.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_dotProduct_pow_two_mul_gaussianVector
    {α : Type*} [Fintype α] (w : α → ℝ) (p : ℕ) :
    Integrable (fun z => (w ⬝ᵥ z) ^ (2 * p)) (gaussianVector α) ∧
      (∫ z, (w ⬝ᵥ z) ^ (2 * p) ∂gaussianVector α) =
        gaussianEvenMoment p * (w ⬝ᵥ w) ^ p := by
  by_cases hw : w = 0
  · subst w
    by_cases hp : p = 0
    · subst p
      simp [gaussianEvenMoment]
    · simp [zero_pow (by omega : 2 * p ≠ 0), hp]
  let N : ℝ := ‖WithLp.toLp 2 w‖
  have hN0 : N ≠ 0 := by
    intro h
    apply hw
    apply WithLp.toLp_injective (p := 2)
    simpa only [WithLp.toLp_zero] using (norm_eq_zero.mp h)
  have hN : 0 < N := lt_of_le_of_ne (norm_nonneg _) hN0.symm
  let u : α → ℝ := N⁻¹ • w
  have hu : ‖WithLp.toLp 2 u‖ = 1 := by
    simp only [u, WithLp.toLp_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hN.le)]
    exact inv_mul_cancel₀ hN0
  have hLaw := hasLaw_dotProduct_gaussianVector u hu
  have hi : Integrable (fun z => (u ⬝ᵥ z) ^ (2 * p)) (gaussianVector α) := by
    have h := integrable_pow_gaussianReal (2 * p)
    rw [← hLaw.map_eq] at h
    have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * p))
        ((gaussianVector α).map (fun z => u ⬝ᵥ z)) := by fun_prop
    exact (integrable_map_measure hmeas hLaw.aemeasurable).1 h
  have he (z : α → ℝ) : (w ⬝ᵥ z) ^ (2 * p) = N ^ (2 * p) * (u ⬝ᵥ z) ^ (2 * p) := by
    rw [← mul_pow]
    congr 1
    simp [u, smul_dotProduct, smul_eq_mul, hN0]
  have hNsq : N ^ 2 = w ⬝ᵥ w := norm_toLp_sq_eq_dotProduct_self w
  constructor
  · simpa only [← he] using hi.const_mul (N ^ (2 * p))
  · simp_rw [he]
    have hI : (∫ z, (u ⬝ᵥ z) ^ (2 * p) ∂gaussianVector α) =
        ∫ z : ℝ, z ^ (2 * p) ∂gaussianReal 0 1 := by
      simpa only [Function.comp_def] using hLaw.integral_comp
        (f := fun z : ℝ => z ^ (2 * p)) (by fun_prop)
    rw [integral_const_mul, hI,
      integral_pow_two_mul_gaussianReal, pow_mul, hNsq]
    exact mul_comm _ _

end NLAlib
