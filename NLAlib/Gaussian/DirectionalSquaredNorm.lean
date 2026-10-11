import NLAlib.Gaussian.Extreme.ChiSquare
import NLAlib.Matrix.Norms
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian chi-square domination from directional sub-Gaussian proxies

Gaussian linearization compares the squared norm MGF of an actual finite
random vector with the standard Gaussian chi-square MGF. This is the sharp
additive row flattening input for the classical one-sign SRHT.
Source: operator re-derivation `sh:srht-quadratic`; supports `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal
namespace NLAlib

/-- The exponential integral of a standard Gaussian linear form is its exact
quadratic MGF. Source: the product Gaussian law; supports SRHT Gaussian linearization. -/
theorem integral_exp_dotProduct_pi_gaussianReal {d : ℕ} (a : Fin d → ℝ) :
    ∫ g : Fin d → ℝ, Real.exp (a ⬝ᵥ g) ∂Measure.pi (fun _ => gaussianReal 0 1) =
      Real.exp ((a ⬝ᵥ a) / 2) := by
  have hs : ∀ t : ℝ, ∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 1 = Real.exp (t ^ 2 / 2) := by
    intro t
    simpa only [mgf, id_eq, zero_mul, NNReal.coe_one, one_mul, zero_add] using
      congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [dotProduct, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp (a i * x))]
  simp_rw [hs]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_div]
  simp only [pow_two]

/-- Gaussian linearization exactly represents a squared-norm exponential as
the Gaussian integral of a linear exponential, including `θ = 0`.
Source: the standard Gaussian MGF; supports classical SRHT row flattening. -/
theorem integral_exp_sqrt_mul_dotProduct_pi_gaussianReal {d : ℕ}
    (v : Fin d → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ g : Fin d → ℝ, Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ v))
        ∂Measure.pi (fun _ => gaussianReal 0 1) = Real.exp (θ * (v ⬝ᵥ v)) := by
  have heq : (fun g : Fin d → ℝ => Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ v))) =
      (fun g => Real.exp ((Real.sqrt (2 * θ) • v) ⬝ᵥ g)) := by
    funext g
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm g v]
  rw [heq, integral_exp_dotProduct_pi_gaussianReal, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  congr 1
  have hs := Real.sq_sqrt (show 0 ≤ 2 * θ by positivity)
  rw [← mul_assoc, ← sq, hs]
  ring

/-- An actual finite random vector with directional MGF proxy `‖u‖²` has
squared-norm MGF at most `(1−2θ)^(-d/2)`. The Gaussian linearization and every
finite expectation are proved from the stated directional proxies.
Source: classical SRHT row flattening; supports operator re-derivation `sh:srht`. -/
theorem integral_exp_sq_norm_le_chi_square_mgf
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      ⟨u ⬝ᵥ u, dotProduct_self_nonneg u⟩ p.toMeasure)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    ∫ ω, Real.exp (θ * (X ω ⬝ᵥ X ω)) ∂p.toMeasure ≤
      (1 - 2 * θ) ^ (-((d : ℝ) / 2)) := by
  let γ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let F : Ω → (Fin d → ℝ) → ℝ := fun ω g =>
    Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ X ω))
  have hF : ∀ ω, Integrable (F ω) γ := by
    intro ω
    apply Integrable.of_integral_ne_zero
    rw [show (∫ g, F ω g ∂γ) = Real.exp (θ * (X ω ⬝ᵥ X ω)) from
      integral_exp_sqrt_mul_dotProduct_pi_gaussianReal (X ω) hθ0]
    exact (Real.exp_pos _).ne'
  have hgauss : (∫ g : Fin d → ℝ, Real.exp (θ * (g ⬝ᵥ g)) ∂γ) =
      (1 - 2 * θ) ^ (-((d : ℝ) / 2)) := by
    have hh := integral_exp_neg_mul_sum_sq_pi_gaussianReal (ι := Fin d) (1 - 2 * θ)
      (show 0 < 1 - 2 * θ by linarith)
    rw [show -((1 - 2 * θ - 1) / 2) = θ by ring, Fintype.card_fin] at hh
    simpa only [dotProduct, ← sq] using hh
  have hgint : Integrable (fun g : Fin d → ℝ => Real.exp (θ * (g ⬝ᵥ g))) γ :=
    Integrable.of_integral_ne_zero (by rw [hgauss]; exact
      (Real.rpow_pos_of_pos (show 0 < 1 - 2 * θ by linarith) _).ne')
  have hsumint : Integrable (fun g => ∑ ω, (p ω).toReal * F ω g) γ :=
    integrable_finsetSum _ (fun ω _ => (hF ω).const_mul (p ω).toReal)
  have hpoint : ∀ g : Fin d → ℝ, (∑ ω, (p ω).toReal * F ω g) ≤
      Real.exp (θ * (g ⬝ᵥ g)) := by
    intro g
    let u := Real.sqrt (2 * θ) • g
    have hu : (u ⬝ᵥ u) / 2 = θ * (g ⬝ᵥ g) := by
      dsimp only [u]
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hs := Real.sq_sqrt (show 0 ≤ 2 * θ by positivity)
      rw [← mul_assoc, ← sq, hs]
      ring
    have heq : (fun ω => Real.exp (1 * (X ω ⬝ᵥ u))) = (fun ω => F ω g) := by
      funext ω
      simp only [u, F, one_mul, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    have hh := (hmgf u).mgf_le 1
    rw [mgf, heq, PMF.integral_eq_sum] at hh
    simp only [smul_eq_mul, one_pow, mul_one] at hh
    change (∑ ω, (p ω).toReal * F ω g) ≤ Real.exp ((u ⬝ᵥ u) / 2) at hh
    rwa [hu] at hh
  calc
    _ = ∑ ω, (p ω).toReal * Real.exp (θ * (X ω ⬝ᵥ X ω)) := by
      rw [PMF.integral_eq_sum]
      simp only [smul_eq_mul]
    _ = ∑ ω, (p ω).toReal * ∫ g, F ω g ∂γ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [show (∫ g, F ω g ∂γ) = Real.exp (θ * (X ω ⬝ᵥ X ω)) from
        integral_exp_sqrt_mul_dotProduct_pi_gaussianReal (X ω) hθ0]
    _ = ∫ g, ∑ ω, (p ω).toReal * F ω g ∂γ := by
      rw [integral_finsetSum _ (fun ω _ => (hF ω).const_mul (p ω).toReal)]
      simp only [integral_const_mul]
    _ ≤ ∫ g, Real.exp (θ * (g ⬝ᵥ g)) ∂γ := integral_mono hsumint hgint hpoint
    _ = _ := hgauss

/-- The actual finite random vector's squared-norm tail has the Gaussian
chi-square Chernoff bound, derived from directional proxies.
Source: Gaussian linearization; supports classical SRHT row flattening. -/
theorem measureReal_sq_norm_ge_le_chi_square_mgf
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      ⟨u ⬝ᵥ u, dotProduct_self_nonneg u⟩ p.toMeasure)
    (u θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    p.toMeasure.real {ω | u ≤ X ω ⬝ᵥ X ω} ≤
      Real.exp (-θ * u) * (1 - 2 * θ) ^ (-((d : ℝ) / 2)) := by
  have hh := measure_ge_le_exp_mul_mgf (μ := p.toMeasure)
    (X := fun ω => X ω ⬝ᵥ X ω) u hθ0 (show Integrable _ _ from .of_finite)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact integral_exp_sq_norm_le_chi_square_mgf p X hmgf hθ0 hθ1

/-- Optimized Gaussian-linearization Chernoff tail for an isotropic-proxy
finite vector, for every nonnegative relative threshold.
Source: the chi-square scalar optimization; supports `sh:srht`. -/
theorem measure_sq_norm_ge_one_add_mul_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      ⟨u ⬝ᵥ u, dotProduct_self_nonneg u⟩ p.toMeasure)
    {ε : ℝ} (hε : 0 ≤ ε) :
    p.toMeasure {ω | (1 + ε) * d ≤ X ω ⬝ᵥ X ω} ≤
      ENNReal.ofReal (Real.exp (-((d : ℝ) / 2) * (ε - Real.log (1 + ε)))) := by
  have h1ε : 0 < 1 + ε := by linarith
  let θ := ε / (2 * (1 + ε))
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 / 2 := by
    dsimp only [θ]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have h2 : 1 - 2 * θ = (1 + ε)⁻¹ := by dsimp only [θ]; field_simp; ring
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine (measureReal_sq_norm_ge_le_chi_square_mgf p X hmgf ((1 + ε) * d) θ hθ0 hθ1).trans
    (le_of_eq ?_)
  rw [h2, Real.inv_rpow h1ε.le, ← Real.rpow_neg h1ε.le, neg_neg, Real.rpow_def_of_pos h1ε,
    ← Real.exp_add]
  congr 1
  dsimp only [θ]
  field_simp
  ring

/-- Laurent–Massart's additive upper tail holds for the actual finite vector
from directional sub-Gaussian proxies, by genuine Gaussian linearization.
Source: supports the sharper original classical SRHT flattening constant. -/
theorem measure_sq_norm_ge_add_two_sqrt_mul_add_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      ⟨u ⬝ᵥ u, dotProduct_self_nonneg u⟩ p.toMeasure)
    {x : ℝ} (hx : 0 ≤ x) :
    p.toMeasure {ω | d + 2 * Real.sqrt (d * x) + 2 * x ≤ X ω ⬝ᵥ X ω} ≤
      ENNReal.ofReal (Real.exp (-x)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases hx.eq_or_lt with rfl | hx0
    · simp [dotProduct]
    · have heq : {ω | ((0 : ℕ) : ℝ) + 2 * Real.sqrt (((0 : ℕ) : ℝ) * x) + 2 * x ≤
          X ω ⬝ᵥ X ω} = ∅ := by
        ext ω
        simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero,
          zero_mul, Real.sqrt_zero, mul_zero, zero_add, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        linarith
      rw [heq, measure_empty]
      exact zero_le
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let a := Real.sqrt (x / d)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = x / d := Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt ((d : ℝ) * x) = d * a := by
    rw [show (d : ℝ) * x = (d : ℝ) ^ 2 * (x / d) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hd0.le]
  have hthreshold : (d : ℝ) + 2 * Real.sqrt (d * x) + 2 * x =
      (1 + (2 * a + 2 * a ^ 2)) * d := by
    rw [hsqrt, ha2]
    field_simp
    ring
  rw [hthreshold]
  refine (measure_sq_norm_ge_one_add_mul_le p X hmgf (by positivity)).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hlog : Real.log (1 + (2 * a + 2 * a ^ 2)) ≤ 2 * a := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * a by positivity)
    nlinarith
  have hx' : x = a ^ 2 * d := by rw [ha2]; field_simp
  rw [hx']
  nlinarith

end NLAlib
