import NLAlib.Gaussian.Concentration.Stein
import NLAlib.ForMathlib.MeasureTheory.IntegralConvergence

/-!
# Coordinate Stein identities and the hard-edge weak limit

This file converts actual coordinate first and second derivatives of regularized
spectral functions into the scalar Gaussian weak inequality, and handles the
one-sided limit without assuming inverse-gap integrability.
Source: operator rederivations, Section 5; atlas wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace NLAlib

/-- The Gaussian coordinate Stein identity summed over a differentiable scalar
function's first and second coordinate derivatives. All integrability premises
refer to actual derivative expressions, allowing polynomial growth.
Source: operator rederivations, Section 5; atlas wishart-lambda-min-tail (helper). -/
theorem integral_stein_energy_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (D DD : ι → (ι → ℝ) → ℝ)
    (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ)
    (hF : ∀ i x t, HasDerivAt (fun y => F (Function.update x i y))
      (D i (Function.update x i t)) t)
    (hD : ∀ i x t, HasDerivAt (fun y => D i (Function.update x i y))
      (DD i (Function.update x i t)) t)
    (hfi : ∀ i, Integrable (fun x => ψ (F x) * D i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hxi : ∀ i, Integrable (fun x => x i * (ψ (F x) * D i x))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hgi : ∀ i, Integrable (fun x => deriv ψ (F x) * D i x ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hddi : ∀ i, Integrable (fun x => ψ (F x) * DD i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) + ψ (F x) * (∑ i, DD i x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
    ∫ x, ψ (F x) * (∑ i, x i * D i x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hcoord (i : ι) :
      (∫ x, x i * (ψ (F x) * D i x) ∂μ) =
      ∫ x, deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x ∂μ := by
    apply integral_coordinate_mul_eq_integral_gaussian_of_hasDerivAt_update
      (fun x => ψ (F x) * D i x)
      (fun x => deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x) i ?_
      (hfi i) (hxi i) ((hgi i).add (hddi i))
    intro x t
    convert! (((hψ (F (Function.update x i t))).hasDerivAt.comp t (hF i x t)).mul
      (hD i x t)) using 1
    simp only [Function.comp_def]
    ring
  calc
    _ = ∫ x, ∑ i, (deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ i, ∫ x, deriv ψ (F x) * D i x ^ 2 + ψ (F x) * DD i x ∂μ :=
      integral_finsetSum _ (fun i _ => (hgi i).add (hddi i))
    _ = ∑ i, ∫ x, x i * (ψ (F x) * D i x) ∂μ :=
      Finset.sum_congr rfl fun i _ => (hcoord i).symm
    _ = ∫ x, ∑ i, x i * (ψ (F x) * D i x) ∂μ :=
      (integral_finsetSum _ (fun i _ => hxi i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The coordinate Stein identity in the shifted form used by the one-sided
hard-edge limit. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem integral_stein_shift_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (D DD : ι → (ι → ℝ) → ℝ)
    (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ) (b : ℝ)
    (hF : ∀ i x t, HasDerivAt (fun y => F (Function.update x i y))
      (D i (Function.update x i t)) t)
    (hD : ∀ i x t, HasDerivAt (fun y => D i (Function.update x i y))
      (DD i (Function.update x i t)) t)
    (hψi : Integrable (fun x => ψ (F x))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hfi : ∀ i, Integrable (fun x => ψ (F x) * D i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hxi : ∀ i, Integrable (fun x => x i * (ψ (F x) * D i x))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hgi : ∀ i, Integrable (fun x => deriv ψ (F x) * D i x ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hddi : ∀ i, Integrable (fun x => ψ (F x) * DD i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) +
      (b - ∑ i, x i * D i x) * ψ (F x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
    ∫ x, (b - ∑ i, DD i x) * ψ (F x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hAi : Integrable (fun x => deriv ψ (F x) * (∑ i, D i x ^ 2)) μ := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hgi i)
  have hCi : Integrable (fun x => ψ (F x) * (∑ i, DD i x)) μ := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hddi i)
  have hBi : Integrable (fun x => ψ (F x) * (∑ i, x i * D i x)) μ := by
    have hh := integrable_finsetSum Finset.univ (fun i _ => hxi i)
    convert! hh using 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he := integral_stein_energy_eq F D DD ψ hψ hF hD hfi hxi hgi hddi
  rw [integral_add hAi hCi] at he
  have hleft :
      (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) +
          (b - ∑ i, x i * D i x) * ψ (F x) ∂μ) =
      (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) ∂μ) +
        b * (∫ x, ψ (F x) ∂μ) -
          ∫ x, ψ (F x) * (∑ i, x i * D i x) ∂μ := by
    have hfun :
        (fun x => deriv ψ (F x) * (∑ i, D i x ^ 2) +
          (b - ∑ i, x i * D i x) * ψ (F x)) =
        (fun x => (deriv ψ (F x) * (∑ i, D i x ^ 2) + b * ψ (F x)) -
          ψ (F x) * (∑ i, x i * D i x)) := by
      funext x
      ring
    rw [hfun]
    have hs :
        (∫ x, (deriv ψ (F x) * (∑ i, D i x ^ 2) + b * ψ (F x)) -
          ψ (F x) * (∑ i, x i * D i x) ∂μ) =
        (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) + b * ψ (F x) ∂μ) -
          ∫ x, ψ (F x) * (∑ i, x i * D i x) ∂μ :=
      integral_sub (hAi.add (hψi.const_mul b)) hBi
    have ha :
        (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) + b * ψ (F x) ∂μ) =
        (∫ x, deriv ψ (F x) * (∑ i, D i x ^ 2) ∂μ) + ∫ x, b * ψ (F x) ∂μ :=
      integral_add hAi (hψi.const_mul b)
    rw [hs, ha, integral_const_mul]
  have hright :
      (∫ x, (b - ∑ i, DD i x) * ψ (F x) ∂μ) =
        b * (∫ x, ψ (F x) ∂μ) - ∫ x, ψ (F x) * (∑ i, DD i x) ∂μ := by
    have hfun : (fun x => (b - ∑ i, DD i x) * ψ (F x)) =
        (fun x => b * ψ (F x) - ψ (F x) * (∑ i, DD i x)) := by
      funext x
      ring
    rw [hfun, integral_sub (hψi.const_mul b) hCi, integral_const_mul]
  rw [hleft, hright]
  linarith

/-- Actual Gaussian coordinate derivatives and a dominated one-sided regularization
limit imply the weak inequality. This assembles the Stein identity and the Fatou
step; the derivative, growth, and limit hypotheses are the reusable concrete
matrix-calculus obligations. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem integral_nonneg_of_gaussian_coordinate_approximation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℕ → (ι → ℝ) → ℝ) (D DD : ℕ → ι → (ι → ℝ) → ℝ)
    (X A' B' C' : (ι → ℝ) → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (b K P : ℝ) (hP : 0 ≤ P)
    (hψ0 : ∀ t, 0 ≤ ψ t) (hψP : ∀ t, ψ t ≤ P)
    (hF : ∀ n i x t, HasDerivAt (fun y => F n (Function.update x i y))
      (D n i (Function.update x i t)) t)
    (hD : ∀ n i x t, HasDerivAt (fun y => D n i (Function.update x i y))
      (DD n i (Function.update x i t)) t)
    (hψi : ∀ n, Integrable (fun x => ψ (F n x))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hfi : ∀ n i, Integrable (fun x => ψ (F n x) * D n i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hxi : ∀ n i, Integrable (fun x => x i * (ψ (F n x) * D n i x))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hgi : ∀ n i, Integrable (fun x => deriv ψ (F n x) * D n i x ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hddi : ∀ n i, Integrable (fun x => ψ (F n x) * DD n i x)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hupper : ∀ n, ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1),
      (∑ i, DD n i x) ≤ K)
    (hFlim : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1),
      Tendsto (fun n => F n x) atTop (𝓝 (X x)))
    (hAlim : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1),
      Tendsto (fun n => ∑ i, D n i x ^ 2) atTop (𝓝 (A' x)))
    (hBlim : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1),
      Tendsto (fun n => ∑ i, x i * D n i x) atTop (𝓝 (B' x)))
    (hClim : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1),
      Tendsto (fun n => ∑ i, DD n i x) atTop (𝓝 (C' x)))
    (hC' : ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1), C' x ≤ b)
    (bound : (ι → ℝ) → ℝ)
    (hboundi : Integrable bound (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hbound : ∀ n, ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1),
      ‖deriv ψ (F n x) * (∑ i, D n i x ^ 2) +
        (b - ∑ i, x i * D n i x) * ψ (F n x)‖ ≤ bound x) :
    0 ≤ ∫ x, deriv ψ (X x) * A' x + (b - B' x) * ψ (X x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hAi (n : ℕ) : Integrable (fun x => deriv ψ (F n x) * (∑ i, D n i x ^ 2)) μ := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hgi n i)
  have hCi (n : ℕ) : Integrable (fun x => ψ (F n x) * (∑ i, DD n i x)) μ := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hddi n i)
  have hBi (n : ℕ) : Integrable (fun x => ψ (F n x) * (∑ i, x i * D n i x)) μ := by
    have hh := integrable_finsetSum Finset.univ (fun i _ => hxi n i)
    convert! hh using 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hLi (n : ℕ) : Integrable
      (fun x => deriv ψ (F n x) * (∑ i, D n i x ^ 2) +
        (b - ∑ i, x i * D n i x) * ψ (F n x)) μ := by
    convert! ((hAi n).add ((hψi n).const_mul b)).sub (hBi n) using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hRi (n : ℕ) : Integrable (fun x => (b - ∑ i, DD n i x) * ψ (F n x)) μ := by
    convert! ((hψi n).const_mul b).sub (hCi n) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  exact integral_nonneg_of_shift_identity_limit μ F
    (fun n x => ∑ i, D n i x ^ 2) (fun n x => ∑ i, x i * D n i x)
    (fun n x => ∑ i, DD n i x) X A' B' C' ψ (deriv ψ)
    hψ.continuous (hψ.continuous_deriv le_rfl) b K P hP hψ0 hψP hLi hRi
    (fun n => integral_stein_shift_eq (F n) (D n) (DD n) ψ
      (hψ.differentiable one_ne_zero) b (hF n) (hD n) (hψi n) (hfi n)
      (hxi n) (hgi n) (hddi n))
    hupper hFlim hAlim hBlim hClim hC' bound hboundi hbound

end NLAlib
