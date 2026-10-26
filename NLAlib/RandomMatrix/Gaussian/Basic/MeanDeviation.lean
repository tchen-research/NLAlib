import NLAlib.Probability.Gaussian.Concentration.MeanDeviation
import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import NLAlib.Matrix.Norms.Frobenius

/-!
# Mean deviations for functions of a Gaussian matrix

Transfer the Euclidean Gaussian mean-deviation and finite-maximum bounds to
the actual Gaussian matrix law, using Frobenius Lipschitz constants.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLAlib

private theorem frobNorm_curry_sub {p m : Type*} [Fintype p] [Fintype m]
    (x y : p × m → ℝ) :
    frobNorm (((MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv x) -
      ((MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv y)) =
      Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
  unfold frobNorm
  rw [frobSq_eq_sum_sq]
  congr 1
  rw [Fintype.sum_prod_type]
  rfl

/-- The centered MGF of a Frobenius-Lipschitz Gaussian-matrix observable is
sub-Gaussian with proxy equal to the squared Lipschitz constant. -/
theorem hasSubgaussianMGF_of_lipschitz_gaussianMatrix
    {p m : Type*} [Fintype p] [Fintype m] (f : Matrix p m ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ X Y, |f X - f Y| ≤ L * frobNorm (X - Y)) :
    HasSubgaussianMGF (fun X => f X - ∫ Y, f Y ∂gaussianMatrix p m)
      ⟨L ^ 2, sq_nonneg L⟩ (gaussianMatrix p m) := by
  classical
  let e := (MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv
  have h : HasSubgaussianMGF
      (fun x => f (e x) - ∫ y, f (e y) ∂gaussianVector (p × m))
      ⟨L ^ 2, sq_nonneg L⟩ (gaussianVector (p × m)) := by
    simpa only [one_mul, Function.comp_def] using
      hasSubgaussianMGF_of_logSobolev hasEuclideanLogSobolev_gaussianVector
        (f ∘ e) L hL (fun x y => by rw [← frobNorm_curry_sub]; exact hLip _ _)
  rw [gaussianMatrix_eq_map_curry, integral_map_equiv]
  constructor
  · intro t
    exact (integrable_map_equiv e _).mpr (h.integrable_exp_mul t)
  · intro t
    simpa only [mgf, integral_map_equiv] using h.mgf_le t

/-- A Frobenius-Lipschitz function of an actual standard Gaussian matrix is
integrable, including the zero-Lipschitz case. -/
theorem integrable_of_lipschitz_gaussianMatrix
    {p m : Type*} [Fintype p] [Fintype m] (f : Matrix p m ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ X Y, |f X - f Y| ≤ L * frobNorm (X - Y)) :
    Integrable f (gaussianMatrix p m) := by
  let e := (MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv
  have h := integrable_of_lipschitz_gaussianVector (f ∘ e) L hL (fun x y => by
    rw [← frobNorm_curry_sub]
    exact hLip _ _)
  rw [gaussianMatrix_eq_map_curry]
  exact (integrable_map_equiv e f).mpr h

/-- A Frobenius-Lipschitz observable of an actual Gaussian matrix has mean
absolute deviation at most twice its Lipschitz constant. -/
theorem integral_abs_sub_integral_le_two_mul_of_lipschitz_gaussianMatrix
    {p m : Type*} [Fintype p] [Fintype m] (f : Matrix p m ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ X Y, |f X - f Y| ≤ L * frobNorm (X - Y)) :
    (∫ X, |f X - ∫ Y, f Y ∂gaussianMatrix p m| ∂gaussianMatrix p m) ≤ 2 * L := by
  let e := (MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv
  have h := integral_abs_sub_integral_le_two_mul_of_lipschitz_gaussianVector
    (f ∘ e) L hL (fun x y => by rw [← frobNorm_curry_sub]; exact hLip _ _)
  rw [gaussianMatrix_eq_map_curry, integral_map_equiv, integral_map_equiv]
  exact h

/-- Finite Gaussian-matrix observables with summably small Lipschitz constants
have uniformly bounded expected maximum, without an independence assumption. -/
theorem integral_iSup_le_mean_add_two_mul_sum_of_lipschitz_gaussianMatrix
    {p m κ : Type*} [Fintype p] [Fintype m] [Fintype κ] [Nonempty κ]
    (f : κ → Matrix p m ℝ → ℝ) (L : κ → ℝ) (hL : ∀ k, 0 ≤ L k)
    (hLip : ∀ k X Y, |f k X - f k Y| ≤ L k * frobNorm (X - Y))
    {M : ℝ} (hM : ∀ k, ∫ X, f k X ∂gaussianMatrix p m ≤ M) :
    (∫ X, ⨆ k, f k X ∂gaussianMatrix p m) ≤ M + 2 * ∑ k, L k := by
  apply (integral_iSup_le_mean_add_sum_integral_abs_sub f
    (fun k => integrable_of_lipschitz_gaussianMatrix (f k) (L k) (hL k) (hLip k)) hM).trans
  gcongr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    integral_abs_sub_integral_le_two_mul_of_lipschitz_gaussianMatrix
      (f k) (L k) (hL k) (hLip k)

end NLAlib
