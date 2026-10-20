import NLAlib.Matrix.Functions.HermitianResolvent
import NLAlib.Matrix.Norms.QuadraticSeries

/-!
# Spectral-norm Lipschitz bounds for actual Hermitian resolvents

The native second resolvent identity and actual Hermitian inverse estimates
give the inverse-height-squared perturbation constant, with no dimension loss.
Real Hermitian Gaussian coefficient series then use their quadratic energy.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 5.5.
Prerequisite for independent-sum-spectrum-universality.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

open scoped Matrix.Norms.L2Operator in
/-- The native spectral norm of a nonreal Hermitian resolvent is Lipschitz
with inverse squared imaginary-height constant. Empty dimensions are included. -/
theorem abs_specNorm_resolvent_sub_le
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    |specNorm (resolvent A ζ) - specNorm (resolvent B ζ)| ≤
      (|ζ.im|⁻¹) ^ 2 * specNorm (A - B) := by
  have hAr : ζ ∈ resolventSet ℂ A := by
    change IsUnit (algebraMap ℂ (Matrix n n ℂ) ζ - A)
    simpa only [Algebra.algebraMap_eq_smul_one] using hA.isUnit_smul_one_sub_of_im_ne_zero hζ
  have hBr : ζ ∈ resolventSet ℂ B := by
    change IsUnit (algebraMap ℂ (Matrix n n ℂ) ζ - B)
    simpa only [Algebra.algebraMap_eq_smul_one] using hB.isUnit_smul_one_sub_of_im_ne_zero hζ
  calc
    _ ≤ specNorm (resolvent A ζ - resolvent B ζ) := by
      simpa only [specNorm_eq_norm] using abs_norm_sub_norm_le (resolvent A ζ) (resolvent B ζ)
    _ = specNorm (resolvent A ζ * (A - B) * resolvent B ζ) := by
      rw [spectrum.resolvent_sub_resolvent hAr hBr]
    _ ≤ (specNorm (resolvent A ζ) * specNorm (A - B)) * specNorm (resolvent B ζ) :=
      (specNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ (|ζ.im|⁻¹ * specNorm (A - B)) * |ζ.im|⁻¹ := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (hA.specNorm_resolvent_le hζ) (specNorm_nonneg _))
        (hB.specNorm_resolvent_le hζ) (specNorm_nonneg _)
        (mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (specNorm_nonneg _))
    _ = _ := by ring

/-- A genuine Hermitian affine coefficient series has the sharp resolvent-norm
Euclidean Lipschitz constant supplied by its quadratic coefficient energy.
This lemma does not identify quadratic weak variance with bilinear weak variance;
the latter supplies a valid upper bound by taking the two unit vectors equal. -/
theorem abs_specNorm_resolvent_affineSeries_sub_le_of_quadratic_energy
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (x y : ι → ℝ) :
    |specNorm (resolvent (D + ∑ i, x i • A i) ζ) -
      specNorm (resolvent (D + ∑ i, y i • A i) ζ)| ≤
      (σ * (|ζ.im|⁻¹) ^ 2) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  have hx : (D + ∑ i, x i • A i).IsHermitian :=
    hD.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hy : (D + ∑ i, y i • A i).IsHermitian :=
    hD.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hd : (D + ∑ i, x i • A i) - (D + ∑ i, y i • A i) =
      ∑ i, (x i - y i) • A i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  calc
    _ ≤ (|ζ.im|⁻¹) ^ 2 * specNorm ((D + ∑ i, x i • A i) - (D + ∑ i, y i • A i)) :=
      abs_specNorm_resolvent_sub_le _ _ hx hy ζ hζ
    _ = (|ζ.im|⁻¹) ^ 2 * specNorm (∑ i, (x i - y i) • A i) := by rw [hd]
    _ ≤ (|ζ.im|⁻¹) ^ 2 * (σ * Real.sqrt (∑ i, (x i - y i) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (specNorm_sum_smul_le_of_quadratic_energy A hA hσ henergy (fun i => x i - y i))
        (by positivity)
    _ = _ := by ring

end NLAlib
