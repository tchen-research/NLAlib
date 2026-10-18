import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Spectral.CourantFischer
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Hermitian series controlled by quadratic-form coefficient energy

Uniform square-energy bounds on the unit-vector quadratic forms control the
spectral norm of every scalar coefficient combination. This gives the weak
variance Lipschitz estimate in Gaussian extreme-eigenvalue comparison.
-/

noncomputable section
open scoped Matrix
open Matrix Finset
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- An upper bound on every unit quadratic-form coefficient energy bounds the
norm of any real coefficient combination by the Euclidean coefficient norm.
The quadratic forms are evaluated on complex unit vectors, so this is the
Hermitian weak-variance quantity rather than a bilinear variance parameter. -/
theorem specNorm_sum_smul_le_of_quadratic_energy
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2) (x : ι → ℝ) :
    specNorm (∑ i, x i • A i) ≤ σ * Real.sqrt (∑ i, x i ^ 2) := by
  classical
  have hB : (∑ i, x i • A i).IsHermitian :=
    isSelfAdjoint_sum _ (fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  rw [hB.specNorm_eq_norm_eigenvalues]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hσ (Real.sqrt_nonneg _))).mpr
  intro j
  let u : n → ℂ := fun k => hB.eigenvectorBasis j k
  have hu : ‖WithLp.toLp 2 u‖ = 1 := by
    simpa only [u, WithLp.toLp_ofLp] using hB.eigenvectorBasis.norm_eq_one j
  have hq : (quadForm (∑ i, x i • A i) u).re =
      ∑ i, x i * (quadForm (A i) u).re := by
    simp only [quadForm, Matrix.sum_mulVec, dotProduct_sum,
      Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Real.norm_eq_abs, hB.eigenvalues_eq]
  change |(quadForm (∑ i, x i • A i) u).re| ≤ _
  rw [hq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x
    (fun i => (quadForm (A i) u).re)
  have hsx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb := mul_le_mul_of_nonneg_left (henergy u hu) hsx
  have ht := hcs.trans hb
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hσ (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hsx]
  simpa only [mul_comm] using ht

end NLAlib
