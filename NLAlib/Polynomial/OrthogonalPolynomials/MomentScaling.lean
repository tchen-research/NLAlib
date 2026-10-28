import NLAlib.Polynomial.OrthogonalPolynomials.FiniteMomentSystem

/-!
# Scaling a polynomial moment functional

A nonzero scalar changes its mass and squared bilinear norms but preserves
its canonical monic polynomials. This permits normalization of numerator and
denominator leading coefficients without assuming that they are positive.
-/

noncomputable section
open Polynomial
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- Scaling a functional scales every entry of its finite Hankel matrix. -/
theorem hankelMomentMatrix_smul (c : 𝕜) (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    hankelMomentMatrix (c • L) n = c • hankelMomentMatrix L n := by
  ext i j
  simp [hankelMomentMatrix]

/-- The Hankel determinant scales by the dimension's power of the scalar. -/
theorem hankelMomentDet_smul (c : 𝕜) (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    hankelMomentDet (c • L) n = c^n * hankelMomentDet L n := by
  rw [hankelMomentDet, hankelMomentMatrix_smul, Matrix.det_smul]
  simp only [Fintype.card_fin, hankelMomentDet]

/-- Nonzero scaling preserves the finite canonical monic polynomial. -/
theorem monicOrthogonalPolynomial_smul (c : 𝕜) (hc : c ≠ 0) (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {n : ℕ} (hn : hankelMomentDet L n ≠ 0) :
    monicOrthogonalPolynomial (c • L) n = monicOrthogonalPolynomial L n := by
  have hcn : hankelMomentDet (c • L) n ≠ 0 := by
    rw [hankelMomentDet_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hn
  have hp := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hn
  apply (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (c • L) hcn).eq_of_hankelMomentDet_ne_zero _ hcn
  refine ⟨hp.monic, hp.natDegree_eq, ?_⟩
  intro q hq
  simp only [LinearMap.smul_apply, smul_eq_mul, hp.orthogonal q hq, mul_zero]

end NLAlib
