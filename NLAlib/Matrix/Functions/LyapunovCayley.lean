import NLAlib.Matrix.Functions.SteinGramian
import NLAlib.Matrix.Spectral.HurwitzCayley

/-!
# Continuous Lyapunov solutions from a stable Cayley transform

The Cayley/Stein reduction constructs the genuine continuous solution and its
positivity before using any continuous semigroup decay theorem.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem mul_cayleyTransform_one (A : Matrix n n ℂ) (hP : IsUnit (A - 1).det) :
    (A - 1) * cayleyTransform A 1 = A + 1 := by
  rw [cayleyTransform_eq_one_add A 1 (by simpa using hP)]
  simp only [RCLike.ofReal_one, one_smul, mul_one, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_nonsing_inv _ hP]
  module

private theorem cayley_congruence_identity (A X : Matrix n n ℂ)
    (hP : IsUnit (A - 1).det) :
    (A - 1) * (X - cayleyTransform A 1 * X * (cayleyTransform A 1)ᴴ) * (A - 1)ᴴ =
      -(2 : ℂ) • (A * X + X * Aᴴ) := by
  have hT := mul_cayleyTransform_one A hP
  have hstar : (cayleyTransform A 1)ᴴ * (A - 1)ᴴ = (A + 1)ᴴ := by
    rw [← Matrix.conjTranspose_mul, hT]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  have hterm : (A - 1) * (cayleyTransform A 1 * X * (cayleyTransform A 1)ᴴ) * (A - 1)ᴴ =
      (A + 1) * X * (A + 1)ᴴ := by
    simp only [← Matrix.mul_assoc] at *
    rw [hT]
    rw [Matrix.mul_assoc _ (cayleyTransform A 1)ᴴ (A - 1)ᴴ, hstar]
  rw [hterm]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one]
  module

/-- The stable Cayley construction of a continuous Lyapunov solution. -/
def lyapunovCayleySolution (A Q : Matrix n n ℂ) : Matrix n n ℂ :=
  steinGramian (cayleyTransform A 1) ((2 : ℂ) • ((A - 1)⁻¹ * Q * ((A - 1)⁻¹)ᴴ))

/-- The continuous Lyapunov equation follows from the actual convergent
Cayley Stein Gramian. No continuous exponential bound is a hypothesis. -/
theorem lyapunovCayleySolution_equation (A Q : Matrix n n ℂ) (hA : IsHurwitz A) :
    A * lyapunovCayleySolution A Q + lyapunovCayleySolution A Q * Aᴴ + Q = 0 := by
  have hP : IsUnit (A - 1).det := by
    simpa using (Matrix.isUnit_iff_isUnit_det _).mp (hA.isUnit_sub_pos_smul_one 1 zero_lt_one)
  have hT := hA.spectralRadius_cayleyTransform_lt_one 1 zero_lt_one
  have hs := summable_stein_of_spectralRadius_lt_one (cayleyTransform A 1)
    ((2 : ℂ) • ((A - 1)⁻¹ * Q * ((A - 1)⁻¹)ᴴ)) hT
  have heq := steinGramian_sub_mul_mul_conjTranspose _ _ hs
  change lyapunovCayleySolution A Q - cayleyTransform A 1 * lyapunovCayleySolution A Q *
    (cayleyTransform A 1)ᴴ = (2 : ℂ) • ((A - 1)⁻¹ * Q * ((A - 1)⁻¹)ᴴ) at heq
  have he := congrArg (fun M : Matrix n n ℂ => (A - 1) * M * (A - 1)ᴴ) heq
  rw [cayley_congruence_identity A _ hP] at he
  have hright : (A - 1) * ((2 : ℂ) • ((A - 1)⁻¹ * Q * ((A - 1)⁻¹)ᴴ)) * (A - 1)ᴴ =
      (2 : ℂ) • Q := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.conjTranspose_one, Matrix.mul_one]
  rw [hright, neg_smul] at he
  have hzero : (2 : ℂ) • (A * lyapunovCayleySolution A Q + lyapunovCayleySolution A Q * Aᴴ + Q) = 0 := by
    rw [smul_add, ← he]
    abel
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- The Cayley construction preserves PSD forcing. -/
theorem posSemidef_lyapunovCayleySolution (A Q : Matrix n n ℂ)
    (hA : IsHurwitz A) (hQ : Q.PosSemidef) : (lyapunovCayleySolution A Q).PosSemidef := by
  apply posSemidef_steinGramian
  · exact (hQ.mul_mul_conjTranspose_same (A - 1)⁻¹).smul (by norm_num : (0 : ℂ) ≤ 2)
  · exact summable_stein_of_spectralRadius_lt_one _ _
      (hA.spectralRadius_cayleyTransform_lt_one 1 zero_lt_one)

/-- Positive definite forcing gives a positive definite continuous solution.
This supplies the strict Lyapunov certificate needed to obtain uniform
Hurwitz semigroup decay. Source: user derivations, Lyapunov stability.
atlas: lyapunov-stability-gramian (partial) -/
theorem posDef_lyapunovCayleySolution (A Q : Matrix n n ℂ)
    (hA : IsHurwitz A) (hQ : Q.PosDef) : (lyapunovCayleySolution A Q).PosDef := by
  have hP : IsUnit (A - 1) := by simpa using hA.isUnit_sub_pos_smul_one 1 zero_lt_one
  have hPi : IsUnit (A - 1)⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have hforce : (((2 : ℂ) • ((A - 1)⁻¹ * Q * ((A - 1)⁻¹)ᴴ))).PosDef :=
    ((Matrix.IsUnit.posDef_star_right_conjugate_iff hPi).mpr hQ).smul (by norm_num : (0 : ℂ) < 2)
  exact posDef_steinGramian _ _ hforce
    (summable_stein_of_spectralRadius_lt_one _ _ (hA.spectralRadius_cayleyTransform_lt_one 1 zero_lt_one))

end NLAlib
