import NLAlib.Matrix.Functions.LyapunovControllability
import NLAlib.Matrix.Functions.LyapunovStability
import NLAlib.Matrix.Spectral.Complexification

/-! # Actual real continuous Lyapunov Gramians -/
noncomputable section
open MeasureTheory Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
set_option backward.isDefEq.respectTransparency false

/-- Entrywise real part, as a continuous real linear map on matrices. -/
def matrixRealPart : Matrix n n ℂ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.map Complex.re
      map_add' := by intro A B; ext i j; simp
      map_smul' := by intro c A; ext i j; simp }

@[simp] theorem matrixRealPart_complexification (A : Matrix n n ℝ) :
    matrixRealPart (realMatrixComplexification A) = A := by ext i j; rfl

private theorem complexification_injective :
    Function.Injective (realMatrixComplexification (n := n) (𝕜 := ℂ)) :=
  Function.LeftInverse.injective matrixRealPart_complexification

/-- Complexification commutes with the actual real matrix exponential. -/
theorem realMatrixComplexification_matrixExp (A : Matrix n n ℝ) :
    (realMatrixComplexification (matrixExp A) : Matrix n n ℂ) =
      matrixExp (realMatrixComplexification A) := by
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) realMatrixComplexification
    continuous_realMatrixComplexification A (by
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _)

/-- The actual real semigroup integrand. -/
def realLyapunovIntegrand (A Q : Matrix n n ℝ) (t : ℝ) : Matrix n n ℝ :=
  matrixExp (t • A) * Q * (matrixExp (t • A))ᴴ

/-- The actual real improper Bochner Gramian. -/
def realLyapunovGramian (A Q : Matrix n n ℝ) : Matrix n n ℝ :=
  ∫ t in Ioi (0 : ℝ), realLyapunovIntegrand A Q t

/-- The actual integrands commute with scalar extension. -/
theorem realMatrixComplexification_lyapunovIntegrand (A Q : Matrix n n ℝ) (t : ℝ) :
    (realMatrixComplexification (realLyapunovIntegrand A Q t) : Matrix n n ℂ) =
      lyapunovIntegrand (realMatrixComplexification A) (realMatrixComplexification Q) t := by
  unfold realLyapunovIntegrand lyapunovIntegrand
  rw [map_mul, map_mul, realMatrixComplexification_matrixExp, map_smul]
  have hstar : (realMatrixComplexification (matrixExp (t • A))ᴴ : Matrix n n ℂ) =
      (realMatrixComplexification (matrixExp (t • A)))ᴴ := map_star realMatrixComplexification _
  rw [hstar, realMatrixComplexification_matrixExp, map_smul]

/-- Hurwitz stability of the complexification proves absolute integrability
of the actual real semigroup integrand. -/
theorem integrableOn_realLyapunovIntegrand (A Q : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) :
    IntegrableOn (realLyapunovIntegrand A Q) (Ioi 0) := by
  have h := matrixRealPart.integrable_comp
    (integrableOn_lyapunovIntegrand (realMatrixComplexification A) (realMatrixComplexification Q) hA)
  have heq : (fun t => matrixRealPart (lyapunovIntegrand (realMatrixComplexification A)
      (realMatrixComplexification Q) t)) = realLyapunovIntegrand A Q := by
    funext t
    rw [← realMatrixComplexification_lyapunovIntegrand, matrixRealPart_complexification]
  rw [heq] at h
  exact h

/-- Scalar extension commutes with the genuine real improper integral. -/
theorem realMatrixComplexification_realLyapunovGramian (A Q : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) :
    (realMatrixComplexification (realLyapunovGramian A Q) : Matrix n n ℂ) =
      lyapunovGramian (realMatrixComplexification A) (realMatrixComplexification Q) := by
  let F := (realMatrixComplexification (n := n) (𝕜 := ℂ)).toLinearMap.toContinuousLinearMap
  have h := F.integral_comp_comm (integrableOn_realLyapunovIntegrand A Q hA)
  change (∫ t in Ioi (0 : ℝ), realMatrixComplexification (realLyapunovIntegrand A Q t)) =
    realMatrixComplexification (realLyapunovGramian A Q) at h
  rw [← h]
  simp only [realMatrixComplexification_lyapunovIntegrand, lyapunovGramian]

private theorem posDef_of_complexification_posDef (A : Matrix n n ℝ)
    (hA : (realMatrixComplexification A : Matrix n n ℂ).PosDef) : A.PosDef := by
  apply ((posSemidef_realMatrixComplexification_iff A).mp hA.posSemidef).posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have hn := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  apply (isUnit_iff_ne_zero.mp hn)
  change (A.map (algebraMap ℝ ℂ)).det = 0
  have hd := (algebraMap ℝ ℂ).map_det A
  rw [hzero, map_zero] at hd
  exact hd.symm

/-- The actual real Gramian is the unique real solution. Source: user
derivations, continuous Lyapunov Gramian.
atlas: lyapunov-stability-gramian (partial) -/
theorem realLyapunovGramian_equation_unique (A Q : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) :
    A * realLyapunovGramian A Q + realLyapunovGramian A Q * Aᴴ + Q = 0 ∧
      ∀ X : Matrix n n ℝ, A * X + X * Aᴴ + Q = 0 → X = realLyapunovGramian A Q := by
  have hstar : (realMatrixComplexification Aᴴ : Matrix n n ℂ) =
      (realMatrixComplexification A)ᴴ := map_star realMatrixComplexification A
  have he := (existsUnique_lyapunov_of_hurwitz (realMatrixComplexification A)
    (realMatrixComplexification Q) hA)
  have hG := realMatrixComplexification_realLyapunovGramian A Q hA
  have hEq : (realMatrixComplexification A) * lyapunovGramian (realMatrixComplexification A) (realMatrixComplexification Q) +
      lyapunovGramian (realMatrixComplexification A) (realMatrixComplexification Q) * (realMatrixComplexification A)ᴴ +
      realMatrixComplexification Q = 0 := by
    rw [lyapunovGramian_eq_of_solution _ _ _ hA (lyapunovCayleySolution_equation _ _ hA)]
    exact lyapunovCayleySolution_equation _ _ hA
  constructor
  · apply complexification_injective
    simpa only [map_add, map_mul, hstar, hG, map_zero] using hEq
  · intro X hX
    apply complexification_injective
    rw [hG]
    exact lyapunovGramian_eq_of_solution _ _ _ hA (by
      have h := congrArg (realMatrixComplexification (n := n) (𝕜 := ℂ)) hX
      simpa only [map_add, map_mul, hstar, map_zero] using h) |>.symm

/-- Positive semidefinite forcing gives an actual real PSD Gramian. -/
theorem posSemidef_realLyapunovGramian (A Q : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) (hQ : Q.PosSemidef) :
    (realLyapunovGramian A Q).PosSemidef := by
  apply (posSemidef_realMatrixComplexification_iff (𝕜 := ℂ) _).mp
  rw [realMatrixComplexification_realLyapunovGramian A Q hA]
  exact posSemidef_lyapunovGramian _ _ hA ((posSemidef_realMatrixComplexification_iff Q).mpr hQ)

/-- Positive definite real forcing gives a real positive definite Gramian. -/
theorem posDef_realLyapunovGramian (A Q : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) (hQ : Q.PosDef) :
    (realLyapunovGramian A Q).PosDef := by
  apply posDef_of_complexification_posDef
  rw [realMatrixComplexification_realLyapunovGramian A Q hA]
  exact posDef_lyapunovGramian _ _ hA (posDef_realMatrixComplexification hQ)

/-- Hurwitz stability of a real matrix is equivalent to a strict real
positive definite Lyapunov certificate. -/
theorem isHurwitz_complexification_iff_exists_real_posDef_lyapunov (A : Matrix n n ℝ) :
    IsHurwitz (realMatrixComplexification A : Matrix n n ℂ) ↔
      ∃ X : Matrix n n ℝ, X.PosDef ∧ (-(A * X + X * Aᴴ)).PosDef := by
  constructor
  · intro hA
    let X := realLyapunovGramian A 1
    have heq := (realLyapunovGramian_equation_unique A 1 hA).1
    refine ⟨X, posDef_realLyapunovGramian A 1 hA Matrix.PosDef.one, ?_⟩
    have hsum : A * X + X * Aᴴ = -1 := eq_neg_of_add_eq_zero_left heq
    rw [hsum, neg_neg]
    exact Matrix.PosDef.one
  · rintro ⟨X, hX, hR⟩
    apply isHurwitz_of_posDef_lyapunov _ (realMatrixComplexification X) (posDef_realMatrixComplexification hX)
    have h := posDef_realMatrixComplexification (𝕜 := ℂ) hR
    have hstar : (realMatrixComplexification Aᴴ : Matrix n n ℂ) =
        (realMatrixComplexification A)ᴴ := map_star realMatrixComplexification A
    simpa only [map_neg, map_add, map_mul, hstar] using h

end NLAlib
