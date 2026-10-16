import NLAlib.Matrix.Functions.LyapunovDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The actual improper continuous Lyapunov Gramian

The Cayley construction supplies a solution, the strict Lyapunov certificate
supplies exponential decay, and improper FTC identifies that solution with
the actual semigroup integral. No decay or integral identity is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The semigroup Gramian integrand, using the adjoint of the actual exponential. -/
def lyapunovIntegrand (A Q : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  matrixExp (t • A) * Q * (matrixExp (t • A))ᴴ

/-- The actual improper Bochner integral over positive time. Changing `Ioi 0`
to `Ici 0` has no effect for Lebesgue measure. -/
def lyapunovGramian (A Q : Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ t in Ioi (0 : ℝ), lyapunovIntegrand A Q t

private theorem continuous_matrixExp_smul (A : Matrix n n ℂ) :
    Continuous (fun t : ℝ => matrixExp (t • A)) := by
  change Continuous (fun t : ℝ => NormedSpace.exp (t • A))
  exact continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const A t).continuousAt

/-- The true Hurwitz semigroup Gramian integrand is absolutely integrable. -/
theorem integrableOn_lyapunovIntegrand (A Q : Matrix n n ℂ) (hA : IsHurwitz A) :
    IntegrableOn (lyapunovIntegrand A Q) (Ioi 0) := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz : lyapunovIntegrand A Q = 0 := by funext t; exact Subsingleton.elim _ _
    rw [hz]
    exact integrable_zero ℝ (Matrix n n ℂ) (volume.restrict (Ioi 0))
  | inr hn =>
    obtain ⟨C, γ, hC, hγ, hbound⟩ := hA.exists_pos_exponential_decay
    have hmajor := (integrableOn_exp_mul_Ioi (by linarith : -2 * γ < 0) (0 : ℝ)).const_mul
      (C ^ 2 * specNorm Q)
    apply hmajor.mono'
    · have hc : Continuous (lyapunovIntegrand A Q) := by
        unfold lyapunovIntegrand
        exact ((continuous_matrixExp_smul A).mul_const Q).mul
          ((show Continuous (fun M : Matrix n n ℂ => Mᴴ) by fun_prop).comp (continuous_matrixExp_smul A))
      exact hc.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← specNorm_eq_norm]
      dsimp [lyapunovIntegrand]
      have hE := hbound t ht.le
      calc
        _ ≤ specNorm (matrixExp (t • A) * Q) * specNorm (matrixExp (t • A))ᴴ := specNorm_mul_le _ _
        _ ≤ (C * Real.exp (-γ * t) * specNorm Q) * (C * Real.exp (-γ * t)) := by
          rw [specNorm_conjTranspose]
          exact mul_le_mul
            ((specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hE (specNorm_nonneg Q)))
            hE (specNorm_nonneg _) (mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) (specNorm_nonneg Q))
        _ = (C ^ 2 * specNorm Q) * (Real.exp (-γ * t) * Real.exp (-γ * t)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

/-- Every propagated fixed matrix tends to zero under a Hurwitz semigroup. -/
theorem tendsto_lyapunovIntegrand_zero (A X : Matrix n n ℂ) (hA : IsHurwitz A) :
    Tendsto (lyapunovIntegrand A X) atTop (𝓝 0) := by
  cases isEmpty_or_nonempty n with
  | inl hn => exact tendsto_const_nhds.congr' (Eventually.of_forall fun _ => Subsingleton.elim _ _)
  | inr hn =>
    obtain ⟨C, γ, hC, hγ, hbound⟩ := hA.exists_pos_exponential_decay
    have hexp : Tendsto (fun t : ℝ => matrixExp (t • A)) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        simpa only [specNorm_eq_norm] using hbound t ht
      · have he := Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by linarith : -γ < 0))
        simpa using he.const_mul C
    have hc : Continuous (fun M : Matrix n n ℂ => Mᴴ) := by fun_prop
    have hstar := hc.continuousAt.tendsto.comp hexp
    convert! (hexp.mul_const X).mul hstar using 1
    simp

private theorem hasDerivAt_lyapunovIntegrand (A X Q : Matrix n n ℂ)
    (hX : A * X + X * Aᴴ + Q = 0) (t : ℝ) :
    HasDerivAt (lyapunovIntegrand A X) (-lyapunovIntegrand A Q t) t := by
  have he : HasDerivAt (fun s : ℝ => matrixExp (s • A)) (matrixExp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  have h := (he.mul_const X).mul he.star
  have hAX : A * X + X * Aᴴ = -Q := eq_neg_of_add_eq_zero_left hX
  convert! h using 1
  change -(matrixExp (t • A) * Q * (matrixExp (t • A))ᴴ) =
      (matrixExp (t • A) * A * X) * (matrixExp (t • A))ᴴ +
        (matrixExp (t • A) * X) * (matrixExp (t • A) * A)ᴴ
  rw [Matrix.conjTranspose_mul]
  calc
    _ = matrixExp (t • A) * (A * X + X * Aᴴ) * (matrixExp (t • A))ᴴ := by rw [hAX]; simp
    _ = _ := by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Every actual continuous Lyapunov solution equals the improper Gramian.
The derivative is integrated by improper FTC and the semigroup endpoint is
proved to vanish. Source: user derivations, continuous Gramian formula (G1).
atlas: lyapunov-stability-gramian (partial) -/
theorem lyapunovGramian_eq_of_solution (A Q X : Matrix n n ℂ) (hA : IsHurwitz A)
    (hX : A * X + X * Aᴴ + Q = 0) : lyapunovGramian A Q = X := by
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hasDerivAt_lyapunovIntegrand A X Q hX t)
    (integrableOn_lyapunovIntegrand A Q hA).neg (tendsto_lyapunovIntegrand_zero A X hA)
  have hzero : lyapunovIntegrand A X 0 = X := by simp [lyapunovIntegrand, matrixExp]
  rw [integral_neg, hzero, zero_sub] at hFTC
  exact neg_injective hFTC

/-- The improper Gramian is the unique Lyapunov solution for Hurwitz data. -/
theorem existsUnique_lyapunov_of_hurwitz (A Q : Matrix n n ℂ) (hA : IsHurwitz A) :
    ∃! X : Matrix n n ℂ, A * X + X * Aᴴ + Q = 0 := by
  refine ⟨lyapunovCayleySolution A Q, lyapunovCayleySolution_equation A Q hA, ?_⟩
  intro Y hY
  exact (lyapunovGramian_eq_of_solution A Q Y hA hY).symm.trans
    (lyapunovGramian_eq_of_solution A Q _ hA (lyapunovCayleySolution_equation A Q hA))

/-- The actual improper Gramian is PSD for PSD forcing. -/
theorem posSemidef_lyapunovGramian (A Q : Matrix n n ℂ) (hA : IsHurwitz A)
    (hQ : Q.PosSemidef) : (lyapunovGramian A Q).PosSemidef := by
  rw [lyapunovGramian_eq_of_solution A Q _ hA (lyapunovCayleySolution_equation A Q hA)]
  exact posSemidef_lyapunovCayleySolution A Q hA hQ

/-- Positive definite forcing gives a positive definite actual improper Gramian. -/
theorem posDef_lyapunovGramian (A Q : Matrix n n ℂ) (hA : IsHurwitz A)
    (hQ : Q.PosDef) : (lyapunovGramian A Q).PosDef := by
  rw [lyapunovGramian_eq_of_solution A Q _ hA (lyapunovCayleySolution_equation A Q hA)]
  exact posDef_lyapunovCayleySolution A Q hA hQ

end NLAlib
