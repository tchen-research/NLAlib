import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Noncommutative exponential differentiation

The exact Duhamel identity follows by differentiating scalar multiples
of fixed matrices. Analyticity of the exponential and continuity of the
parametric integral identify its full Fréchet derivative, without any
commutation or normality assumption. Higham, Functions of Matrices;
toolkit derivations, formula (F10).
-/

noncomputable section
open Matrix Filter MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

private local instance : NormedAlgebra ℝ (Matrix n n 𝕜) := normedAlgebraRealMatrix
private local instance : NormedAlgebra ℚ (Matrix n n 𝕜) := NormedAlgebra.restrictScalars ℚ ℝ _

/-- The matrix exponential is Fréchet differentiable on its full algebra,
over either the real or complex scalar field. -/
theorem hasFDerivAt_matrixExp (A : Matrix n n 𝕜) :
    HasFDerivAt matrixExp (fderiv 𝕜 matrixExp A) A := by
  exact (NormedSpace.exp_analytic (𝕂 := 𝕜) A).differentiableAt.hasFDerivAt

/-- The exact Duhamel difference formula for arbitrary square matrices. -/
theorem matrixExp_sub_matrixExp_eq_integral (A B : Matrix n n 𝕜) :
    matrixExp A - matrixExp B =
      ∫ t : ℝ in 0..1, matrixExp ((1-t) • A) * (A-B) * matrixExp (t • B) := by
  let F (t : ℝ) := matrixExp ((1-t) • A) * matrixExp (t • B)
  let G (t : ℝ) := matrixExp ((1-t) • A) * (A-B) * matrixExp (t • B)
  have hder (t : ℝ) : HasDerivAt F (-G t) t := by
    have hleft := (hasDerivAt_exp_smul_const A (1-t)).scomp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    have hright := hasDerivAt_exp_smul_const' B t
    convert! hleft.mul hright using 1
    change -G t = _
    simp only [G, neg_smul, one_smul, zero_sub]
    noncomm_ring
  have hcont : Continuous G := by
    dsimp [G, matrixExp]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hder t) (hcont.neg.intervalIntegrable 0 1)
  simp only [F, zero_smul, sub_zero, one_smul, sub_self, matrixExp,
    NormedSpace.exp_zero, one_mul, mul_one, intervalIntegral.integral_neg] at hi
  change NormedSpace.exp A - NormedSpace.exp B = _
  exact neg_injective (by simpa only [neg_sub] using hi.symm)

/-- The full Fréchet derivative of the matrix exponential is the
noncommutative insertion integral. Both real and complex matrices and
empty dimensions are covered.
atlas: matrix-exponential-frechet-integral -/
theorem fderiv_matrixExp_apply (A E : Matrix n n 𝕜) :
    fderiv 𝕜 matrixExp A E =
      ∫ s : ℝ in 0..1, matrixExp ((1-s) • A) * E * matrixExp (s • A) := by
  let J (t : ℝ) := ∫ s : ℝ in 0..1,
    matrixExp ((1-s) • (A + t • E)) * E * matrixExp (s • A)
  have hc : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (a₀ := 0) (b₀ := 1)
    dsimp [Function.uncurry, matrixExp]
    fun_prop
  have hpath : HasDerivAt (fun t : ℝ => A + t • E) E 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const E).const_add A
  have hd : HasDerivAt (fun t : ℝ => matrixExp (A + t • E))
      (fderiv 𝕜 matrixExp A E) 0 := by
    exact ((hasFDerivAt_matrixExp A).restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hpath (by simp)
  have heq : (fun t : ℝ => t⁻¹ • (matrixExp (A + (0+t) • E) - matrixExp (A + (0 : ℝ) • E)))
      =ᶠ[𝓝[>] 0] J := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [zero_add, zero_smul, add_zero]
    rw [matrixExp_sub_matrixExp_eq_integral]
    have he : A + t • E - A = t • E := by abel
    rw [he]
    have hint : (∫ s : ℝ in 0..1, matrixExp ((1-s) • (A + t • E)) *
        (t • E) * matrixExp (s • A)) = t • J t := by
      simp only [J, Matrix.mul_smul, Matrix.smul_mul, intervalIntegral.integral_smul]
    rw [hint, inv_smul_smul₀ ht0]
  have hj : Tendsto J (𝓝[>] 0) (𝓝 (J 0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hd.tendsto_slope_zero_right.congr' heq
  have he := tendsto_nhds_unique hlim hj
  simpa [J] using he

end NLAlib
