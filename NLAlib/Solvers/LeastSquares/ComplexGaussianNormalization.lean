import NLAlib.Solvers.LeastSquares.ComplexGaussianMoments

/-!
# Unit-variance complex Gaussian sketch-and-solve

The paper's standard complex entry is `(g+i h)/sqrt 2`. Rescaling its matrix
by `sqrt 2` gives the already proved native circular law. The actual
Moore--Penrose estimator is invariant under that nonzero global sketch
scaling, so its expectation and exact residual factor are identical.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem hasLaw_sqrtTwo_smul_complexGaussianMatrix {m n : Type*} [Fintype m] [Fintype n] :
    HasLaw (fun G : Matrix m n ℂ => Real.sqrt 2 • G) (circularComplexGaussianMatrix m n)
      (complexGaussianMatrix m n) := by
  refine ⟨(by fun_prop : Measurable _).aemeasurable,?_⟩
  have h2 : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [complexGaussianMatrix,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun G : Matrix m n ℂ => Real.sqrt 2 • G) ∘
      (fun G => (Real.sqrt 2)⁻¹ • G)=id := by
    funext G
    simp only [Function.comp_apply,smul_smul,mul_inv_cancel₀ h2,one_smul,id_eq]
  rw [he,Measure.map_id]

private theorem sketchAndSolve_sqrtTwo_smul_adjoint {m n p s : Type*}
    [Fintype m] [Fintype n] [Fintype s]
    (A : Matrix m n ℂ) (G : Matrix m s ℂ) (B : Matrix m p ℂ) :
    sketchAndSolve A (Real.sqrt 2 • G)ᴴ B=sketchAndSolve A Gᴴ B := by
  have he : Real.sqrt 2 • G=(Real.sqrt 2 : ℂ)•G := by
    ext i j
    simp only [Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,smul_eq_mul]
    rfl
  rw [he,Matrix.conjTranspose_smul]
  apply sketchAndSolve_smul_sketch A Gᴴ B
  apply star_ne_zero.mpr
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))

open scoped Matrix.Norms.L2Operator in
/-- The actual minimum-norm estimator is unbiased for the standard complex
Gaussian law with entries `(g+i h)/sqrt 2`, including deficient input matrices.
Source: Epperly--Webber 2026, Theorem 2.1, complex Gaussian case.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_sketchAndSolve_of_hasLaw_complexGaussianMatrix
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℂ}
    (hΨ : HasLaw Ψ (complexGaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) p ℂ) (hs : A.rank+1≤s) :
    Integrable (fun ω => sketchAndSolve A (Ψ ω)ᴴ B) μ ∧
      ∫ ω, sketchAndSolve A (Ψ ω)ᴴ B ∂μ=moorePenroseInverse A*B := by
  have hU : HasLaw (fun ω => Real.sqrt 2 • Ψ ω)
      (circularComplexGaussianMatrix (Fin m) (Fin s)) μ :=
    hasLaw_sqrtTwo_smul_complexGaussianMatrix.comp hΨ
  simpa only [sketchAndSolve_sqrtTwo_smul_adjoint] using
    integrable_and_integral_sketchAndSolve_of_hasLaw_circularComplexGaussianMatrix hU A B hs

open scoped Matrix.Norms.L2Operator in
/-- Exact native residual expectation for standard complex Gaussian sketches.
The denominator is `s-r`, with no real-field offset. Rank zero is included.
Source: Epperly--Webber 2026, Theorem 2.1, complex Gaussian case.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_sub_mul_sketchAndSolve_of_hasLaw_complexGaussianMatrix
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {m n s : ℕ}
    {p : Type*} [Fintype p]
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℂ}
    (hΨ : HasLaw Ψ (complexGaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) p ℂ) (hs : A.rank+1≤s) :
    Integrable (fun ω => frobSq (B-A*sketchAndSolve A (Ψ ω)ᴴ B)) μ ∧
      ∫ ω, frobSq (B-A*sketchAndSolve A (Ψ ω)ᴴ B) ∂μ=
        (1+(A.rank:ℝ)/((s:ℝ)-A.rank))*frobSq ((1-A*moorePenroseInverse A)*B) := by
  have hU : HasLaw (fun ω => Real.sqrt 2 • Ψ ω)
      (circularComplexGaussianMatrix (Fin m) (Fin s)) μ :=
    hasLaw_sqrtTwo_smul_complexGaussianMatrix.comp hΨ
  simpa only [sketchAndSolve_sqrtTwo_smul_adjoint] using
    integrable_and_integral_frobSq_sub_mul_sketchAndSolve_of_hasLaw_circularComplexGaussianMatrix hU A B hs

end NLAlib
