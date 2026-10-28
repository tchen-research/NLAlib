import NLAlib.Solvers.LeastSquares.FrameDecomposition
import NLAlib.Solvers.LeastSquares.Measurability
import NLAlib.RandomMatrix.Gaussian.Basic.ComplexBlocks
import NLAlib.RandomMatrix.Gaussian.Moments.ComplexConditioning
import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral

/-!
# Exact native complex Gaussian sketch-and-solve expectations

The exact minimum-norm estimator is unbiased at arbitrary input rank. Its
expected residual factor is `1+r/(s-r)`. Both assertions use the full actual
complex Gaussian matrix law. Native orthonormal blocks are independent, and
the proved inverse-Wishart moment supplies integrability along with the value.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem circularComplexGaussian_frameNoise_moments
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {m r s : ℕ}
    {p : Type*} [Fintype p]
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℂ}
    (hΨ : HasLaw Ψ (circularComplexGaussianMatrix (Fin m) (Fin s)) μ)
    (Q : Matrix (Fin m) (Fin r) ℂ) (hQ : HasOrthonormalCols Q) (hrs : r+1≤s)
    (B : Matrix (Fin m) p ℂ) :
    Integrable (fun ω => frobSq (sketchSolveFrameNoise Q (Ψ ω)ᴴ B)) μ ∧
      (∫ ω, frobSq (sketchSolveFrameNoise Q (Ψ ω)ᴴ B) ∂μ)=
        (r:ℝ)/((s:ℝ)-r)*frobSq (projResidual Q B) ∧
      ∀ i j, Integrable (fun ω => sketchSolveFrameNoise Q (Ψ ω)ᴴ B i j) μ ∧
        ∫ ω, sketchSolveFrameNoise Q (Ψ ω)ᴴ B i j ∂μ=0 := by
  obtain ⟨Qp,hQp,hcomp⟩ := exists_unitary_complement Q hQ
  have hQQp := conjTranspose_mul_eq_zero_of_completion hQ hQp hcomp
  have hXY := hasLaw_circularComplexGaussianMatrix_blocks_of_hasLaw hΨ Q Qp hQ hQp hQQp
  let D := Qpᴴ*projResidual Q B
  have hN (ω : Ωs) : sketchSolveFrameNoise Q (Ψ ω)ᴴ B=
      pinvL (Qᴴ*Ψ ω)ᴴ*(Qpᴴ*Ψ ω)ᴴ*D := by
    rw [sketchSolveFrameNoise_eq_completion Q Qp (Ψ ω)ᴴ B hQ hcomp]
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    rfl
  have hD : frobSq D=frobSq (projResidual Q B) := by
    have hh : Qp*D=projResidual Q B := (residual_eq_mul_conjTranspose_mul_residual hQ hcomp B).symm
    rw [← hh,frobSq_mul_left_of_orthonormal hQp.conjTranspose_mul_self]
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_complexGaussian_regression_noise hrs hXY D
  rw [hD] at hv
  simp_rw [hN]
  refine ⟨hi,hv,fun i j => ?_⟩
  exact integrable_and_integral_complexGaussian_regression_noise_entry hrs hXY D i j

private theorem ae_complexGaussian_sketch_full_rank_on_frame
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {m r s : ℕ}
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℂ}
    (hΨ : HasLaw Ψ (circularComplexGaussianMatrix (Fin m) (Fin s)) μ)
    (Q : Matrix (Fin m) (Fin r) ℂ) (hQ : HasOrthonormalCols Q) (hrs : r≤s) :
    ∀ᵐ ω ∂μ, IsUnit (((Ψ ω)ᴴ*Q)ᴴ*((Ψ ω)ᴴ*Q)) := by
  have hX := (hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows Qᴴ
    (by rwa [Matrix.conjTranspose_conjTranspose])).comp hΨ
  have h := ae_isUnit_mul_conjTranspose_of_hasLaw_circularComplexGaussianMatrix hX hrs
  simpa only [Function.comp_apply,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using h

open scoped Matrix.Norms.L2Operator in
/-- Exact residual second moment for the actual native circular complex
Gaussian sketch-and-solve estimator, including rank-zero input.
Source: Epperly--Webber 2026, Theorem 2.1, complex case. -/
theorem integrable_and_integral_frobSq_sub_mul_sketchAndSolve_of_hasLaw_circularComplexGaussianMatrix
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {m n s : ℕ}
    {p : Type*} [Fintype p]
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℂ}
    (hΨ : HasLaw Ψ (circularComplexGaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) p ℂ) (hs : A.rank+1≤s) :
    Integrable (fun ω => frobSq (B-A*sketchAndSolve A (Ψ ω)ᴴ B)) μ ∧
      ∫ ω, frobSq (B-A*sketchAndSolve A (Ψ ω)ᴴ B) ∂μ=
        (1+(A.rank:ℝ)/((s:ℝ)-A.rank))*frobSq ((1-A*moorePenroseInverse A)*B) := by
  have := hΨ.isProbabilityMeasure
  obtain ⟨Q,hQ,hQA,hProj⟩ := exists_orthonormal_range_frame A
  have hRank : A.rank=Fintype.card (Fin A.rank) := by simp only [Fintype.card_fin]
  obtain ⟨hi,hv,hmean⟩ := circularComplexGaussian_frameNoise_moments hΨ Q hQ hs B
  have hE : projResidual Q B=(1-A*moorePenroseInverse A)*B :=
    projResidual_eq_optimalResidual A Q hQ hQA hRank B
  rw [hE] at hv
  have heq : (fun ω => frobSq (B-A*sketchAndSolve A (Ψ ω)ᴴ B)) =ᵐ[μ]
      fun ω => frobSq ((1-A*moorePenroseInverse A)*B)+frobSq (sketchSolveFrameNoise Q (Ψ ω)ᴴ B) := by
    filter_upwards [ae_complexGaussian_sketch_full_rank_on_frame hΨ Q hQ (by omega)] with ω hω
    exact frobSq_residual_sketchAndSolve_eq A Q hQ hQA hRank (Ψ ω)ᴴ B hω
  refine ⟨((integrable_const _).add hi).congr heq.symm,?_⟩
  rw [integral_congr_ae heq,integral_add (integrable_const _) hi,integral_const,
    probReal_univ,one_smul,hv]
  ring

open scoped Matrix.Norms.L2Operator in
/-- Exact complex unbiasedness of the actual minimum-norm Gaussian estimator.
Entries and the full matrix are integrable; the full-rank assumption applies
only to the random sketch restricted to the input range, and is proved.
Source: Epperly--Webber 2026, Theorem 2.1, complex case. -/
theorem integrable_and_integral_sketchAndSolve_of_hasLaw_circularComplexGaussianMatrix
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {m n s : ℕ}
    {p : Type*} [Fintype p] [DecidableEq p]
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℂ}
    (hΨ : HasLaw Ψ (circularComplexGaussianMatrix (Fin m) (Fin s)) μ)
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) p ℂ) (hs : A.rank+1≤s) :
    Integrable (fun ω => sketchAndSolve A (Ψ ω)ᴴ B) μ ∧
      ∫ ω, sketchAndSolve A (Ψ ω)ᴴ B ∂μ=moorePenroseInverse A*B := by
  have := hΨ.isProbabilityMeasure
  obtain ⟨Q,hQ,hQA,hProj⟩ := exists_orthonormal_range_frame A
  have hRank : A.rank=Fintype.card (Fin A.rank) := by simp only [Fintype.card_fin]
  obtain ⟨hNi,hNv,hmean⟩ := circularComplexGaussian_frameNoise_moments hΨ Q hQ hs B
  let R := Qᴴ*A
  let F := fun ω => pinvR R*sketchSolveFrameNoise Q (Ψ ω)ᴴ B
  have hFi (i : Fin n) (j : p) : Integrable (fun ω => F ω i j) μ := by
    change Integrable (fun ω => ∑ k,pinvR R i k*sketchSolveFrameNoise Q (Ψ ω)ᴴ B k j) μ
    exact integrable_finsetSum _ fun k _ => (hmean k j).1.const_mul _
  have hFv (i : Fin n) (j : p) : (∫ ω, F ω i j ∂μ)=0 := by
    change (∫ ω,∑ k,pinvR R i k*sketchSolveFrameNoise Q (Ψ ω)ᴴ B k j ∂μ)=0
    rw [integral_finsetSum _ fun k _ => (hmean k j).1.const_mul _]
    apply Finset.sum_eq_zero
    intro k _
    rw [integral_const_mul,(hmean k j).2,mul_zero]
  have hFM : Integrable F μ := Matrix.integrable_iff_entries.mpr hFi
  have hF0 : (∫ ω,F ω ∂μ)=0 := by
    ext i j
    rw [Matrix.integral_apply hFM i j,hFv]
    rfl
  have heq : (fun ω => sketchAndSolve A (Ψ ω)ᴴ B) =ᵐ[μ] fun ω => moorePenroseInverse A*B+F ω := by
    filter_upwards [ae_complexGaussian_sketch_full_rank_on_frame hΨ Q hQ (by omega)] with ω hω
    exact sketchAndSolve_eq_frame_noise A Q hQ hQA hRank (Ψ ω)ᴴ B hω
  refine ⟨((integrable_const _).add hFM).congr heq.symm,?_⟩
  rw [integral_congr_ae heq,integral_add (integrable_const _) hFM,integral_const,
    probReal_univ,one_smul,hF0,add_zero]

end NLAlib
