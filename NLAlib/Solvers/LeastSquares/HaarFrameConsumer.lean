import NLAlib.Solvers.LeastSquares.FrameDecomposition
import NLAlib.Solvers.LeastSquares.HaarBlockMoments
import NLAlib.Matrix.Subspaces.OrthogonalComplement
import NLAlib.ForMathlib.MeasureTheory.MatrixMultiplicationIntegral

/-!
# Actual Haar sketch-and-solve from native top-Gram moments

These deterministic/probabilistic consumer bridges keep the actual minimum-norm
Moore--Penrose estimator. The following real and complex specializations supply
the inverse top-Gram moments from the native Haar probability law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped Matrix
namespace NLAlib
variable {K : Type*} [RCLike K] {n d p ell r q : ℕ}

open scoped Matrix.Norms.L2Operator in
private local instance {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b] :
    NormedSpace ℝ (Matrix a b K) := NormedSpace.restrictScalars ℝ K (Matrix a b K)

private theorem sketchSolveFrameNoise_eq_haarBlockNoise
    (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (B : Matrix (Fin n) (Fin p) K) (Ω : UnitaryStiefel K n ell)
    (hU : HasOrthonormalCols U) (hcomp : U*Uᴴ+V*Vᴴ=1) :
    sketchSolveFrameNoise U Ω.valᴴ B=haarBlockNoise U V Ω*(Vᴴ*projResidual U B) := by
  rw [sketchSolveFrameNoise_eq_completion U V Ω.valᴴ B hU hcomp]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The native Haar estimator has the correct integrable matrix mean whenever
the actual Haar top Gram has its proved finite inverse-trace moment. -/
theorem integrable_and_integral_sketchAndSolve_haar_of_frame
    (A : Matrix (Fin n) (Fin d) K) (B : Matrix (Fin n) (Fin p) K)
    (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1)
    (hUA : U*(Uᴴ*A)=A) (hRank : A.rank=r) (helln : ell≤n)
    (hfull : ∀ᵐ Ω ∂unitaryHaarFrameLaw K n ell helln,IsUnit (unitaryFrameTopGram K U Ω))
    (htrace : Integrable (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (fun Ω => sketchAndSolve A Ω.valᴴ B) (unitaryHaarFrameLaw K n ell helln) ∧
      (∫ Ω,sketchAndSolve A Ω.valᴴ B ∂unitaryHaarFrameLaw K n ell helln)=moorePenroseInverse A*B := by
  obtain ⟨hZ,hZmean⟩ := integrable_and_integral_haarBlockNoise helln U V hU hV hUV hcomp hfull htrace
  obtain ⟨hN,hNmean⟩ := integrable_and_integral_matrix_sandwich
    (pinvR (Uᴴ*A)) (Vᴴ*projResidual U B) hZ
  rw [hZmean,Matrix.mul_zero,Matrix.zero_mul] at hNmean
  have he : (fun Ω => sketchAndSolve A Ω.valᴴ B) =ᵐ[unitaryHaarFrameLaw K n ell helln]
      (fun Ω => moorePenroseInverse A*B+pinvR (Uᴴ*A)*haarBlockNoise U V Ω*(Vᴴ*projResidual U B)) := by
    filter_upwards [hfull] with Ω hΩ
    have hSQ : IsUnit ((Ω.valᴴ*U)ᴴ*(Ω.valᴴ*U)) := by
      simpa only [unitaryFrameTopGram,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using hΩ
    rw [sketchAndSolve_eq_frame_noise A U hU hUA (by simpa using hRank) Ω.valᴴ B hSQ,
      sketchSolveFrameNoise_eq_haarBlockNoise U V B Ω hU hcomp,Matrix.mul_assoc]
  have hconst := integrable_const (μ := unitaryHaarFrameLaw K n ell helln) (moorePenroseInverse A*B)
  refine ⟨(hconst.add hN).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hconst hN,hNmean,add_zero,integral_const,
    probReal_univ]
  ext i j
  change ((1 : ℝ) : K) * ((moorePenroseInverse A*B) i j) = _
  simp only [RCLike.ofReal_one, one_mul]

/-- The native residual expectation is its optimal squared residual times the
exact finite-dimensional factor supplied by the actual Haar inverse top Gram. -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_of_frame
    (A : Matrix (Fin n) (Fin d) K) (B : Matrix (Fin n) (Fin p) K)
    (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1)
    (hUA : U*(Uᴴ*A)=A) (hRank : A.rank=r) (helln : ell≤n) (hq : 0<q)
    (hfull : ∀ᵐ Ω ∂unitaryHaarFrameLaw K n ell helln,IsUnit (unitaryFrameTopGram K U Ω))
    (htrace : Integrable (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (fun Ω => frobSq (B-A*sketchAndSolve A Ω.valᴴ B)) (unitaryHaarFrameLaw K n ell helln) ∧
      (∫ Ω,frobSq (B-A*sketchAndSolve A Ω.valᴴ B) ∂unitaryHaarFrameLaw K n ell helln)=
        (1+((∫ Ω,RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace
          ∂unitaryHaarFrameLaw K n ell helln)-r)/q)*frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨hN,hNval⟩ := integrable_and_integral_frobSq_haarBlockNoise_mul
    helln hq U V hU hV hUV hcomp hfull htrace (Vᴴ*projResidual U B)
  have hD : frobSq (Vᴴ*projResidual U B)=frobSq ((1-A*moorePenroseInverse A)*B) := by
    calc
      _ = frobSq (V*(Vᴴ*projResidual U B)) :=
        (frobSq_mul_left_of_orthonormal hV (Vᴴ*projResidual U B)).symm
      _ = frobSq (projResidual U B) := congrArg frobSq
        (residual_eq_mul_conjTranspose_mul_residual hU hcomp B).symm
      _ = _ := congrArg frobSq (projResidual_eq_optimalResidual A U hU hUA (by simpa using hRank) B)
  have he : (fun Ω => frobSq (B-A*sketchAndSolve A Ω.valᴴ B)) =ᵐ[unitaryHaarFrameLaw K n ell helln]
      (fun Ω => frobSq ((1-A*moorePenroseInverse A)*B)+frobSq (haarBlockNoise U V Ω*(Vᴴ*projResidual U B))) := by
    filter_upwards [hfull] with Ω hΩ
    have hSQ : IsUnit ((Ω.valᴴ*U)ᴴ*(Ω.valᴴ*U)) := by
      simpa only [unitaryFrameTopGram,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using hΩ
    rw [frobSq_residual_sketchAndSolve_eq A U hU hUA (by simpa using hRank) Ω.valᴴ B hSQ,
      sketchSolveFrameNoise_eq_haarBlockNoise U V B Ω hU hcomp]
  have hconst := integrable_const (μ := unitaryHaarFrameLaw K n ell helln)
    (frobSq ((1-A*moorePenroseInverse A)*B))
  refine ⟨(hconst.add hN).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hconst hN,hNval,hD,integral_const,
    probReal_univ,one_smul]
  ring

end NLAlib
