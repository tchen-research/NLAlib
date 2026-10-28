import NLAlib.Solvers.LeastSquares.SketchAndSolve
import NLAlib.LowRank.Nystrom.RawNystromBridge
import NLAlib.Matrix.Spectral.ThinSVD
import NLAlib.Matrix.Basic.MoorePenroseTransformations

/-!
# Native real and complex sketch-and-solve frame decomposition

These deterministic identities use the actual Moore--Penrose estimator at
arbitrary input rank. A fixed orthonormal range frame isolates all sketch
randomness in one block-noise matrix. They are shared by Gaussian and Haar
moment calculations, and include rank-zero and empty matrix shapes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p q s r : Type*} [Fintype m] [Fintype n] [Fintype q] [Fintype s]

/-- Every real or complex matrix has an exact orthonormal range frame with
`rank A` columns. The returned projector is its native Moore--Penrose projector. -/
theorem exists_orthonormal_range_frame [DecidableEq n] (A : Matrix m n 𝕜) :
    ∃ Q : Matrix m (Fin A.rank) 𝕜, HasOrthonormalCols Q ∧
      Q*(Qᴴ*A)=A ∧ A*moorePenroseInverse A=Q*Qᴴ := by
  obtain ⟨U,V,h⟩ := exists_isThinSVD A
  refine ⟨U,h.left_orth,?_,h.mul_moorePenroseInverse_eq⟩
  rw [← Matrix.mul_assoc,← h.mul_moorePenroseInverse_eq,mul_moorePenroseInverse_mul]

/-- Native core-noise matrix for an arbitrary sketch `S` and range frame `Q`. -/
def sketchSolveFrameNoise [DecidableEq q] (Q : Matrix m q 𝕜) (S : Matrix s m 𝕜)
    (B : Matrix m p 𝕜) : Matrix q p 𝕜 := pinvL (S*Q)*(S*projResidual Q B)

/-- The fitted frame coordinates split into the true projected right-hand
side and its exact sketch-induced noise. -/
theorem pinvL_sketch_mul_eq_frame_add_noise [DecidableEq q]
    (Q : Matrix m q 𝕜) (S : Matrix s m 𝕜) (B : Matrix m p 𝕜)
    (hSQ : IsUnit ((S*Q)ᴴ*(S*Q))) :
    pinvL (S*Q)*(S*B)=Qᴴ*B+sketchSolveFrameNoise Q S B := by
  have hB : S*B=(S*Q)*(Qᴴ*B)+S*projResidual Q B := by
    calc
      _ = S*(Q*(Qᴴ*B)+projResidual Q B) := by rw [mul_conjTranspose_mul_add_residual]
      _ = _ := by rw [Matrix.mul_add,← Matrix.mul_assoc]
  rw [hB,Matrix.mul_add,← Matrix.mul_assoc,pinvL_mul hSQ,Matrix.one_mul]
  rfl

section FullFrame
variable [DecidableEq q]
variable (A : Matrix m n 𝕜) (Q : Matrix m q 𝕜)
variable (hQ : HasOrthonormalCols Q) (hQA : Q*(Qᴴ*A)=A)
variable (hRank : A.rank=Fintype.card q)
include hQ hQA hRank

/-- The original pseudoinverse factors through any exact full range frame. -/
theorem moorePenroseInverse_eq_pinvR_frame_mul_conjTranspose :
    moorePenroseInverse A=pinvR (Qᴴ*A)*Qᴴ := by
  have hR := isUnit_rowGram_of_frame_factorization Q A hQA hRank
  have hQG : IsUnit (Qᴴ*Q) := by rw [hQ.conjTranspose_mul_self]; exact isUnit_one
  have h := moorePenroseInverse_mul_eq_pinvR_mul_pinvL Q (Qᴴ*A) hQG hR
  have hP : pinvL Q=Qᴴ := by rw [pinvL,hQ.conjTranspose_mul_self,inv_one,Matrix.one_mul]
  rwa [hQA,hP] at h

/-- Any exact full range frame has precisely the native Moore--Penrose
range projector of the input. -/
theorem mul_moorePenroseInverse_eq_frame_projector : A*moorePenroseInverse A=Q*Qᴴ := by
  rw [moorePenroseInverse_eq_pinvR_frame_mul_conjTranspose A Q hQ hQA hRank]
  calc
    _ = Q*((Qᴴ*A)*pinvR (Qᴴ*A))*Qᴴ := by
      conv_lhs => lhs; rw [← hQA]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [mul_pinvR (isUnit_rowGram_of_frame_factorization Q A hQA hRank),Matrix.mul_one]

/-- Projection residuals in the fixed frame are exactly the original
least-squares optimal residuals. -/
theorem projResidual_eq_optimalResidual [DecidableEq m] (B : Matrix m p 𝕜) :
    projResidual Q B=(1-A*moorePenroseInverse A)*B := by
  rw [mul_moorePenroseInverse_eq_frame_projector A Q hQ hQA hRank]
  simp only [projResidual,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc]

/-- The actual minimum-norm sketch-and-solve estimator splits into its true
minimum-norm solution and an explicit frame-noise term. -/
theorem sketchAndSolve_eq_frame_noise (S : Matrix s m 𝕜) (B : Matrix m p 𝕜)
    (hSQ : IsUnit ((S*Q)ᴴ*(S*Q))) :
    sketchAndSolve A S B=moorePenroseInverse A*B+
      pinvR (Qᴴ*A)*sketchSolveFrameNoise Q S B := by
  have hR := isUnit_rowGram_of_frame_factorization Q A hQA hRank
  have hFactor : S*A=(S*Q)*(Qᴴ*A) := by
    calc
      _ = S*(Q*(Qᴴ*A)) := congrArg (S*·) hQA.symm
      _ = _ := (Matrix.mul_assoc _ _ _).symm
  rw [sketchAndSolve,hFactor,moorePenroseInverse_mul_eq_pinvR_mul_pinvL _ _ hSQ hR,
    Matrix.mul_assoc,pinvL_sketch_mul_eq_frame_add_noise Q S B hSQ,Matrix.mul_add,
    moorePenroseInverse_eq_pinvR_frame_mul_conjTranspose A Q hQ hQA hRank,
    Matrix.mul_assoc]

/-- The native fitted values have the same exact frame-noise decomposition. -/
theorem fitted_sketchAndSolve_eq_frame_noise (S : Matrix s m 𝕜) (B : Matrix m p 𝕜)
    (hSQ : IsUnit ((S*Q)ᴴ*(S*Q))) :
    A*sketchAndSolve A S B=Q*(Qᴴ*B+sketchSolveFrameNoise Q S B) := by
  rw [sketchAndSolve_eq_frame_noise A Q hQ hQA hRank S B hSQ,Matrix.mul_add]
  have hR := mul_pinvR (isUnit_rowGram_of_frame_factorization Q A hQA hRank)
  have hAP : A*pinvR (Qᴴ*A)=Q := by
    calc
      _ = Q*((Qᴴ*A)*pinvR (Qᴴ*A)) := by
        conv_lhs => lhs; rw [← hQA]
        exact Matrix.mul_assoc _ _ _
      _ = Q := by rw [hR,Matrix.mul_one]
  rw [← Matrix.mul_assoc, mul_moorePenroseInverse_eq_frame_projector A Q hQ hQA hRank,
    Matrix.mul_assoc, ← Matrix.mul_assoc A, hAP, Matrix.mul_add]

variable [Fintype p]

open scoped Matrix.Norms.L2Operator in
/-- The native squared residual is its optimal squared residual plus the
exact squared Frobenius norm of the frame-noise matrix. -/
theorem frobSq_residual_sketchAndSolve_eq [DecidableEq m] (S : Matrix s m 𝕜) (B : Matrix m p 𝕜)
    (hSQ : IsUnit ((S*Q)ᴴ*(S*Q))) :
    frobSq (B-A*sketchAndSolve A S B)=
      frobSq ((1-A*moorePenroseInverse A)*B)+frobSq (sketchSolveFrameNoise Q S B) := by
  rw [fitted_sketchAndSolve_eq_frame_noise A Q hQ hQA hRank S B hSQ,
    frobSq_sub_mul_eq hQ]
  have hsub : Qᴴ*B-(Qᴴ*B+sketchSolveFrameNoise Q S B) = -sketchSolveFrameNoise Q S B := by abel
  rw [hsub,frobSq_neg,projResidual_eq_optimalResidual A Q hQ hQA hRank]

end FullFrame

/-- An orthonormal complement expresses the native frame noise entirely in
the top and bottom sketch blocks. -/
theorem sketchSolveFrameNoise_eq_completion [Fintype r] [DecidableEq q] [DecidableEq m]
    (Q : Matrix m q 𝕜) (Qp : Matrix m r 𝕜) (S : Matrix s m 𝕜) (B : Matrix m p 𝕜)
    (hQ : HasOrthonormalCols Q) (hcomp : Q*Qᴴ+Qp*Qpᴴ=1) :
    sketchSolveFrameNoise Q S B=pinvL (S*Q)*(S*Qp)*(Qpᴴ*projResidual Q B) := by
  unfold sketchSolveFrameNoise
  conv_lhs => rw [residual_eq_mul_conjTranspose_mul_residual hQ hcomp B]
  simp only [Matrix.mul_assoc]

/-- Nonzero global scaling of the sketch leaves the actual minimum-norm
sketch-and-solve estimator unchanged. -/
theorem sketchAndSolve_smul_sketch
    (A : Matrix m n 𝕜) (S : Matrix s m 𝕜) (B : Matrix m p 𝕜) {c : 𝕜} (hc : c≠0) :
    sketchAndSolve A (c•S) B=sketchAndSolve A S B := by
  unfold sketchAndSolve
  rw [Matrix.smul_mul,moorePenroseInverse_smul,Matrix.smul_mul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,inv_mul_cancel₀ hc,one_smul]

/-- Rank-zero input has exactly zero sketched solution and its original
right-hand side as residual, for every sketch and every width. -/
theorem sketchAndSolve_zero (S : Matrix s m 𝕜) (B : Matrix m p 𝕜) :
    sketchAndSolve (0 : Matrix m n 𝕜) S B=0 := by simp [sketchAndSolve]

end NLAlib
