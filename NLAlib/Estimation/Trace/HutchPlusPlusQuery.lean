import NLAlib.Estimation.Trace.HutchPlusPlus
import NLAlib.Krylov.QueryModel.SubspaceIteration

/-!
# Matrix-vector realization of Hutch++

Query `Y = AS`, then `AY`, then `AW` for `W = (I-YY⁺)Z`. The output is
`tr(Y⁺AY) + tr(WᵀAW)/r`. Cyclicity identifies the first term with the exact
range trace. This is the native Hutch++ estimate, using `2s+r` vector queries,
without an oracle-dependent choice of basis or assumptions on sketch rank.
Source: the projector formula for Meyer et al. (2021), Algorithm 1.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n s r : Type*} [Fintype n] [DecidableEq n] [Fintype s] [Fintype r]

/-- A block product using one scalar vector query for each member of an arbitrary finite
column index type. -/
private def finiteBlockMultiplyProgram (B : Matrix n s ℝ) :
    QueryProgram (n → ℝ) (n → ℝ) (Matrix n s ℝ) (Fintype.card s) :=
  (QueryProgram.family fun j => B.col ((Fintype.equivFin s).symm j)).map
    (fun h => Matrix.of fun i j => h (Fintype.equivFin s j) i)

omit [DecidableEq n] in
/-- The finite-column query program computes the actual matrix product. -/
private theorem run_finiteBlockMultiplyProgram (A : Matrix n n ℝ) (B : Matrix n s ℝ) :
    (finiteBlockMultiplyProgram B).run A.mulVec = A * B := by
  simp only [finiteBlockMultiplyProgram, QueryProgram.run_map, QueryProgram.run_family,
    Equiv.symm_apply_apply]
  rfl

omit [DecidableEq n] in
/-- The probe estimate is the normalized trace of its compressed quadratic-form matrix. -/
theorem hutchinsonEstimate_eq_trace_mul (A : Matrix n n ℝ) (Z : Matrix n r ℝ) :
    hutchinsonEstimate A Z = (Fintype.card r : ℝ)⁻¹ * (Zᵀ * (A * Z)).trace := by
  simp only [hutchinsonEstimate, Matrix.trace, Matrix.diag, quadForm, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, star_trivial, div_eq_mul_inv]
  exact mul_comm _ _

/-- A query program for the native Hutch++ scalar estimator. The first and second block
products both have the sketch width; the final block has the residual-probe width. -/
def hutchPlusPlusProgram (S : Matrix n s ℝ) (Z : Matrix n r ℝ) :
    QueryProgram (n → ℝ) (n → ℝ) ℝ (Fintype.card r + Fintype.card s + Fintype.card s) :=
  (finiteBlockMultiplyProgram S).bind fun Y =>
    (finiteBlockMultiplyProgram Y).bind fun AY =>
      let W := (1 - rangeProjector Y) * Z
      (finiteBlockMultiplyProgram W).map fun AW =>
        (moorePenroseInverse Y * AY).trace + (Fintype.card r : ℝ)⁻¹ * (Wᵀ * AW).trace

/-- The program returns the existing estimator exactly for every matrix and every sketch,
including zero widths and all rank drops.
atlas: hutchpp (partial) -/
theorem run_hutchPlusPlusProgram (A : Matrix n n ℝ) (S : Matrix n s ℝ) (Z : Matrix n r ℝ) :
    (hutchPlusPlusProgram S Z).run A.mulVec = hutchPlusPlusEstimate A S Z := by
  classical
  simp only [hutchPlusPlusProgram, QueryProgram.run_bind, QueryProgram.run_map,
    run_finiteBlockMultiplyProgram]
  rw [hutchPlusPlusEstimate_eq_projector, hutchinsonEstimate_eq_trace_mul]
  congr 1
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, ← rangeProjector_eq_mul_moorePenroseInverse, Matrix.trace_mul_comm]
  · congr 2
    have hp : (1 - rangeProjector (A * S))ᵀ = 1 - rangeProjector (A * S) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.isHermitian_one.sub (rangeProjector_isHermitian (A * S))).eq
    simp only [Matrix.transpose_mul, hp, hutchPlusPlusResidual, Matrix.mul_assoc]

/-- A single native Hutch++ estimate is computable in exactly `2s+r` matrix-vector
queries. The algorithm is selected before the matrix; it does not inspect matrix entries.
atlas: hutchpp (partial) -/
theorem exists_matvecAlg_hutchPlusPlusEstimate (S : Matrix n s ℝ) (Z : Matrix n r ℝ) :
    ∃ alg : MatvecAlg ℝ n ℝ,
      alg.cost = 2 * Fintype.card s + Fintype.card r ∧
        ∀ A : Matrix n n ℝ, alg.run A = hutchPlusPlusEstimate A S Z := by
  refine ⟨⟨_, hutchPlusPlusProgram S Z⟩, ?_, fun A => run_hutchPlusPlusProgram A S Z⟩
  change Fintype.card r + Fintype.card s + Fintype.card s = _
  omega

end NLAlib
