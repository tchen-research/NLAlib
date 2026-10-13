import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.Basic

/-!
# Integrals of reindexed and block-diagonal random matrices

`integral_reindex` and `integral_fromBlocks_diag`: the Bochner integral commutes with
`Matrix.reindex` and with block-diagonal assembly. The deterministic calculus they rest on is
`NLAlib.Matrix.Functions.HermitianCalculus`.

Atlas: support for `matrix-laplace`, `matrix-bernstein`, `hermitian-dilation`. Source: Tropp 2015,
*An Introduction to Matrix Concentration Inequalities*, §§2.1, 4.6.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace NLAlib

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

open scoped Matrix.Norms.L2Operator in
/-- The Bochner integral of a random square matrix commutes with reindexing. -/
theorem integral_reindex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (e : ι ≃ κ)
    (X : Ω → Matrix ι ι ℂ) :
    ∫ ω, Matrix.reindex e e (X ω) ∂μ = Matrix.reindex e e (∫ ω, X ω ∂μ) := by
  let L : Matrix ι ι ℂ ≃L[ℝ] Matrix κ κ ℂ :=
    (Matrix.reindexLinearEquiv ℝ ℂ e e).toContinuousLinearEquiv
  exact L.integral_comp_comm X

end Reindex

section Blocks

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Block-diagonal assembly `(P, Q) ↦ fromBlocks P 0 0 Q` as a real continuous linear map. -/
private def fromBlocksDiagCLM :
    (Matrix m m ℂ × Matrix n n ℂ) →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => fromBlocks x.1 0 0 x.2
      map_add' := fun x y => by rw [fromBlocks_add]; simp
      map_smul' := fun c x => by rw [fromBlocks_smul]; simp }

open scoped Matrix.Norms.L2Operator in
/-- The Bochner integral of a pair is the pair of integrals. -/
private lemma integral_prodMk {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Ω → Matrix m m ℂ) (Q : Ω → Matrix n n ℂ) (hP : Integrable P μ) (hQ : Integrable Q μ) :
    ∫ ω, (P ω, Q ω) ∂μ = (∫ ω, P ω ∂μ, ∫ ω, Q ω ∂μ) := by
  have h := Integrable.prodMk hP hQ
  refine Prod.ext ?_ ?_
  · exact ((ContinuousLinearMap.fst ℝ (Matrix m m ℂ) (Matrix n n ℂ)).integral_comp_comm h).symm
  · exact ((ContinuousLinearMap.snd ℝ (Matrix m m ℂ) (Matrix n n ℂ)).integral_comp_comm h).symm

open scoped Matrix.Norms.L2Operator in
/-- The Bochner integral of a random block-diagonal matrix is block diagonal with the integrated
blocks. -/
theorem integral_fromBlocks_diag {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Ω → Matrix m m ℂ) (Q : Ω → Matrix n n ℂ) (hP : Integrable P μ) (hQ : Integrable Q μ) :
    ∫ ω, fromBlocks (P ω) 0 0 (Q ω) ∂μ = fromBlocks (∫ ω, P ω ∂μ) 0 0 (∫ ω, Q ω ∂μ) := by
  have h := fromBlocksDiagCLM.integral_comp_comm (Integrable.prodMk hP hQ)
  rw [integral_prodMk μ P Q hP hQ] at h
  exact h

end Blocks

section EigenProjections

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- For a Hermitian `A` and a scalar random variable `s` with all exponential moments,
`matrixExp (s • A)` is integrable and `𝔼 matrixExp (s • A) = cfc (mgf s μ) A`.
Tropp 2015, §4.6 (helper for Lemmas 4.6.2–4.6.3). -/
theorem integrable_and_integral_matrixExp_smul_eq_cfc_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix d d ℂ) (hA : A.IsHermitian) (s : Ω → ℝ)
    (hs : ∀ t, Integrable (fun ω => Real.exp (t * s ω)) μ) :
    Integrable (fun ω => matrixExp (s ω • A)) μ ∧
    ∫ ω, matrixExp (s ω • A) ∂μ = cfc (fun t => mgf s μ t) A := by
  have h : (fun ω => matrixExp (s ω • A)) =
      fun ω => ∑ i, Real.exp (hA.eigenvalues i * s ω) • eigenvectorProjector hA i := by
    funext ω
    rw [matrixExp_smul_eq_cfc A hA, cfc_eq_sum_smul_eigenvectorProjector hA]
    simp only [mul_comm]
  rw [h]
  refine ⟨integrable_finsetSum _ (fun i _ => (hs _).smul_const _), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hs _).smul_const _), cfc_eq_sum_smul_eigenvectorProjector hA]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul_const]
  rfl

end EigenProjections

end NLAlib
