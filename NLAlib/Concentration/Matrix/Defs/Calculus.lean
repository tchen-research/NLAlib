import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Defs.Dilation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Shared calculus for complex matrices

Small facts used throughout the matrix concentration files, collected here so that each has one
copy:

* spectral calculus of a Hermitian matrix: `matrixExp_smul_eq_cfc`, `traceExp_smul_eq_sum`,
  `le_of_mem_spectrum_of_lambdaMax_le`, `abs_le_norm_of_mem_spectrum`;
* reindexing: `reindexStarAlgEquiv`, `norm_reindex`, `lambdaMax_reindex`, `integral_reindex`;
* the Hermitian dilation and block-diagonal matrices: `dilationLinearMap`, `dilation_sq`,
  `fromBlocks₁₁CLM`, `fromBlocks₂₂CLM`, `integral_fromBlocks_diag`.

Atlas: support for `matrix-laplace`, `matrix-gaussian-series`, `matrix-chernoff`,
`matrix-bernstein`, `hermitian-dilation`, `intrinsic-dimension`.

Ported from the Prove2me missions *An Introduction to Matrix Concentration Inequalities, Ch 3–8*
(Tropp 2015), where each of these appeared as a private helper in several files.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace NLAlib

section Spectral

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- For Hermitian `A`, `matrixExp (s • A)` is the functional calculus of `x ↦ exp (s x)` at `A`.
Tropp 2015, §2.1.11. -/
theorem matrixExp_smul_eq_cfc (A : Matrix d d ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

/-- For Hermitian `A`, `traceExp (θ • A) = ∑ i, exp (θ λᵢ)` over the eigenvalues of `A`. Tropp
2015, §3.1. -/
theorem traceExp_smul_eq_sum (A : Matrix d d ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

/-- For Hermitian `A` with `lambdaMax A ≤ L`, every real spectral value of `A` is at most `L`.
Tropp 2015, §2.1. -/
theorem le_of_mem_spectrum_of_lambdaMax_le (A : Matrix d d ℂ) (hA : A.IsHermitian) {L : ℝ}
    (hb : lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact (le_csSup hfin.bddAbove hx).trans hb

/-- A real spectral value of a square complex matrix is bounded in absolute value by its ℓ₂
operator norm. Tropp 2015, §2.1. -/
theorem abs_le_norm_of_mem_spectrum [Nonempty d] (B : Matrix d d ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ ℂ x ∈ spectrum ℂ B := (spectrum.algebraMap_mem_iff ℂ).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

end Spectral

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- `Matrix.reindex e e` as a `⋆`-algebra equivalence of square complex matrices over `ℂ`. -/
def reindexStarAlgEquiv (e : ι ≃ κ) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; rfl
    map_smul' := by intro r A; rfl }

/-- Reindexing preserves the ℓ₂ operator norm. -/
theorem norm_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖Matrix.reindex e e A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (reindexStarAlgEquiv e) A

/-- Reindexing preserves the real spectrum, hence `lambdaMax`. -/
theorem lambdaMax_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    lambdaMax (Matrix.reindex e e A) = lambdaMax A := by
  have h := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ e) A
  rw [Matrix.coe_reindexAlgEquiv] at h
  unfold lambdaMax
  rw [h]

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

/-- The Hermitian dilation as a real-linear map. Tropp 2015, Def. 2.1.5. Atlas:
`hermitian-dilation`. -/
def dilationLinearMap (m n : Type*) : Matrix m n ℂ →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun := dilation
  map_add' X Y := by
    simp [dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add]
  map_smul' c X := by
    simp [dilation, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

/-- `dilationLinearMap` applies `dilation`. -/
@[simp]
theorem dilationLinearMap_apply {m n : Type*} (X : Matrix m n ℂ) :
    dilationLinearMap m n X = dilation X := rfl

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The square of the Hermitian dilation is block diagonal: `(dilation X)² =
fromBlocks (X Xᴴ) 0 0 (Xᴴ X)`. Tropp 2015, eq. (2.1.28). Atlas: `hermitian-dilation`. -/
theorem dilation_sq (X : Matrix m n ℂ) :
    dilation X ^ 2 = fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
  simp [dilation, sq, fromBlocks_multiply]

variable (n) in
/-- The upper-left block inclusion `P ↦ fromBlocks P 0 0 0` as a continuous linear map. -/
def fromBlocks₁₁CLM : Matrix m m ℂ →L[ℂ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => fromBlocks P 0 0 0
      map_add' := fun P P' => by rw [fromBlocks_add]; simp
      map_smul' := fun c P => by rw [fromBlocks_smul]; simp }

variable (m) in
/-- The lower-right block inclusion `Q ↦ fromBlocks 0 0 0 Q` as a continuous linear map. -/
def fromBlocks₂₂CLM : Matrix n n ℂ →L[ℂ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Q => fromBlocks 0 0 0 Q
      map_add' := fun Q Q' => by rw [fromBlocks_add]; simp
      map_smul' := fun c Q => by rw [fromBlocks_smul]; simp }

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `fromBlocks₁₁CLM` puts its argument in the upper-left block. -/
@[simp]
theorem fromBlocks₁₁CLM_apply (P : Matrix m m ℂ) :
    fromBlocks₁₁CLM n P = fromBlocks P 0 0 0 := rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- `fromBlocks₂₂CLM` puts its argument in the lower-right block. -/
@[simp]
theorem fromBlocks₂₂CLM_apply (Q : Matrix n n ℂ) :
    fromBlocks₂₂CLM m Q = fromBlocks 0 0 0 Q := rfl

/-- The Bochner integral of a random block-diagonal matrix is block diagonal with the integrated
blocks. -/
theorem integral_fromBlocks_diag {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Ω → Matrix m m ℂ) (Q : Ω → Matrix n n ℂ) (hP : Integrable P μ) (hQ : Integrable Q μ) :
    ∫ ω, fromBlocks (P ω) 0 0 (Q ω) ∂μ = fromBlocks (∫ ω, P ω ∂μ) 0 0 (∫ ω, Q ω ∂μ) := by
  have hsplit : ∀ (A : Matrix m m ℂ) (B : Matrix n n ℂ),
      fromBlocks A 0 0 B = fromBlocks₁₁CLM n A + fromBlocks₂₂CLM m B := by
    intro A B
    rw [fromBlocks₁₁CLM_apply, fromBlocks₂₂CLM_apply, fromBlocks_add]; simp
  simp_rw [hsplit]
  rw [integral_add ((fromBlocks₁₁CLM n).integrable_comp hP)
      ((fromBlocks₂₂CLM m).integrable_comp hQ),
    ContinuousLinearMap.integral_comp_comm _ hP, ContinuousLinearMap.integral_comp_comm _ hQ]

end Blocks

end NLAlib
