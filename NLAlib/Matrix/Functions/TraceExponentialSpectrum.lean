import NLAlib.Matrix.Functions.ExpLog
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Trace exponentials from a complete family of distinct eigenvalues

The exterior eigenvalue branches in Stahl's representation enumerate all the
eigenvalues of a matrix pencil outside a sufficiently large disk. This file
converts that spectral fact into the boundary trace identity, using an eigenvector basis and similarity invariance of the matrix exponential.
Source: Stahl 2013, §§3–4; infrastructure toward `trace-exponential-stahl`.
-/

noncomputable section

open Matrix Module.End

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A full family of distinct spectral points supplies a basis of eigenvectors, including when the finite index type is empty.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_eigenbasis_of_injective_mem_spectrum
    (M : Matrix n n ℂ) (ev : n → ℂ) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum ℂ M) :
    ∃ b : Module.Basis n ℂ (n → ℂ), ∀ i, M *ᵥ b i = ev i • b i := by
  classical
  have heig : ∀ i, Module.End.HasEigenvalue M.toLin' (ev i) := by
    intro i
    apply Module.End.HasEigenvalue.of_mem_spectrum
    simpa using hmem i
  choose v hv using fun i => (heig i).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' M.toLin' ev hev v hv
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli
    (Module.finrank_fintype_fun_eq_card ℂ).symm
  refine ⟨b, ?_⟩
  intro i
  change M.toLin' (b i) = ev i • b i
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using
    (hv i).apply_eq_smul

/-- A full family of distinct spectral points exhausts the matrix spectrum.
This lets conjugate spectral points be matched to exterior branch labels.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem spectrum_eq_range_of_injective_mem_spectrum
    (M : Matrix n n ℂ) (ev : n → ℂ) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum ℂ M) : spectrum ℂ M = Set.range ev := by
  obtain ⟨b, hb⟩ := exists_eigenbasis_of_injective_mem_spectrum M ev hev hmem
  have hD : LinearMap.toMatrix b b M.toLin' = Matrix.diagonal ev := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [← Matrix.spectrum_toLin' M, ← LinearMap.spectrum_toMatrix M.toLin' b,
    hD, spectrum_diagonal]

/-- A complete eigenvector basis computes the trace of the matrix exponential
as the sum of the scalar exponentials of its eigenvalues.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem trace_matrixExp_eq_sum_exp_of_eigenbasis
    (M : Matrix n n ℂ) (ev : n → ℂ) (b : Module.Basis n ℂ (n → ℂ))
    (hb : ∀ i, M *ᵥ b i = ev i • b i) :
    Matrix.trace (matrixExp M) = ∑ i, Complex.exp (ev i) := by
  classical
  let e := Pi.basisFun ℂ n
  let U : (Matrix n n ℂ)ˣ :=
    ⟨e.toMatrix b, b.toMatrix e, e.toMatrix_mul_toMatrix_flip b,
      b.toMatrix_mul_toMatrix_flip e⟩
  have hD : LinearMap.toMatrix b b M.toLin' = Matrix.diagonal ev := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hM : (U : Matrix n n ℂ) * Matrix.diagonal ev * (↑(U⁻¹) : Matrix n n ℂ) = M := by
    change e.toMatrix b * Matrix.diagonal ev * b.toMatrix e = M
    rw [← hD, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
    simp [e]
  rw [← hM, matrixExp, Matrix.exp_units_conj, Matrix.trace_units_conj,
    Matrix.exp_diagonal, Matrix.trace_diagonal]
  simp [← Complex.exp_eq_exp_ℂ]

/-- A list of distinct spectral points with the same index type as the matrix
is its full spectrum and computes its exponential trace. In particular, this
discharges Stahl's boundary trace identity from exterior eigenvalue
branches rather than taking that identity as a separate assumption.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem trace_matrixExp_eq_sum_exp_of_injective_mem_spectrum
    (M : Matrix n n ℂ) (ev : n → ℂ) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum ℂ M) :
    Matrix.trace (matrixExp M) = ∑ i, Complex.exp (ev i) := by
  obtain ⟨b, hb⟩ := exists_eigenbasis_of_injective_mem_spectrum M ev hev hmem
  exact trace_matrixExp_eq_sum_exp_of_eigenbasis M ev b hb

end NLAlib
