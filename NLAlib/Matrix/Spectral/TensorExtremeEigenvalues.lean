import NLAlib.Matrix.Structured.KroneckerFrames
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Functions.HermitianCalculus

/-! # Largest Hermitian eigenvalues under coordinate changes and amplification

Tensoring with a nonempty finite identity repeats every spectral value.
The actual spectral set and its supremum are therefore unchanged, including
indefinite and zero-dimensional matrices. Source: Horn–Johnson, §4.2.
-/
noncomputable section
open Matrix
open scoped Matrix Kronecker
namespace NLAlib
variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- Amplification by a nonempty identity preserves the complete real spectrum,
including signed eigenvalues of an indefinite Hermitian matrix. -/
theorem spectrum_real_kronecker_one [Nonempty r] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    spectrum ℝ (A ⊗ₖ (1 : Matrix r r ℂ)) = spectrum ℝ A := by
  classical
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hU : HasOrthonormalCols U := by
    change Uᴴ * U = 1
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hD : A = thinSingularMatrix U U hA.eigenvalues := by
    simpa only [thinSingularMatrix, U, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using hA.spectral_theorem
  have hI : (1 : Matrix r r ℂ) =
      thinSingularMatrix (1 : Matrix r r ℂ) (1 : Matrix r r ℂ) (fun _ : r => 1) := by
    simp [thinSingularMatrix]
  have hAmp : A ⊗ₖ (1 : Matrix r r ℂ) =
      thinSingularMatrix (U ⊗ₖ (1 : Matrix r r ℂ)) (U ⊗ₖ (1 : Matrix r r ℂ))
        (fun ir => hA.eigenvalues ir.1) := by
    calc
      _ = thinSingularMatrix U U hA.eigenvalues ⊗ₖ
          thinSingularMatrix (1 : Matrix r r ℂ) (1 : Matrix r r ℂ) (fun _ : r => 1) := by
        rw [← hD, ← hI]
      _ = _ := by rw [thinSingularMatrix_kronecker]; simp only [mul_one]
  have hW : HasOrthonormalCols (U ⊗ₖ (1 : Matrix r r ℂ)) :=
    hasOrthonormalCols_kronecker hU hasOrthonormalCols_one
  calc
    _ = spectrum ℝ (thinSingularMatrix (U ⊗ₖ (1 : Matrix r r ℂ))
        (U ⊗ₖ (1 : Matrix r r ℂ)) (fun ir => hA.eigenvalues ir.1)) :=
      congrArg (spectrum ℝ) hAmp
    _ = Set.range (fun ir : n × r => hA.eigenvalues ir.1) :=
      spectrum_real_thinSingularMatrix _ hW _
    _ = Set.range hA.eigenvalues := by
      ext x
      constructor
      · rintro ⟨ir, hir⟩; exact ⟨ir.1, hir⟩
      · rintro ⟨i, hi⟩; exact ⟨(i, Classical.choice inferInstance), hi⟩
    _ = spectrum ℝ A := hA.spectrum_real_eq_range_eigenvalues.symm

/-- Identity amplification preserves the largest Hermitian eigenvalue,
with no positivity assumption on the matrix. -/
theorem lambdaMax_kronecker_one [Nonempty r] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    lambdaMax (A ⊗ₖ (1 : Matrix r r ℂ)) = lambdaMax A := by
  unfold lambdaMax
  rw [spectrum_real_kronecker_one hA]

end NLAlib
