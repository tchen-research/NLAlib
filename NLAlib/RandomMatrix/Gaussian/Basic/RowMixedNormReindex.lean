import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfileReindex
import NLAlib.Matrix.Norms.RowMixedNormMeasurable

/-!
# Gaussian mixed-row norm invariance under coordinate permutations

The actual matrix-law reindexing and the deterministic mixed-norm invariance
preserve the law and mean of every native mixed row norm, including infinity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

/-- Simultaneous finite permutations of a symmetric Gaussian profile preserve
the actual law of every mixed row norm of exponent at least one. -/
theorem identDistrib_rowMixedNorm_symmetricGaussianMatrix_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    IdentDistrib (fun G => rowMixedNorm (symmetricGaussianMatrix b G) p)
      (fun G => rowMixedNorm (symmetricGaussianMatrix (b.submatrix e e) G) p)
      (gaussianMatrix κ κ) (gaussianMatrix ι ι) := by
  have h := (identDistrib_symmetricGaussianMatrix_submatrix e b hb).comp
    (measurable_rowMixedNorm hp)
  have hr (A : Matrix κ κ ℝ) : rowMixedNorm (A.submatrix e e) p = rowMixedNorm A p :=
    rowMixedNorm_submatrix_equiv A e e hp
  simpa only [Function.comp_def, hr] using h

/-- Simultaneous finite profile permutations preserve the actual expected
native mixed row norm, including infinity. -/
theorem integral_rowMixedNorm_symmetricGaussianMatrix_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    (∫ G, rowMixedNorm (symmetricGaussianMatrix (b.submatrix e e) G) p ∂gaussianMatrix ι ι) =
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix κ κ :=
  (identDistrib_rowMixedNorm_symmetricGaussianMatrix_submatrix e b hb hp).integral_eq.symm

end NLAlib
