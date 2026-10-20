import NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixBlockSpectra
import NLAlib.Matrix.Basic.Dilation

/-! # Actual rectangular dilation spectra over arbitrary C*-algebras

Native C*-matrix spectra retain the full possibly continuous free spectrum.
The nonzero row and column Gram spectra agree by the genuine ambient
product-spectrum identity, rather than a finite eigenvalue enumeration.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A]

/-- The actual native C*-matrix adapter of the ordinary rectangular
Hermitian dilation, with the same literal entries. -/
def rectangularDilation (Y : Matrix m n A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  ofMatrix (NLAlib.dilation Y)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The native rectangular dilation is actually self-adjoint. -/
theorem isSelfAdjoint_rectangularDilation (Y : Matrix m n A) :
    IsSelfAdjoint (rectangularDilation Y) := by
  change (NLAlib.dilation Y).IsHermitian
  exact NLAlib.isHermitian_dilation Y

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The literal row Gram matrix is actually self-adjoint in its native
C*-matrix algebra, including empty shapes. -/
theorem isSelfAdjoint_rowGram (Y : Matrix m n A) :
    IsSelfAdjoint (ofMatrix (Y * Yᴴ)) := by
  change (Y * Yᴴ)ᴴ = Y * Yᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The literal column Gram matrix is actually self-adjoint. -/
theorem isSelfAdjoint_columnGram (Y : Matrix m n A) :
    IsSelfAdjoint (ofMatrix (Yᴴ * Y)) := by
  change (Yᴴ * Y)ᴴ = Yᴴ * Y
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

private theorem notMem_spectrum_zero_of_ne_zero
    (D : Type*) [Fintype D] [DecidableEq D] {r : ℝ} (hr : r ≠ 0) :
    r ∉ spectrum ℝ (0 : CStarMatrix D D A) := by
  rw [spectrum.notMem_iff, sub_zero]
  exact (isUnit_iff_ne_zero.mpr hr).map (algebraMap ℝ (CStarMatrix D D A))

variable [PartialOrder A] [StarOrderedRing A]

/-- Actual nonzero row and column Gram spectra agree for rectangular
matrices over arbitrary C*-algebras. This allows continuous spectral sets. -/
theorem mem_spectrum_real_rowGram_iff_columnGram_of_ne_zero
    (Y : Matrix m n A) {r : ℝ} (hr : r ≠ 0) :
    r ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)) ↔
      r ∈ spectrum ℝ (ofMatrix (Yᴴ * Y)) := by
  let U : CStarMatrix (m ⊕ n) (m ⊕ n) A := ofMatrix (Matrix.fromBlocks 0 Y 0 0)
  let V : CStarMatrix (m ⊕ n) (m ⊕ n) A := ofMatrix (Matrix.fromBlocks 0 0 Yᴴ 0)
  have hUV : U * V = blockDiagonalStarAlgHom (ofMatrix (Y * Yᴴ), (0 : CStarMatrix n n A)) := by
    change Matrix.fromBlocks 0 Y 0 0 * Matrix.fromBlocks 0 0 Yᴴ 0 = Matrix.fromBlocks (Y * Yᴴ) 0 0 0
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  have hVU : V * U = blockDiagonalStarAlgHom ((0 : CStarMatrix m m A), ofMatrix (Yᴴ * Y)) := by
    change Matrix.fromBlocks 0 0 Yᴴ 0 * Matrix.fromBlocks 0 Y 0 0 = Matrix.fromBlocks 0 0 0 (Yᴴ * Y)
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have h := spectrum.unit_mem_mul_comm (R := ℝ) (a := U) (b := V) (r := Units.mk0 r hr)
  rw [hUV, hVU,
    spectrum_real_blockDiagonal _ _ (isSelfAdjoint_rowGram Y) (by change star (0 : CStarMatrix n n A) = 0; simp),
    spectrum_real_blockDiagonal _ _ (by change star (0 : CStarMatrix m m A) = 0; simp) (isSelfAdjoint_columnGram Y)] at h
  simpa only [Units.val_mk0, Set.mem_union,
    notMem_spectrum_zero_of_ne_zero (A := A) n hr,
    notMem_spectrum_zero_of_ne_zero (A := A) m hr, or_false, false_or] using h

omit [PartialOrder A] [StarOrderedRing A] in
/-- Squaring the actual native dilation gives the literal two Gram blocks. -/
theorem rectangularDilation_sq (Y : Matrix m n A) :
    rectangularDilation Y ^ 2 =
      blockDiagonalStarAlgHom (ofMatrix (Y * Yᴴ), ofMatrix (Yᴴ * Y)) := by
  change (NLAlib.dilation Y) ^ 2 = Matrix.fromBlocks (Y * Yᴴ) 0 0 (Yᴴ * Y)
  simp only [NLAlib.dilation, pow_two, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

/-- The square-image of the full actual dilation spectrum is exactly the
union of the two actual Gram spectra. This retains continuous free spectra.
Source: arXiv:2406.11453v2, Section 5.3.
atlas: gaussian-quadratic-free-spectrum (partial). -/
theorem sq_image_spectrum_real_rectangularDilation (Y : Matrix m n A) :
    (fun r : ℝ => r ^ 2) '' spectrum ℝ (rectangularDilation Y) =
      spectrum ℝ (ofMatrix (Y * Yᴴ)) ∪ spectrum ℝ (ofMatrix (Yᴴ * Y)) := by
  rw [← cfc_map_spectrum (a := rectangularDilation Y) (f := fun r : ℝ => r ^ 2)
    (isSelfAdjoint_rectangularDilation Y),
    cfc_pow_id (R := ℝ) (rectangularDilation Y) 2 (isSelfAdjoint_rectangularDilation Y),
    rectangularDilation_sq]
  exact spectrum_real_blockDiagonal _ _ (isSelfAdjoint_rowGram Y) (isSelfAdjoint_columnGram Y)

end CStarMatrix
