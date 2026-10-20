import NLAlib.Matrix.Structured.PositiveGramRow
import NLAlib.Matrix.Structured.GramDilationCoefficientParameters
import NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixPiLp
import NLAlib.ForMathlib.Analysis.CStarAlgebra.MatrixFreeAlgebraEvaluation
import NLAlib.ForMathlib.Analysis.CStarAlgebra.SqrtMap
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Norms.BilinearZeroParameter

/-! # Exact scalar and free affine Gram-dilation identities

The actual `3d`-dimensional Hermitian affine matrix is the positive
rectangular row dilation. Positive square roots commute with the genuine
scalar matrix embedding; actual free variables are retained throughout.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d A : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The literal row linearization of an actual free affine matrix is the
actual Hermitian affine matrix on the larger coefficient space. -/
theorem rectangularDilation_rowPair_affineCombination
    (A₀ Q : Matrix d d ℂ) (C : ι → Matrix d d ℂ) (S : ι → A)
    (hS : ∀ i, IsSelfAdjoint (S i)) :
    CStarMatrix.rectangularDilation
      (CStarMatrix.rowPair (CStarMatrix.affineCombination ℂ A₀ C S)
        (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A) (CStarMatrix.ofMatrix Q))) =
      CStarMatrix.affineCombination ℂ
        (dilation (CStarMatrix.rowPair (CStarMatrix.ofMatrix A₀) (CStarMatrix.ofMatrix Q)))
        (gramCoefficientDilation C) S := by
  have hstar (i : ι) : star (S i) = S i := (hS i).star_eq
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [CStarMatrix.rectangularDilation, CStarMatrix.rowPair, CStarMatrix.affineCombination,
      CStarMatrix.mapStarAlgHom_apply, gramCoefficientDilation, gramCoefficientRow,
      dilation, Matrix.conjTranspose_apply, star_add, star_sum,
      star_smul, hstar, ← algebraMap_star_comm]

open scoped Matrix.Norms.L2Operator in
/-- The actual positive Gram row over an arbitrary C*-algebra uses exactly
the scalar embedded deterministic square root. -/
theorem positiveGramRow_scalar_shift_eq_rowPair
    (X : CStarMatrix d d A) (B : Matrix d d ℂ) (hB : B.IsHermitian)
    {b : ℝ} (hb : specNorm B ≤ b) (δ : ℝ) :
    CStarMatrix.positiveGramRow X
        (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A) (CStarMatrix.ofMatrix B)) b δ =
      CStarMatrix.rowPair X (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A)
        (CFC.sqrt (CStarMatrix.ofMatrix B +
          algebraMap ℝ (CStarMatrix d d ℂ) (b + 4 * δ ^ 2)))) := by
  let f := CStarMatrix.mapStarAlgHom (D := d) (StarAlgHom.ofId ℂ A)
  have hbn : ‖CStarMatrix.ofMatrix B‖ ≤ b := by
    simpa only [CStarMatrix.norm_ofMatrix_complex, ← specNorm_eq_norm] using hb
  have hsrc : IsSelfAdjoint (CStarMatrix.ofMatrix B) := by exact hB
  have hnonneg := CStarMatrix.nonneg_add_algebraMap_of_norm_le
    (CStarMatrix.ofMatrix B) hsrc (show ‖CStarMatrix.ofMatrix B‖ ≤ b + 4 * δ ^ 2 by nlinarith)
  have hmap := f.map_sqrt hnonneg
  have hreal : f (algebraMap ℝ (CStarMatrix d d ℂ) (b + 4 * δ ^ 2)) =
      algebraMap ℝ (CStarMatrix d d A) (b + 4 * δ ^ 2) :=
    (f.restrictScalars ℝ).commutes _
  rw [map_add f, hreal] at hmap
  unfold CStarMatrix.positiveGramRow
  rw [← hmap]

open scoped Matrix.Norms.L2Operator in
/-- The actual positive row dilation of a free affine matrix has exactly
the scalar positive-row mean and the genuine three-block coefficients. -/
theorem rectangularDilation_positiveGramRow_affineCombination
    (A₀ B : Matrix d d ℂ) (hB : B.IsHermitian) (C : ι → Matrix d d ℂ)
    (S : ι → A) (hS : ∀ i, IsSelfAdjoint (S i))
    {b : ℝ} (hb : specNorm B ≤ b) (δ : ℝ) :
    CStarMatrix.rectangularDilation (CStarMatrix.positiveGramRow
      (CStarMatrix.affineCombination ℂ A₀ C S)
      (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A) (CStarMatrix.ofMatrix B)) b δ) =
      CStarMatrix.affineCombination ℂ
        (CStarMatrix.ofMatrix.symm (CStarMatrix.rectangularDilation
          (CStarMatrix.positiveGramRow (CStarMatrix.ofMatrix A₀) (CStarMatrix.ofMatrix B) b δ)))
        (gramCoefficientDilation C) S := by
  rw [positiveGramRow_scalar_shift_eq_rowPair _ B hB hb δ]
  let Q : CStarMatrix d d ℂ := CFC.sqrt
    (CStarMatrix.ofMatrix B + algebraMap ℝ (CStarMatrix d d ℂ) (b + 4 * δ ^ 2))
  have hQ : CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm Q) = Q :=
    CStarMatrix.ofMatrix.apply_symm_apply Q
  have h := rectangularDilation_rowPair_affineCombination A₀ (CStarMatrix.ofMatrix.symm Q) C S hS
  rw [hQ] at h
  exact h

omit [Fintype d] [DecidableEq d] in
/-- The scalar affine evaluation at actual real coordinates is exactly
the ordinary Gaussian matrix series, with its original coefficients. -/
theorem affineCombination_ofReal_eq_ofMatrix_real_series
    (A₀ : Matrix d d ℂ) (C : ι → Matrix d d ℂ) (x : ι → ℝ) :
    CStarMatrix.affineCombination ℂ A₀ C (fun i => (x i : ℂ)) =
      CStarMatrix.ofMatrix (A₀ + ∑ i, x i • C i) := by
  ext a b
  simp only [CStarMatrix.affineCombination, CStarMatrix.ofMatrix_apply,
    Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Algebra.algebraMap_self,
    RingHom.id_apply, smul_eq_mul, Complex.real_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Native and ordinary scalar matrix spectra coincide through their
actual star-algebra equivalence. No finite spectral enumeration is used. -/
theorem spectrum_real_ofMatrix_complex (T : Matrix d d ℂ) :
    spectrum ℝ (CStarMatrix.ofMatrix T) = spectrum ℝ T := by
  exact AlgEquiv.spectrum_eq
    ((CStarMatrix.ofMatrixStarAlgEquiv (n := d) (A := ℂ)).toAlgEquiv.restrictScalars ℝ) T

variable [Nontrivial A]

/-- A genuine scalar matrix embedded into any nontrivial C*-algebra has
the same actual self-adjoint spectrum. -/
theorem spectrum_real_scalar_matrix_eq (T : Matrix d d ℂ) (hT : T.IsHermitian) :
    spectrum ℝ (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A) (CStarMatrix.ofMatrix T)) =
      spectrum ℝ T := by
  have hself : IsSelfAdjoint (CStarMatrix.ofMatrix T) := hT
  exact (hself.map_spectrum_real
    (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A))
    (CStarMatrix.mapStarAlgHom_injective _ (FaithfulSMul.algebraMap_injective ℂ A))).trans
      (spectrum_real_ofMatrix_complex T)


/-- With zero original bilinear weak variance, the actual free shifted
Gram spectrum is exactly the deterministic scalar shifted Gram spectrum.
The conclusion is derived from vanishing actual coefficients and genuine
spectral permanence, with no free-law or comparison premise. -/
theorem spectrum_shiftedGram_affineCombination_eq_of_zero_weak
    (A₀ B : Matrix d d ℂ) (hB : B.IsHermitian)
    (C : ι → Matrix d d ℂ) (hzero : bilinearSquareMass C Finset.univ = 0)
    (S : ι → A) :
    spectrum ℝ ((CStarMatrix.affineCombination ℂ A₀ C S) *
        star (CStarMatrix.affineCombination ℂ A₀ C S) +
        CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ A) (CStarMatrix.ofMatrix B)) =
      spectrum ℝ (A₀ * A₀ᴴ + B) := by
  have hC := (bilinearSquareMass_univ_eq_zero_iff C).mp hzero
  let f := CStarMatrix.mapStarAlgHom (D := d) (StarAlgHom.ofId ℂ A)
  have hX : CStarMatrix.affineCombination ℂ A₀ C S = f (CStarMatrix.ofMatrix A₀) := by
    ext i j
    simp only [CStarMatrix.affineCombination, CStarMatrix.ofMatrix_apply, hC, f,
      Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
      CStarMatrix.mapStarAlgHom_apply, StarAlgHom.ofId_apply]
  rw [hX]
  change spectrum ℝ (f (CStarMatrix.ofMatrix A₀) * star (f (CStarMatrix.ofMatrix A₀)) +
    f (CStarMatrix.ofMatrix B)) = _
  rw [← map_star, ← map_mul, ← map_add]
  change spectrum ℝ (f (CStarMatrix.ofMatrix (A₀ * A₀ᴴ + B))) = _
  exact spectrum_real_scalar_matrix_eq (A₀ * A₀ᴴ + B)
    ((Matrix.posSemidef_self_mul_conjTranspose A₀).isHermitian.add hB)

end NLAlib
