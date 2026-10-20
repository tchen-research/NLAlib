import NLAlib.Matrix.Functions.PositiveBlockNorm
import NLAlib.Matrix.Norms.Core
import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral

/-!
# Actual paired-kernel integral contractions

The actual map `X ↦ integral A X B*` is a spectral-norm contraction whenever
both actual row-Gram integrals are bounded by the identity. The proof uses
a pointwise positive block and integrates it; there is no dimension factor
and no assumed norm bound for the integral map.

This supplies the mixed-map Cauchy--Schwarz step in the global injectivity
argument for the matrix K-transform.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
  {μ : Measure Ω}

private theorem posSemidef_cross_kernel_fromBlocks
    (A B X : Matrix n n ℂ) (hX : specNorm X ≤ 1) :
    (fromBlocks (A * Aᴴ) (A * X * Bᴴ) (A * X * Bᴴ)ᴴ (B * Bᴴ)).PosSemidef := by
  have h := (posSemidef_identity_fromBlocks_of_specNorm_le_one hX).mul_mul_conjTranspose_same
    (fromBlocks A 0 0 B)
  convert! h using 1
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The actual integral of the mixed kernel is the off-diagonal block of
an actual PSD Gram block. Only the three displayed matrix kernels need be
integrable, and empty matrix dimensions are included. -/
theorem posSemidef_integral_cross_kernel_fromBlocks
    (A B : Ω → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hAA : Integrable (fun ω => A ω * (A ω)ᴴ) μ)
    (hBB : Integrable (fun ω => B ω * (B ω)ᴴ) μ)
    (hAB : Integrable (fun ω => A ω * X * (B ω)ᴴ) μ)
    (hX : specNorm X ≤ 1) :
    (fromBlocks (∫ ω, A ω * (A ω)ᴴ ∂μ) (∫ ω, A ω * X * (B ω)ᴴ ∂μ)
      (∫ ω, A ω * X * (B ω)ᴴ ∂μ)ᴴ (∫ ω, B ω * (B ω)ᴴ ∂μ)).PosSemidef := by
  let F : Ω → Matrix (n ⊕ n) (n ⊕ n) ℂ := fun ω =>
    fromBlocks (A ω * (A ω)ᴴ) (A ω * X * (B ω)ᴴ)
      (A ω * X * (B ω)ᴴ)ᴴ (B ω * (B ω)ᴴ)
  have hABstar : Integrable (fun ω => (A ω * X * (B ω)ᴴ)ᴴ) μ := by
    let L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
      (starₗᵢ ℝ : Matrix n n ℂ ≃ₗᵢ[ℝ] Matrix n n ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.integrable_comp hAB
  have hF : Integrable F μ := by
    apply Matrix.integrable_iff_entries.mpr
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (Matrix.integrable_iff_entries.mp hAA) i j
    · exact (Matrix.integrable_iff_entries.mp hAB) i j
    · exact (Matrix.integrable_iff_entries.mp hABstar) i j
    · exact (Matrix.integrable_iff_entries.mp hBB) i j
  have hFpos : ∀ᵐ ω ∂μ, 0 ≤ F ω := ae_of_all _ fun ω =>
    (posSemidef_cross_kernel_fromBlocks (A ω) (B ω) X hX).nonneg
  have hInt : (∫ ω, F ω ∂μ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae hFpos)
  have he : (∫ ω, F ω ∂μ) =
      fromBlocks (∫ ω, A ω * (A ω)ᴴ ∂μ) (∫ ω, A ω * X * (B ω)ᴴ ∂μ)
        (∫ ω, A ω * X * (B ω)ᴴ ∂μ)ᴴ (∫ ω, B ω * (B ω)ᴴ ∂μ) := by
    rw [← Matrix.integral_conjTranspose]
    ext i j
    rw [Matrix.integral_apply hF]
    rcases i with i | i <;> rcases j with j | j
    · exact (Matrix.integral_apply hAA i j).symm
    · exact (Matrix.integral_apply hAB i j).symm
    · exact (Matrix.integral_apply hABstar i j).symm
    · exact (Matrix.integral_apply hBB i j).symm
  rw [he] at hInt
  exact hInt

/-- An actual paired-kernel integral is a spectral-norm contraction when
both row-Gram integrals are bounded by the identity. Only the actual three
matrix kernels need be integrable. Empty dimensions are included. -/
theorem specNorm_integral_cross_kernel_le_one
    (A B : Ω → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hAA : Integrable (fun ω => A ω * (A ω)ᴴ) μ)
    (hBB : Integrable (fun ω => B ω * (B ω)ᴴ) μ)
    (hAB : Integrable (fun ω => A ω * X * (B ω)ᴴ) μ)
    (hA : (∫ ω, A ω * (A ω)ᴴ ∂μ) ≤ 1)
    (hB : (∫ ω, B ω * (B ω)ᴴ ∂μ) ≤ 1)
    (hX : specNorm X ≤ 1) :
    specNorm (∫ ω, A ω * X * (B ω)ᴴ ∂μ) ≤ 1 := by
  have hInt := posSemidef_integral_cross_kernel_fromBlocks A B X hAA hBB hAB hX
  have hdiag := posSemidef_fromBlocks_diag (Matrix.le_iff.mp hA) (Matrix.le_iff.mp hB)
  have hsum := hInt.add hdiag
  have hsumEq :
      fromBlocks (∫ ω, A ω * (A ω)ᴴ ∂μ) (∫ ω, A ω * X * (B ω)ᴴ ∂μ)
          (∫ ω, A ω * X * (B ω)ᴴ ∂μ)ᴴ (∫ ω, B ω * (B ω)ᴴ ∂μ) +
        fromBlocks (1 - ∫ ω, A ω * (A ω)ᴴ ∂μ) 0 0 (1 - ∫ ω, B ω * (B ω)ᴴ ∂μ) =
      fromBlocks 1 (∫ ω, A ω * X * (B ω)ᴴ ∂μ)
        (∫ ω, A ω * X * (B ω)ᴴ ∂μ)ᴴ 1 := by
    rw [Matrix.fromBlocks_add]
    simp
  rw [hsumEq] at hsum
  rw [specNorm_eq_norm]
  exact norm_le_one_of_posSemidef_identity_fromBlocks hsum

private theorem posDef_cross_diag {P Q : Matrix n n ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) : (fromBlocks P 0 0 Q).PosDef := by
  apply (posSemidef_fromBlocks_diag hP.posSemidef hQ.posSemidef).posDef_iff_isUnit.mpr
  exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hP.isUnit,hQ.isUnit⟩

private theorem norm_lt_one_of_posDef_complex_identity_fromBlocks
    {X : Matrix n n ℂ} (hX : (fromBlocks 1 X Xᴴ 1).PosDef) : ‖X‖ < 1 := by
  have hle := norm_le_one_of_posSemidef_identity_fromBlocks hX.posSemidef
  apply lt_of_le_of_ne hle
  intro he
  rcases isEmpty_or_nonempty n with hn | hn
  · have hz : X = 0 := Subsingleton.elim _ _
    simp [hz] at he
  · have hs := CStarAlgebra.norm_mem_spectrum_of_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
    rw [Matrix.l2_opNorm_conjTranspose_mul_self,he,one_mul] at hs
    have hu : IsUnit (1-Xᴴ*X) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      have hd := (Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit
      rwa [Matrix.det_fromBlocks_one₁₁] at hd
    apply (spectrum.mem_iff.mp hs)
    simpa only [map_one] using hu

/-- Strict positivity of both actual row-Gram defects makes the actual
mixed-kernel map strictly contract every point of the closed unit ball.
This is the strict mixed-map step of the Wishart global-injectivity proof.
atlas: block-wishart-variational-edges (partial) -/
theorem specNorm_integral_cross_kernel_lt_one
    (A B : Ω → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hAA : Integrable (fun ω => A ω * (A ω)ᴴ) μ)
    (hBB : Integrable (fun ω => B ω * (B ω)ᴴ) μ)
    (hAB : Integrable (fun ω => A ω * X * (B ω)ᴴ) μ)
    (hA : (1-∫ ω, A ω * (A ω)ᴴ ∂μ).PosDef)
    (hB : (1-∫ ω, B ω * (B ω)ᴴ ∂μ).PosDef)
    (hX : specNorm X ≤ 1) :
    specNorm (∫ ω, A ω * X * (B ω)ᴴ ∂μ) < 1 := by
  have hInt := posSemidef_integral_cross_kernel_fromBlocks A B X hAA hBB hAB hX
  have hdiag := posDef_cross_diag hA hB
  have hsum := Matrix.PosDef.posSemidef_add hInt hdiag
  have he :
      fromBlocks (∫ ω, A ω * (A ω)ᴴ ∂μ) (∫ ω, A ω * X * (B ω)ᴴ ∂μ)
          (∫ ω, A ω * X * (B ω)ᴴ ∂μ)ᴴ (∫ ω, B ω * (B ω)ᴴ ∂μ) +
        fromBlocks (1-∫ ω, A ω * (A ω)ᴴ ∂μ) 0 0
          (1-∫ ω, B ω * (B ω)ᴴ ∂μ) =
      fromBlocks 1 (∫ ω, A ω * X * (B ω)ᴴ ∂μ)
        (∫ ω, A ω * X * (B ω)ᴴ ∂μ)ᴴ 1 := by
    rw [Matrix.fromBlocks_add]
    simp
  rw [he] at hsum
  rw [specNorm_eq_norm]
  exact norm_lt_one_of_posDef_complex_identity_fromBlocks hsum

/-- The genuine mixed-kernel integral has no nonzero fixed point when
both actual row-Gram defects are strictly positive. No norm bound for the
integral operator is assumed.
atlas: block-wishart-variational-edges (partial) -/
theorem eq_zero_of_integral_cross_kernel_fixedPoint
    (A B : Ω → Matrix n n ℂ) (X : Matrix n n ℂ)
    (hAA : Integrable (fun ω => A ω * (A ω)ᴴ) μ)
    (hBB : Integrable (fun ω => B ω * (B ω)ᴴ) μ)
    (hAB : Integrable (fun ω => A ω * X * (B ω)ᴴ) μ)
    (hA : (1-∫ ω, A ω * (A ω)ᴴ ∂μ).PosDef)
    (hB : (1-∫ ω, B ω * (B ω)ᴴ ∂μ).PosDef)
    (hfix : X = ∫ ω, A ω * X * (B ω)ᴴ ∂μ) : X = 0 := by
  by_contra hz
  have hn : 0 < specNorm X := by simpa only [specNorm_eq_norm] using norm_pos_iff.mpr hz
  let Y := (specNorm X)⁻¹ • X
  have hkernel : (fun ω => A ω * Y * (B ω)ᴴ) =
      (fun ω => (specNorm X)⁻¹ • (A ω * X * (B ω)ᴴ)) := by
    funext ω
    simp [Y]
  have hY : specNorm Y = 1 := by
    change specNorm ((specNorm X)⁻¹ • X) = 1
    rw [specNorm_eq_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
      ← specNorm_eq_norm,inv_mul_cancel₀ hn.ne']
  have hYi : Integrable (fun ω => A ω * Y * (B ω)ᴴ) μ := by
    rw [hkernel]
    exact hAB.smul ((specNorm X)⁻¹ : ℝ)
  have hYfix : (∫ ω, A ω * Y * (B ω)ᴴ ∂μ) = Y := by
    rw [hkernel,integral_smul,← hfix]
  have hlt := specNorm_integral_cross_kernel_lt_one A B Y hAA hBB hYi hA hB hY.le
  rw [hYfix,hY] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

end NLAlib
