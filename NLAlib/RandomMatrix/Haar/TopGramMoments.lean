import NLAlib.RandomMatrix.Haar.TopGramTransfer
import NLAlib.RandomMatrix.Haar.RealGaussianQR
import NLAlib.RandomMatrix.Haar.ComplexGaussianQR
import NLAlib.RandomMatrix.Haar.GaussianBlockMoments
import NLAlib.Matrix.Subspaces.OrthogonalComplement

/-!
# Exact inverse top-Gram means under actual real and complex Haar frame laws

Native Gaussian QR, independent orthogonal Gaussian blocks, the exact inverse
Wishart moments and Haar inversion give the source finite-dimension correction.
All `ell≤n`, including a full sketch and its empty lower block, are retained.
No matrix-Beta law or desired output expectation is assumed.
Source: Epperly--Webber (2026), Theorem 2.1 and Section 5.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The actual real Haar top block has full row rank almost surely. -/
theorem ae_isUnit_topGram_haar_real {n r ell : ℕ} (hr : r ≤ ell) (helln : ell ≤ n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U) :
    ∀ᵐ Q ∂unitaryHaarFrameLaw ℝ n ell helln, IsUnit (unitaryFrameTopGram ℝ U Q) := by
  let E := (coordinateUnitaryStiefel ℝ n ell helln).val
  apply ae_isUnit_topGram_of_unitaryQR_law ℝ (hr.trans helln) helln U hU
    (gaussianMatrix (Fin n) (Fin r)) (hasLaw_unitaryQRFrame_gaussianMatrix (hr.trans helln))
  · exact gaussianMatrix_ae_linearIndependent_qrColumnFamily (hr.trans helln)
  · exact ae_gaussian_topGram_isUnit E (coordinateUnitaryStiefel ℝ n ell helln).property hr

/-- The actual complex Haar top block has full row rank almost surely. -/
theorem ae_isUnit_topGram_haar_complex {n r ell : ℕ} (hr : r ≤ ell) (helln : ell ≤ n)
    (U : Matrix (Fin n) (Fin r) ℂ) (hU : HasOrthonormalCols U) :
    ∀ᵐ Q ∂unitaryHaarFrameLaw ℂ n ell helln, IsUnit (unitaryFrameTopGram ℂ U Q) := by
  let E := (coordinateUnitaryStiefel ℂ n ell helln).val
  exact ae_isUnit_topGram_of_unitaryQR_law ℂ (hr.trans helln) helln U hU
    (circularComplexGaussianMatrix (Fin n) (Fin r))
    (hasLaw_unitaryQRFrame_circularComplexGaussianMatrix (hr.trans helln))
    (circularComplexGaussianMatrix_ae_linearIndependent_unitaryQRColumnFamily (hr.trans helln))
    (ae_circularComplexGaussian_topGram_isUnit E (coordinateUnitaryStiefel ℂ n ell helln).property hr)

/-- The actual real Haar inverse top-Gram trace is integrable and has the
exact mean `r+(n-ell)r/(ell-r-1)`, for arbitrary fixed orthonormal input frame.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_re_trace_inv_topGram_haar_real {n r ell : ℕ}
    (hr : r+2 ≤ ell) (helln : ell ≤ n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U) :
    Integrable (fun Q => RCLike.re (Matrix.trace (unitaryFrameTopGram ℝ U Q)⁻¹))
      (unitaryHaarFrameLaw ℝ n ell helln) ∧
    ∫ Q, RCLike.re (Matrix.trace (unitaryFrameTopGram ℝ U Q)⁻¹)
      ∂unitaryHaarFrameLaw ℝ n ell helln = (r:ℝ)+((n:ℝ)-ell)*r/((ell:ℝ)-r-1) := by
  have hre : r ≤ ell := by omega
  let E := (coordinateUnitaryStiefel ℝ n ell helln).val
  have hE : HasOrthonormalCols E := (coordinateUnitaryStiefel ℝ n ell helln).property
  obtain ⟨V,hV,hEV,hcomp⟩ :
      ∃ V : Matrix (Fin n) (Fin (n-ell)) ℝ,
        HasOrthonormalCols V ∧ Eᴴ*V=0 ∧ E*Eᴴ+V*Vᴴ=1 := by
    have hcard : Fintype.card (Fin n)-Fintype.card (Fin ell)=n-ell := by
      simp only [Fintype.card_fin]
    rw [← hcard]
    exact exists_unitary_complement_orthogonal E hE
  have hcross := integrable_and_integral_frobSq_gaussian_top_bottom_inverse E V hE hV hEV hr
  have hfull : ∀ᵐ G ∂gaussianMatrix (Fin n) (Fin r),
      LinearIndependent ℝ (unitaryQRColumnFamily ℝ G) := by
    exact gaussianMatrix_ae_linearIndependent_qrColumnFamily (hre.trans helln)
  have h := integrable_and_integral_re_trace_inv_topGram_of_unitaryQR_law ℝ
    (hre.trans helln) helln U hU V hcomp (gaussianMatrix (Fin n) (Fin r))
    (hasLaw_unitaryQRFrame_gaussianMatrix (hre.trans helln)) hfull
    (ae_gaussian_topGram_isUnit E hE hre) (((n-ell:ℕ):ℝ)*r/((ell:ℝ)-r-1)) hcross
  simpa only [Nat.cast_sub helln] using h

/-- The actual complex Haar inverse top-Gram trace is integrable and has the
exact mean `r+(n-ell)r/(ell-r)`. The underlying complex frame law is actual
normalized compact unitary Haar probability, with arbitrary nonreal data.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_re_trace_inv_topGram_haar_complex {n r ell : ℕ}
    (hr : r+1 ≤ ell) (helln : ell ≤ n)
    (U : Matrix (Fin n) (Fin r) ℂ) (hU : HasOrthonormalCols U) :
    Integrable (fun Q => RCLike.re (Matrix.trace (unitaryFrameTopGram ℂ U Q)⁻¹))
      (unitaryHaarFrameLaw ℂ n ell helln) ∧
    ∫ Q, RCLike.re (Matrix.trace (unitaryFrameTopGram ℂ U Q)⁻¹)
      ∂unitaryHaarFrameLaw ℂ n ell helln = (r:ℝ)+((n:ℝ)-ell)*r/((ell:ℝ)-r) := by
  have hre : r ≤ ell := by omega
  let E := (coordinateUnitaryStiefel ℂ n ell helln).val
  have hE : HasOrthonormalCols E := (coordinateUnitaryStiefel ℂ n ell helln).property
  obtain ⟨V,hV,hEV,hcomp⟩ :
      ∃ V : Matrix (Fin n) (Fin (n-ell)) ℂ,
        HasOrthonormalCols V ∧ Eᴴ*V=0 ∧ E*Eᴴ+V*Vᴴ=1 := by
    have hcard : Fintype.card (Fin n)-Fintype.card (Fin ell)=n-ell := by
      simp only [Fintype.card_fin]
    rw [← hcard]
    exact exists_unitary_complement_orthogonal E hE
  have hcross := integrable_and_integral_frobSq_circularComplexGaussian_top_bottom_inverse E V hE hV hEV hr
  have h := integrable_and_integral_re_trace_inv_topGram_of_unitaryQR_law ℂ
    (hre.trans helln) helln U hU V hcomp (circularComplexGaussianMatrix (Fin n) (Fin r))
    (hasLaw_unitaryQRFrame_circularComplexGaussianMatrix (hre.trans helln))
    (circularComplexGaussianMatrix_ae_linearIndependent_unitaryQRColumnFamily (hre.trans helln))
    (ae_circularComplexGaussian_topGram_isUnit E hE hre) (((n-ell:ℕ):ℝ)*r/((ell:ℝ)-r)) hcross
  simpa only [Nat.cast_sub helln] using h

/-- Native real Haar top-block rank transports to any random frame with that law. -/
theorem ae_isUnit_topGram_haar_real_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n r ell : ℕ}
    {Q : Ω → UnitaryStiefel ℝ n ell} (hr : r ≤ ell) (helln : ell ≤ n)
    (hQ : HasLaw Q (unitaryHaarFrameLaw ℝ n ell helln) μ)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U) :
    ∀ᵐ ω ∂μ, IsUnit (unitaryFrameTopGram ℝ U (Q ω)) := by
  have h := ae_isUnit_topGram_haar_real hr helln U hU
  rw [← hQ.map_eq] at h
  exact ae_of_ae_map hQ.aemeasurable h

/-- Native complex Haar top-block rank transports to any random frame with that law. -/
theorem ae_isUnit_topGram_haar_complex_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n r ell : ℕ}
    {Q : Ω → UnitaryStiefel ℂ n ell} (hr : r ≤ ell) (helln : ell ≤ n)
    (hQ : HasLaw Q (unitaryHaarFrameLaw ℂ n ell helln) μ)
    (U : Matrix (Fin n) (Fin r) ℂ) (hU : HasOrthonormalCols U) :
    ∀ᵐ ω ∂μ, IsUnit (unitaryFrameTopGram ℂ U (Q ω)) := by
  have h := ae_isUnit_topGram_haar_complex hr helln U hU
  rw [← hQ.map_eq] at h
  exact ae_of_ae_map hQ.aemeasurable h

private theorem measurable_re_trace_inv_topGram {𝕜 : Type*} [RCLike 𝕜] {n r ell : ℕ}
    (U : Matrix (Fin n) (Fin r) 𝕜) :
    Measurable (fun Q : UnitaryStiefel 𝕜 n ell => RCLike.re (Matrix.trace (unitaryFrameTopGram 𝕜 U Q)⁻¹)) :=
  (RCLike.continuous_re.comp continuous_id.matrix_trace).measurable.comp
    (measurable_matrix_inv.comp (by unfold unitaryFrameTopGram; fun_prop))

/-- The actual real Haar inverse top-Gram trace mean and integrability on any
sample space carrying that native frame law.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_re_trace_inv_topGram_haar_real_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n r ell : ℕ}
    {Q : Ω → UnitaryStiefel ℝ n ell} (hr : r+2 ≤ ell) (helln : ell ≤ n)
    (hQ : HasLaw Q (unitaryHaarFrameLaw ℝ n ell helln) μ)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : HasOrthonormalCols U) :
    Integrable (fun ω => RCLike.re (Matrix.trace (unitaryFrameTopGram ℝ U (Q ω))⁻¹)) μ ∧
    ∫ ω, RCLike.re (Matrix.trace (unitaryFrameTopGram ℝ U (Q ω))⁻¹) ∂μ =
      (r:ℝ)+((n:ℝ)-ell)*r/((ell:ℝ)-r-1) := by
  have h := integrable_and_integral_re_trace_inv_topGram_haar_real hr helln U hU
  constructor
  · have hi := h.1
    rw [← hQ.map_eq] at hi
    exact hi.comp_aemeasurable hQ.aemeasurable
  · exact (hQ.integral_comp (measurable_re_trace_inv_topGram U).aestronglyMeasurable).trans h.2

/-- The actual complex Haar inverse top-Gram trace mean and integrability on
any sample space carrying that native frame law.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_re_trace_inv_topGram_haar_complex_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n r ell : ℕ}
    {Q : Ω → UnitaryStiefel ℂ n ell} (hr : r+1 ≤ ell) (helln : ell ≤ n)
    (hQ : HasLaw Q (unitaryHaarFrameLaw ℂ n ell helln) μ)
    (U : Matrix (Fin n) (Fin r) ℂ) (hU : HasOrthonormalCols U) :
    Integrable (fun ω => RCLike.re (Matrix.trace (unitaryFrameTopGram ℂ U (Q ω))⁻¹)) μ ∧
    ∫ ω, RCLike.re (Matrix.trace (unitaryFrameTopGram ℂ U (Q ω))⁻¹) ∂μ =
      (r:ℝ)+((n:ℝ)-ell)*r/((ell:ℝ)-r) := by
  have h := integrable_and_integral_re_trace_inv_topGram_haar_complex hr helln U hU
  constructor
  · have hi := h.1
    rw [← hQ.map_eq] at hi
    exact hi.comp_aemeasurable hQ.aemeasurable
  · exact (hQ.integral_comp (measurable_re_trace_inv_topGram U).aestronglyMeasurable).trans h.2

end NLAlib
