import NLAlib.RandomMatrix.Haar.QRLeadingGram
import NLAlib.Matrix.Measurability.GramPseudoinverse
import Mathlib.Probability.HasLaw

/-!
# Native transfer of Gaussian QR Gram moments to actual Haar frames

The scalar statistic and the full-rank event are transported through exact
matrix pushforward laws. The inverse moment is derived from the original
Gaussian blocks and their finite Frobenius moment, not from a Beta-law premise.
Supports Epperly--Webber (2026), Theorem 2.1 and Section 5.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Exact matrix law connecting a genuine QR input law to the Haar top Gram. -/
theorem map_leadingGram_unitaryQRFrame_eq_map_topGram {n r ell : ℕ}
    (hrn : r ≤ n) (helln : ell ≤ n) (U : Matrix (Fin n) (Fin r) 𝕜)
    (hU : HasOrthonormalCols U) (μ : Measure (Matrix (Fin n) (Fin r) 𝕜))
    (hlaw : HasLaw (unitaryQRFrame 𝕜 n r hrn) (unitaryHaarFrameLaw 𝕜 n r hrn) μ) :
    μ.map (fun G => unitaryFrameLeadingGram 𝕜 helln (unitaryQRFrame 𝕜 n r hrn G)) =
      (unitaryHaarFrameLaw 𝕜 n ell helln).map (unitaryFrameTopGram 𝕜 U) := by
  rw [unitaryHaarFrameLaw_map_topGram_eq 𝕜 hrn helln U hU]
  rw [← hlaw.map_eq,Measure.map_map (by unfold unitaryFrameLeadingGram; fun_prop)
    (measurable_unitaryQRFrame 𝕜 n r hrn)]
  rfl

private theorem measurableSet_isUnit_matrix (r : ℕ) :
    MeasurableSet {M : Matrix (Fin r) (Fin r) 𝕜 | IsUnit M} := by
  simp only [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  exact (isClosed_eq continuous_id.matrix_det continuous_const).isOpen_compl.measurableSet

/-- Actual QR block rank gives almost-sure invertibility of the Haar top Gram.
Only the original Gaussian rank events, rather than an output-rank assumption,
are needed by this transfer. -/
theorem ae_isUnit_topGram_of_unitaryQR_law {n r ell : ℕ}
    (hrn : r ≤ n) (helln : ell ≤ n) (U : Matrix (Fin n) (Fin r) 𝕜)
    (hU : HasOrthonormalCols U) (μ : Measure (Matrix (Fin n) (Fin r) 𝕜))
    (hlaw : HasLaw (unitaryQRFrame 𝕜 n r hrn) (unitaryHaarFrameLaw 𝕜 n r hrn) μ)
    (hfull : ∀ᵐ G ∂μ, LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 G))
    (htop : ∀ᵐ G ∂μ, IsUnit (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ*
      ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G))) :
    ∀ᵐ Q ∂unitaryHaarFrameLaw 𝕜 n ell helln, IsUnit (unitaryFrameTopGram 𝕜 U Q) := by
  let J := fun G => unitaryFrameLeadingGram 𝕜 helln (unitaryQRFrame 𝕜 n r hrn G)
  have hL : Measurable (unitaryFrameLeadingGram 𝕜 (r := r) helln) := by
    unfold unitaryFrameLeadingGram
    fun_prop
  have hJ : Measurable J := by
    exact hL.comp (measurable_unitaryQRFrame 𝕜 n r hrn)
  have hsrc : ∀ᵐ G ∂μ, IsUnit (J G) := by
    filter_upwards [hfull,htop] with G hG hY
    let E := (coordinateUnitaryStiefel 𝕜 n ell helln).val
    let Q := (unitaryQRFrame 𝕜 n r hrn G).val
    let R := unitaryQRUpper 𝕜 hrn G
    have hYR : (Eᴴ*Q)*R=Eᴴ*G := by
      rw [Matrix.mul_assoc,unitaryQRFrame_mul_unitaryQRUpper 𝕜 hrn G hG]
    exact (inv_gram_of_mul_right_eq (Eᴴ*Q) (Eᴴ*G) R
      (isUnit_unitaryQRUpper 𝕜 hrn G hG) hY hYR).2
  have hmap : ∀ᵐ M ∂μ.map J, IsUnit M :=
    (ae_map_iff hJ.aemeasurable (measurableSet_isUnit_matrix 𝕜 r)).mpr hsrc
  rw [map_leadingGram_unitaryQRFrame_eq_map_topGram 𝕜 hrn helln U hU μ hlaw] at hmap
  exact ae_of_ae_map (by unfold unitaryFrameTopGram; fun_prop) hmap

/-- The finite native Gaussian block mean gives the actual Haar top-Gram
inverse trace mean. The source statistic is a squared Frobenius norm, so its
integrability is established before any expectation is transferred. -/
theorem integrable_and_integral_re_trace_inv_topGram_of_unitaryQR_law
    {n r ell s : ℕ} (hrn : r ≤ n) (helln : ell ≤ n)
    (U : Matrix (Fin n) (Fin r) 𝕜) (hU : HasOrthonormalCols U)
    (V : Matrix (Fin n) (Fin s) 𝕜)
    (hcomp : (coordinateUnitaryStiefel 𝕜 n ell helln).val*
      (coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ+V*Vᴴ=1)
    (μ : Measure (Matrix (Fin n) (Fin r) 𝕜))
    (hlaw : HasLaw (unitaryQRFrame 𝕜 n r hrn) (unitaryHaarFrameLaw 𝕜 n r hrn) μ)
    (hfull : ∀ᵐ G ∂μ, LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 G))
    (htop : ∀ᵐ G ∂μ, IsUnit (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ*
      ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G))) (c : ℝ)
    (hcross : Integrable (fun G => frobSq ((Vᴴ*G)*
      (pinvR (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ))ᴴ)) μ ∧
      ∫ G, frobSq ((Vᴴ*G)*(pinvR (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ))ᴴ) ∂μ = c) :
    Integrable (fun Q => RCLike.re (Matrix.trace (unitaryFrameTopGram 𝕜 U Q)⁻¹))
      (unitaryHaarFrameLaw 𝕜 n ell helln) ∧
    ∫ Q, RCLike.re (Matrix.trace (unitaryFrameTopGram 𝕜 U Q)⁻¹)
      ∂unitaryHaarFrameLaw 𝕜 n ell helln = (r:ℝ)+c := by
  have := hlaw.isProbabilityMeasure
  let J := fun G => unitaryFrameLeadingGram 𝕜 helln (unitaryQRFrame 𝕜 n r hrn G)
  let H := unitaryFrameTopGram 𝕜 U (ell := ell)
  let φ : Matrix (Fin r) (Fin r) 𝕜 → ℝ := fun M => RCLike.re (Matrix.trace M⁻¹)
  have hL : Measurable (unitaryFrameLeadingGram 𝕜 (r := r) helln) := by
    unfold unitaryFrameLeadingGram
    fun_prop
  have hJ : Measurable J := hL.comp (measurable_unitaryQRFrame 𝕜 n r hrn)
  have hH : Measurable H := by unfold H unitaryFrameTopGram; fun_prop
  have hφ : Measurable φ :=
    (RCLike.continuous_re.comp continuous_id.matrix_trace).measurable.comp measurable_matrix_inv
  have hl : μ.map J = (unitaryHaarFrameLaw 𝕜 n ell helln).map H :=
    map_leadingGram_unitaryQRFrame_eq_map_topGram 𝕜 hrn helln U hU μ hlaw
  have he : (fun G => φ (J G)) =ᵐ[μ] fun G => (r:ℝ)+frobSq ((Vᴴ*G)*
      (pinvR (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ))ᴴ) := by
    filter_upwards [hfull,htop] with G hG hY
    exact (re_trace_inv_leadingGram_unitaryQRFrame_eq 𝕜 hrn helln V hcomp G hG hY).1
  have hi : Integrable (fun G => φ (J G)) μ :=
    ((integrable_const (r:ℝ)).add hcross.1).congr he.symm
  have hmap := (integrable_map_measure hφ.aestronglyMeasurable hJ.aemeasurable).mpr hi
  rw [hl] at hmap
  refine ⟨(integrable_map_measure hφ.aestronglyMeasurable hH.aemeasurable).mp hmap,?_⟩
  rw [← integral_map hH.aemeasurable hφ.aestronglyMeasurable,← hl,
    integral_map hJ.aemeasurable hφ.aestronglyMeasurable,integral_congr_ae he,
    integral_add (integrable_const _) hcross.1,hcross.2,integral_const]
  simp

end NLAlib
