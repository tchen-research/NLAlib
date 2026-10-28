import NLAlib.Estimation.Reconstruction.NormalSpectralScaling
import NLAlib.Estimation.Reconstruction.NormalSpectralQuadrature

/-!
# Positive finite normal spectral estimates at the physical scale

The same primitive query strategy can return the finite positive Gauss grid
law. Physical dilation preserves its atom count and scales transport error.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Return the actual finite positive readout at the supplied physical scale. -/
def normalScaledSpectralQuadratureProgram (S : ℝ) (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (Measure ℂ)
      (hermitianPartChebyshevCost M+hermitianPartChebyshevCost M) :=
  ((normalSpectralQuadratureProgram b M).adaptResponses (fun v => S⁻¹•v)).map
    (fun μ => μ.map (fun z => S•z))

omit [DecidableEq n] in
/-- Physical quadrature removes the known scale from each primitive response. -/
theorem run_normalScaledSpectralQuadratureProgram (A : Matrix n n ℂ) (S : ℝ)
    (b : n → ℂ) (M : ℕ) :
    (normalScaledSpectralQuadratureProgram S b M).run (matrixAdjointOracle A) =
      (((normalSpectralQuadratureProgram b M).run (matrixAdjointOracle (S⁻¹•A))).map
        (fun z => S•z)) := by
  rw [normalScaledSpectralQuadratureProgram, QueryProgram.run_map, QueryProgram.run_adaptResponses,
    ← matrixAdjointOracle_real_smul]

/-- Native valid inputs give a positive finite probability law after physical scaling.
atlas: normal-spectral-density-query (partial) -/
theorem isProbabilityMeasure_run_normalScaledSpectralQuadratureProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1) (M : ℕ) :
    IsProbabilityMeasure ((normalScaledSpectralQuadratureProgram S b M).run (matrixAdjointOracle A)) := by
  rw [run_normalScaledSpectralQuadratureProgram]
  have := isProbabilityMeasure_run_normalSpectralQuadratureProgram
    (normal_real_smul hA S⁻¹) b hb (specNorm_inv_smul_le_one hS hbound) M
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The finite native output adds at most `24S/M`, hence the card's `72S/M`,
relative to the actual continuous reconstruction, with no extra matrix queries.
atlas: normal-spectral-density-query (partial) -/
theorem wassersteinEDistOne_normalScaledSpectralQuadratureProgram_le
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1) {M : ℕ} (hM : 1 ≤ M) :
    wassersteinEDistOne
      ((normalScaledSpectralQuadratureProgram S b M).run (matrixAdjointOracle A))
      ((normalScaledSpectralDensityProgram S b M).run (matrixAdjointOracle A)) ≤
        ENNReal.ofReal (72*S/M) := by
  rw [run_normalScaledSpectralQuadratureProgram, run_normalScaledSpectralDensityProgram]
  have hB := normal_real_smul hA S⁻¹
  have hBn := specNorm_inv_smul_le_one hS hbound
  rw [run_normalSpectralDensityProgram hB b hb hBn]
  have hw := wassersteinEDistOne_map_real_smul_le
    ((normalSpectralQuadratureProgram b M).run (matrixAdjointOracle (S⁻¹•A)))
    (normalSpectralDensityKernelLaw hB b M) hS
  apply hw.trans
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (24/(M:ℝ)) :=
      mul_le_mul_of_nonneg_left
        (wassersteinEDistOne_run_normalSpectralQuadratureProgram_le hB b hb hBn hM) (by positivity)
    _ ≤ ENNReal.ofReal (72*S/M) := by
      rw [← ENNReal.ofReal_mul hS.le]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = 24*S/M := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg M)

/-- The scaled native quadrature output has at most `(M+1)^2` positive atoms.
atlas: normal-spectral-density-query (partial) -/
theorem exists_finite_support_run_normalScaledSpectralQuadratureProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1) (M : ℕ) :
    ∃ s : Finset ℂ, s.card ≤ (M+1)^2 ∧
      (normalScaledSpectralQuadratureProgram S b M).run (matrixAdjointOracle A) (s : Set ℂ)ᶜ = 0 := by
  classical
  rw [run_normalScaledSpectralQuadratureProgram]
  obtain ⟨s,hcard,hnull⟩ := exists_finite_support_run_normalSpectralQuadratureProgram
    (normal_real_smul hA S⁻¹) b hb (specNorm_inv_smul_le_one hS hbound) M
  let t := s.image (fun z => S•z)
  refine ⟨t,Finset.card_image_le.trans hcard,?_⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hh : ∀ᵐ z ∂((normalSpectralQuadratureProgram b M).run (matrixAdjointOracle (S⁻¹•A))).map
      (fun z => S•z), z ∈ (t : Set ℂ) := by
    apply (ae_map_iff (by fun_prop)
      (p := fun z : ℂ => z ∈ (t : Set ℂ)) t.finite_toSet.measurableSet).mpr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
    have hz' : z ∈ s := by simpa only [Set.mem_compl_iff,not_not,Finset.mem_coe] using hz
    exact Finset.mem_image.mpr ⟨z,hz',rfl⟩
  filter_upwards [hh] with z hz
  exact fun he => he hz

end NLAlib
