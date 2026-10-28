import NLAlib.Estimation.Reconstruction.NormalSpectralReconstruction
import NLAlib.Estimation.Reconstruction.NormalSpectralMomentTail
import NLAlib.ForMathlib.MeasureTheory.WassersteinMap

/-!
# Native normal spectral-density queries

The actual two-sided query strategy returns the positive kernel law and obeys
the source's explicit one-probe probability bound. The isometric real coordinate
transport introduces no extra dimension or metric factor.
Source: MMSUW 2026, Theorem 1.1 and Algorithms 1--2.
-/

noncomputable section
open MeasureTheory Real
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Native valid inputs produce an actual probability measure.
atlas: normal-spectral-density-query (partial) -/
theorem isProbabilityMeasure_run_normalSpectralDensityProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A ≤ 1) (M : ℕ) :
    IsProbabilityMeasure ((normalSpectralDensityProgram b M).run (matrixAdjointOracle A)) := by
  rw [run_normalSpectralDensityProgram hA b hb hbound]
  have := isProbabilityMeasure_normalSpectralCubeLaw hA b hb hbound
  unfold normalSpectralDensityKernelLaw
  exact Measure.isProbabilityMeasure_map
    Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.aemeasurable

/-- The actual positive kernel output has error controlled by the native
weighted mixed-moment discrepancy. The proved deterministic constant 36 is
stronger than the card's conservative constant 84. -/
theorem wassersteinEDistOne_normalSpectralDensityKernelLaw_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A ≤ 1) {M : ℕ} (hM : 1 ≤ M) :
    wassersteinEDistOne (normalEmpiricalSpectralLaw hA) (normalSpectralDensityKernelLaw hA b M) ≤
      ENNReal.ofReal (36/M + π*tensorChebyshevMomentError (normalCoordinateSpectralLaw hA b)
        (normalEmpiricalCoordinateSpectralLaw hA) M) := by
  have := isProbabilityMeasure_normalCoordinateSpectralLaw hA b hb
  have hν := ae_mem_chebyshevCube_normalCoordinateSpectralLaw hA b hbound
  have hμ := ae_mem_chebyshevCube_normalEmpiricalCoordinateSpectralLaw hA hbound
  have ht := wassersteinEDistOne_tensorChebyshevSmoothedLaw_le_momentError
    (normalEmpiricalCoordinateSpectralLaw hA) (normalCoordinateSpectralLaw hA b) hμ hν hM
  have hs : sqrt ((2:ℝ)*π^2/2) = π := by
    rw [show (2:ℝ)*π^2/2=π^2 by ring, sqrt_sq pi_pos.le]
  norm_num only [Nat.cast_ofNat] at ht
  rw [hs, tensorChebyshevMomentError_comm] at ht
  have hm := wassersteinEDistOne_map_le_mul (normalEmpiricalCoordinateSpectralLaw hA)
    (tensorChebyshevSmoothedLaw (chebyshevCubeLift (normalCoordinateSpectralLaw hA b)) M)
    (K := 1) one_ne_zero Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitz
  simp only [ENNReal.coe_one, one_mul, map_normalEmpiricalCoordinateSpectralLaw_symm] at hm
  exact hm.trans ht

/-- One random start pays the exact explicit radius in the published card for
the native query strategy, outside an event of probability at most `δ`.
atlas: normal-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_normalSpectralDensityProgram_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (hbound : specNorm A ≤ 1)
    {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (complexSphereVector n).real {b |
      ENNReal.ofReal (84/M + π*normalTensorMomentRadius (Fintype.card n) M δ *
        sqrt (5+(π/2)*log M)) <
      wassersteinEDistOne (normalEmpiricalSpectralLaw hA)
        ((normalSpectralDensityProgram b M).run (matrixAdjointOracle A))} ≤ δ := by
  have hsub : ∀ᵐ b : n → ℂ ∂complexSphereVector n, b ∈ {b : n → ℂ |
      ENNReal.ofReal (84/M + π*normalTensorMomentRadius (Fintype.card n) M δ *
        sqrt (5+(π/2)*log M)) <
      wassersteinEDistOne (normalEmpiricalSpectralLaw hA)
        ((normalSpectralDensityProgram b M).run (matrixAdjointOracle A))} →
      b ∈ {b | normalTensorMomentRadius (Fintype.card n) M δ *sqrt (5+(π/2)*log M) <
        tensorChebyshevMomentError (normalCoordinateSpectralLaw hA b)
          (normalEmpiricalCoordinateSpectralLaw hA) M} := by
    filter_upwards [ae_norm_eq_one_complexSphereVector (n := n)] with b hb
    intro hbad
    change ENNReal.ofReal _ < _ at hbad
    by_contra he
    have he' := le_of_not_gt he
    have hw := wassersteinEDistOne_normalSpectralDensityKernelLaw_le hA b hb hbound
      (show 1 ≤ M by omega)
    rw [run_normalSpectralDensityProgram hA b hb hbound] at hbad
    apply (not_lt_of_ge (hw.trans (ENNReal.ofReal_le_ofReal ?_))) hbad
    have hdet : (36:ℝ)/M ≤ 84/M := div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg M)
    have hs := mul_le_mul_of_nonneg_left he' pi_pos.le
    nlinarith
  have hm := ENNReal.toReal_mono (measure_ne_top (complexSphereVector n) _)
    (measure_mono_ae hsub)
  exact hm.trans (measureReal_normalTensorMomentError_radius_gt_le hA hbound (by omega) hδ hδ1)

/-- The native density strategy uses exactly `4M` primitive matrix or adjoint
queries, with all reconstruction performed from the observed finite array.
atlas: normal-spectral-density-query (partial) -/
theorem normalSpectralDensityProgram_queryCount (M : ℕ) :
    hermitianPartChebyshevCost M+hermitianPartChebyshevCost M = 4*M :=
  normalMixedMomentProgram_queryCount M

end NLAlib
