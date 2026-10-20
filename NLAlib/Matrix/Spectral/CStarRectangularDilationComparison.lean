import NLAlib.Matrix.Spectral.CStarRectangularDilationPositive
import NLAlib.ForMathlib.Topology.MetricSpace.PositiveSquareHausdorff

/-! # Positive-gap rectangular dilation comparison

The actual positive row-Gram spectral sets inherit a quantitative
Hausdorff comparison from their Hermitian dilations. The positive gap
excludes matching to the dilation's extra zero spectrum. Arbitrary
C*-algebra entries retain continuous free spectra.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {m n A B : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Under an actual strict spectral gap, the entire row-Gram spectrum
is the square-image of the positive part of the actual dilation spectrum. -/
theorem spectrum_real_rowGram_eq_sq_positive_dilation
    (Y : Matrix m n A) (hgap : ∀ r ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)), 0 < r) :
    spectrum ℝ (ofMatrix (Y * Yᴴ)) =
      (fun r : ℝ => r ^ 2) '' (spectrum ℝ (rectangularDilation Y) ∩ Set.Ioi 0) := by
  ext r
  constructor
  · intro hr
    have hr0 := hgap r hr
    exact ⟨Real.sqrt r, ⟨(sqrt_mem_spectrum_real_rectangularDilation_iff Y hr0).mpr hr,
      Real.sqrt_pos.mpr hr0⟩, Real.sq_sqrt hr0.le⟩
  · rintro ⟨s, ⟨hs, hs0⟩, rfl⟩
    exact (mem_spectrum_real_rectangularDilation_iff_sq_mem_rowGram Y hs0).mp hs

variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Nonempty m] [Nontrivial A] [Nontrivial B]

/-- Actual rectangular row-Gram spectra inherit the sharp deterministic
squaring modulus from a dilation comparison, provided both positive
spectra have gap `4δ²`. The reference radius uses only the true reference
row-Gram norm. Source: arXiv:2406.11453v2, Section 5.3.
atlas: gaussian-quadratic-free-spectrum (partial). -/
theorem hausdorffDist_spectrum_rowGram_le_of_dilation_gap
    (Y : Matrix m n A) (Z : Matrix m n B) {δ : ℝ} (hδ : 0 < δ)
    (hgapY : ∀ r ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)), 4 * δ ^ 2 ≤ r)
    (hgapZ : ∀ r ∈ spectrum ℝ (ofMatrix (Z * Zᴴ)), 4 * δ ^ 2 ≤ r)
    (hd : Metric.hausdorffDist (spectrum ℝ (rectangularDilation Y))
      (spectrum ℝ (rectangularDilation Z)) ≤ δ) :
    Metric.hausdorffDist (spectrum ℝ (ofMatrix (Y * Yᴴ)))
      (spectrum ℝ (ofMatrix (Z * Zᴴ))) ≤
        2 * δ * Real.sqrt ‖ofMatrix (Z * Zᴴ)‖ + δ ^ 2 := by
  have hposY : ∀ r ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)), 0 < r := by
    intro r hr
    exact lt_of_lt_of_le (by positivity) (hgapY r hr)
  have hposZ : ∀ r ∈ spectrum ℝ (ofMatrix (Z * Zᴴ)), 0 < r := by
    intro r hr
    exact lt_of_lt_of_le (by positivity) (hgapZ r hr)
  rw [spectrum_real_rowGram_eq_sq_positive_dilation Y hposY,
    spectrum_real_rowGram_eq_sq_positive_dilation Z hposZ]
  apply Metric.hausdorffDist_sq_positive_le_of_gap
    (spectrum.isCompact _) (spectrum.isCompact _)
    (ContinuousFunctionalCalculus.spectrum_nonempty _ (isSelfAdjoint_rectangularDilation Y))
    (ContinuousFunctionalCalculus.spectrum_nonempty _ (isSelfAdjoint_rectangularDilation Z))
    hδ (Real.sqrt_nonneg _)
  · intro r hr hr0
    have hs := hgapY (r ^ 2)
      ((mem_spectrum_real_rectangularDilation_iff_sq_mem_rowGram Y hr0).mp hr)
    nlinarith
  · intro r hr hr0
    have hs := hgapZ (r ^ 2)
      ((mem_spectrum_real_rectangularDilation_iff_sq_mem_rowGram Z hr0).mp hr)
    nlinarith
  · intro r hr hr0
    have hs := spectrum.norm_le_norm_of_mem
      ((mem_spectrum_real_rectangularDilation_iff_sq_mem_rowGram Z hr0).mp hr)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)] at hs
    have hsqrt := Real.sq_sqrt (norm_nonneg (ofMatrix (Z * Zᴴ)))
    have hnonneg := Real.sqrt_nonneg ‖ofMatrix (Z * Zᴴ)‖
    nlinarith
  · exact hd

end CStarMatrix
