import NLAlib.RandomMatrix.Haar.UnitaryQR
import NLAlib.RandomMatrix.Haar.HaarQR

/-!
# Existing real Gaussian QR in the generic unitary frame interface

The generic frame is definitionally the existing real positive-diagonal QR
construction. Its actual Haar law therefore agrees exactly, including null-set
fallbacks and zero-column frames.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The real specialization is the existing canonical real QR frame. -/
theorem unitaryQRFrame_real_eq_canonicalQRFrame {n k : ℕ} (hkn : k ≤ n) :
    unitaryQRFrame ℝ n k hkn = canonicalQRFrame n k hkn := rfl

/-- The native real Gaussian measure has the generic actual unitary frame law. -/
theorem gaussianMatrix_map_unitaryQRFrame {n k : ℕ} (hkn : k ≤ n) :
    (gaussianMatrix (Fin n) (Fin k)).map (unitaryQRFrame ℝ n k hkn) =
      unitaryHaarFrameLaw ℝ n k hkn := by
  rw [unitaryQRFrame_real_eq_canonicalQRFrame,unitaryHaarFrameLaw_real_eq_haarFrameLaw]
  exact gaussianMatrix_map_canonicalQRFrame hkn

/-- The actual real Gaussian canonical QR frame has the invariant Stiefel law. -/
theorem hasLaw_unitaryQRFrame_gaussianMatrix {n k : ℕ} (hkn : k ≤ n) :
    HasLaw (unitaryQRFrame ℝ n k hkn) (unitaryHaarFrameLaw ℝ n k hkn)
      (gaussianMatrix (Fin n) (Fin k)) :=
  ⟨(measurable_unitaryQRFrame ℝ n k hkn).aemeasurable,gaussianMatrix_map_unitaryQRFrame hkn⟩

end NLAlib
