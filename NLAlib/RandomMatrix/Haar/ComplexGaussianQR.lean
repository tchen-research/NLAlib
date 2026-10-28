import NLAlib.RandomMatrix.Haar.UnitaryQR
import NLAlib.RandomMatrix.Gaussian.Basic.ComplexFullRank
import NLAlib.RandomMatrix.Gaussian.Basic.ComplexTranspose

/-!
# Native circular complex Gaussian QR has the actual unitary Haar frame law

Transposition preserves the full independent matrix product law. The resulting
almost-sure column rank, unitary invariance and generic QR uniqueness bridge
identify the actual complex Stiefel probability, including rectangular frames.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib

/-- A tall native complex Gaussian matrix has full Hermitian column rank a.s. -/
theorem circularComplexGaussianMatrix_ae_isUnit_conjTranspose_mul {n k : ℕ} (hkn : k ≤ n) :
    ∀ᵐ G ∂circularComplexGaussianMatrix (Fin n) (Fin k), IsUnit (Gᴴ*G) := by
  have h := circularComplexGaussianMatrix_ae_rank_eq hkn
  rw [← (hasLaw_circularComplexGaussianMatrix_transpose n k).map_eq] at h
  have h' := ae_of_ae_map (hasLaw_circularComplexGaussianMatrix_transpose n k).aemeasurable h
  filter_upwards [h'] with G hG
  apply Matrix.isUnit_of_rank_eq_card
  rw [Matrix.rank_conjTranspose_mul_self,Fintype.card_fin]
  simpa only [Matrix.rank_transpose] using hG

/-- The actual complex Gaussian columns are linearly independent almost surely. -/
theorem circularComplexGaussianMatrix_ae_linearIndependent_unitaryQRColumnFamily
    {n k : ℕ} (hkn : k ≤ n) :
    ∀ᵐ G ∂circularComplexGaussianMatrix (Fin n) (Fin k),
      LinearIndependent ℂ (unitaryQRColumnFamily ℂ G) := by
  filter_upwards [circularComplexGaussianMatrix_ae_isUnit_conjTranspose_mul hkn] with G hG
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [gram_unitaryQRColumnFamily]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG)

/-- The canonical rectangular QR of actual complex Gaussian input has the
actual compact unitary Haar frame law, including empty frames.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem circularComplexGaussianMatrix_map_unitaryQRFrame {n k : ℕ} (hkn : k ≤ n) :
    (circularComplexGaussianMatrix (Fin n) (Fin k)).map (unitaryQRFrame ℂ n k hkn) =
      unitaryHaarFrameLaw ℂ n k hkn := by
  apply map_unitaryQRFrame_eq_unitaryHaarFrameLaw ℂ hkn
    (circularComplexGaussianMatrix (Fin n) (Fin k))
    (circularComplexGaussianMatrix_ae_linearIndependent_unitaryQRColumnFamily hkn)
  intro O
  apply hasLaw_mul_circularComplexGaussianMatrix_orthonormalRows O.val
  change O.valᴴᴴ*O.valᴴ=1
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp (conjTranspose_mul_self_unitaryGroup ℂ O)

/-- The actual complex Gaussian canonical QR frame has normalized unitary Haar law. -/
theorem hasLaw_unitaryQRFrame_circularComplexGaussianMatrix {n k : ℕ} (hkn : k ≤ n) :
    HasLaw (unitaryQRFrame ℂ n k hkn) (unitaryHaarFrameLaw ℂ n k hkn)
      (circularComplexGaussianMatrix (Fin n) (Fin k)) :=
  ⟨(measurable_unitaryQRFrame ℂ n k hkn).aemeasurable,circularComplexGaussianMatrix_map_unitaryQRFrame hkn⟩

end NLAlib
