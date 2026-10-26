import NLAlib.RandomMatrix.Gaussian.Spectral.ProfileMaskOperatorMeans
import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfileReindex
import NLAlib.Matrix.Structured.ProfileRearrangementEnvelope

/-!
# Sharp profile upper bound for the Gaussian operator mean

The actual finite permutation, the three-mask decomposition, and invariance
of the symmetric Gaussian law give the source's sharp operator mean profile
for every finite symmetric nonnegative coefficient matrix.
Source: Latała--van Handel--Youssef (2018), Section 3.2, Proposition 3.9.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- The expected spectral norm of an actual symmetric Gaussian profile matrix
is bounded by a universal constant times its maximum row energy plus its
sorted logarithmically weighted row maxima. This includes empty dimensions
and zero profiles, and assumes no rearrangement or Gaussian estimate. -/
theorem integral_specNorm_symmetricGaussianMatrix_le_profile_envelopes
    {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Matrix ι ι ℝ)
    (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j) :
    (∫ G, specNorm (symmetricGaussianMatrix A G) ∂gaussianMatrix ι ι) ≤
      4096 * (profileMaxRowEnergy A + profileLogRowMaximum A) := by
  obtain ⟨e, he⟩ := exists_equiv_entry_le_profile_envelopes A hA hA0
  let B := A.submatrix e e
  have hB : B.IsSymm := by
    ext i j
    exact hA.apply (e i) (e j)
  have hrow (i : Fin (Fintype.card ι)) :
      ∑ j, B i j ^ 2 ≤ profileMaxRowEnergy A ^ 2 := by
    change (∑ j, (fun l => A (e i) l ^ 2) (e j)) ≤ _
    rw [e.sum_comp (fun l => A (e i) l ^ 2)]
    exact sum_row_sq_le_profileMaxRowEnergy_sq A (e i)
  have hmean := integral_specNorm_symmetricGaussianMatrix_le_of_profile_rearrangement
    B hB (profileMaxRowEnergy_nonneg A) (profileLogRowMaximum_nonneg A)
    (fun i j => hA0 (e i) (e j)) hrow (fun k => (he k).1) (fun k => (he k).2)
  simpa only [B, integral_specNorm_symmetricGaussianMatrix_submatrix e A hA] using hmean

end NLAlib
