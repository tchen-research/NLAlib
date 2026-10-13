import NLAlib.RandomMatrix.Haar.HaarFrameMeasure
import NLAlib.Matrix.Subspaces.CanonicalQR
import NLAlib.RandomMatrix.Gaussian.Moments.SecondMoment
import NLAlib.RandomMatrix.Gaussian.Invariance.Invariance
/-!
# Gaussian canonical QR has the Haar frame law

The actual positive-diagonal QR map is measurable, is equivariant on the
full-rank set, and that set has full Gaussian probability. Haar/Tonelli
uniqueness therefore proves its full rectangular Stiefel pushforward law.
Source: operator re-derivation `sh:gaussian-qr`.
Atlas: `haar-orthogonal`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- A tall standard Gaussian matrix has linearly independent Euclidean columns
almost surely, including zero columns. Source: operator re-derivation
`sh:gaussian-qr`, via the proved nonzero Gram determinant null-set theorem. -/
theorem gaussianMatrix_ae_linearIndependent_qrColumnFamily {n k : ℕ} (hkn : k ≤ n) :
    ∀ᵐ G ∂gaussianMatrix (Fin n) (Fin k), LinearIndependent ℝ (qrColumnFamily G) := by
  filter_upwards [gaussianMatrix_ae_isUnit_transpose_mul hkn] with G hG
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [gram_qrColumnFamily]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG)

/-- Canonical Gaussian QR has the actual invariant Haar probability law on
the entire rectangular Stiefel frame space, including empty frames. The map
uses positive-diagonal QR on full rank and its explicit coordinate fallback
only on a proved Gaussian null set.
Source: operator re-derivation `sh:gaussian-qr` and `sh:haar-unique`.
atlas: haar-orthogonal -/
theorem gaussianMatrix_map_canonicalQRFrame {n k : ℕ} (hkn : k ≤ n) :
    (gaussianMatrix (Fin n) (Fin k)).map (canonicalQRFrame n k hkn) = haarFrameLaw n k hkn := by
  let ν := (gaussianMatrix (Fin n) (Fin k)).map (canonicalQRFrame n k hkn)
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_canonicalQRFrame n k hkn).aemeasurable
  apply measure_eq_haarFrameLaw_of_invariant hkn ν
  intro O
  let T : Matrix (Fin n) (Fin k) ℝ → Matrix (Fin n) (Fin k) ℝ := fun G => O.val * G
  have hT : Measurable T := measurable_const.matrix_mul measurable_id
  have hrot : HasLaw T (gaussianMatrix (Fin n) (Fin k)) (gaussianMatrix (Fin n) (Fin k)) := by
    have hh := hasLaw_gaussianMatrix_orthogonal O.val (1 : Matrix (Fin k) (Fin k) ℝ)
      (transpose_mul_self_orthogonalGroup O) (by simp [HasOrthonormalCols])
    simpa only [Matrix.mul_one, T] using hh
  have heq : (fun G => O • canonicalQRFrame n k hkn G) =ᵐ[gaussianMatrix (Fin n) (Fin k)]
      (fun G => canonicalQRFrame n k hkn (T G)) := by
    filter_upwards [gaussianMatrix_ae_linearIndependent_qrColumnFamily hkn] with G hG
    exact (canonicalQRFrame_orthogonal_mul hkn O G hG).symm
  change ν.map (fun Q => O • Q) = ν
  dsimp only [ν]
  rw [Measure.map_map (by fun_prop) (measurable_canonicalQRFrame n k hkn)]
  change (gaussianMatrix (Fin n) (Fin k)).map (fun G => O • canonicalQRFrame n k hkn G) = _
  rw [Measure.map_congr heq]
  change (gaussianMatrix (Fin n) (Fin k)).map ((canonicalQRFrame n k hkn) ∘ T) = _
  rw [← Measure.map_map (measurable_canonicalQRFrame n k hkn) hT, hrot.map_eq]

/-- `gaussianMatrix_map_canonicalQRFrame` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin n) (Fin k)) μ`: its canonical QR frame has the Haar frame law.
Atlas: `haar-orthogonal`. -/
theorem gaussianMatrix_map_canonicalQRFrame_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n k : ℕ} {X : Ω → Matrix (Fin n) (Fin k) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin n) (Fin k)) μ) (hkn : k ≤ n) :
    HasLaw (fun ω => canonicalQRFrame n k hkn (X ω)) (haarFrameLaw n k hkn) μ :=
  (⟨(measurable_canonicalQRFrame n k hkn).aemeasurable,
    gaussianMatrix_map_canonicalQRFrame hkn⟩ :
    HasLaw (canonicalQRFrame n k hkn) (haarFrameLaw n k hkn) (gaussianMatrix (Fin n) (Fin k))).comp
    hX

/-- The square Stiefel frame is an element of Mathlib's actual orthogonal group.
Source: operator re-derivation `sh:gaussian-qr`, square case. -/
def stiefelSquareToOrthogonal {n : ℕ} (Q : Stiefel n n) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨Q.val, Matrix.mem_unitaryGroup_iff'.mpr (by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (show Q.valᵀ * Q.val = 1 from Q.property))⟩

/-- The square-frame identification with the orthogonal group is continuous.
Source: operator re-derivation `sh:gaussian-qr`, finite-dimensional linear maps. -/
theorem continuous_stiefelSquareToOrthogonal (n : ℕ) :
    Continuous (stiefelSquareToOrthogonal (n := n)) :=
  continuous_subtype_val.subtype_mk _

/-- Acting on the full coordinate frame returns the same orthogonal group
element under the square identification. Source: operator re-derivation `sh:haar`. -/
theorem stiefelSquareToOrthogonal_smul_coordinate {n : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    stiefelSquareToOrthogonal (O • coordinateStiefel n n le_rfl) = O := by
  apply Subtype.ext
  change O.val * (coordinateStiefel n n le_rfl).val = O.val
  have hcoord : (coordinateStiefel n n le_rfl).val =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [coordinateStiefel, Matrix.one_apply]
  rw [hcoord, Matrix.mul_one]

/-- The square Haar frame law identifies with actual orthogonal-group Haar
probability. Source: operator re-derivation `sh:haar`. -/
theorem haarFrameLaw_map_stiefelSquareToOrthogonal (n : ℕ) :
    (haarFrameLaw n n le_rfl).map stiefelSquareToOrthogonal = orthogonalHaar n := by
  unfold haarFrameLaw
  rw [Measure.map_map (continuous_stiefelSquareToOrthogonal n).measurable (by fun_prop)]
  have heq : stiefelSquareToOrthogonal ∘
      (fun O => O • coordinateStiefel n n le_rfl) = id := by
    funext O
    exact stiefelSquareToOrthogonal_smul_coordinate O
  rw [heq, Measure.map_id]

/-- The square canonical positive-diagonal Gaussian QR factor has the actual
normalized Haar law on Mathlib's orthogonal group, including dimension zero.
Source: operator re-derivation `sh:gaussian-qr`.
atlas: haar-orthogonal -/
theorem gaussianMatrix_map_canonicalQR_orthogonal (n : ℕ) :
    (gaussianMatrix (Fin n) (Fin n)).map
      (fun G => stiefelSquareToOrthogonal (canonicalQRFrame n n le_rfl G)) = orthogonalHaar n := by
  change (gaussianMatrix (Fin n) (Fin n)).map
    (stiefelSquareToOrthogonal ∘ canonicalQRFrame n n le_rfl) = _
  rw [← Measure.map_map (continuous_stiefelSquareToOrthogonal n).measurable
    (measurable_canonicalQRFrame n n le_rfl), gaussianMatrix_map_canonicalQRFrame,
    haarFrameLaw_map_stiefelSquareToOrthogonal]

/-- `gaussianMatrix_map_canonicalQR_orthogonal` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin n) (Fin n)) μ`: its square canonical QR factor has the normalized
Haar law on the orthogonal group. Atlas: `haar-orthogonal`. -/
theorem gaussianMatrix_map_canonicalQR_orthogonal_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin n) (Fin n)) μ) :
    HasLaw (fun ω => stiefelSquareToOrthogonal (canonicalQRFrame n n le_rfl (X ω)))
      (orthogonalHaar n) μ :=
  (⟨((continuous_stiefelSquareToOrthogonal n).measurable.comp
      (measurable_canonicalQRFrame n n le_rfl)).aemeasurable,
    gaussianMatrix_map_canonicalQR_orthogonal n⟩ :
    HasLaw (fun G => stiefelSquareToOrthogonal (canonicalQRFrame n n le_rfl G)) (orthogonalHaar n)
      (gaussianMatrix (Fin n) (Fin n))).comp hX

end NLAlib
