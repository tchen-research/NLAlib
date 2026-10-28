import NLAlib.RandomMatrix.Haar.UnitaryFrameMeasure
import NLAlib.Matrix.Subspaces.UnitaryCanonicalQR
import Mathlib.Probability.HasLaw

/-!
# Unitary-invariant full-rank input gives the actual Haar QR frame law

This native law bridge applies over the real or complex field. Its hypotheses
concern the original matrix distribution and its full-rank set, rather than a
claimed Stiefel output law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- A full-rank unitary-invariant matrix law has the actual normalized Haar
Stiefel pushforward under the measurable canonical QR map.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem map_unitaryQRFrame_eq_unitaryHaarFrameLaw {n k : ℕ} (hkn : k ≤ n)
    (ν : Measure (Matrix (Fin n) (Fin k) 𝕜)) [IsProbabilityMeasure ν]
    (hfull : ∀ᵐ G ∂ν, LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 G))
    (hinv : ∀ O : Matrix.unitaryGroup (Fin n) 𝕜,
      HasLaw (fun G : Matrix (Fin n) (Fin k) 𝕜 => O.val*G) ν ν) :
    ν.map (unitaryQRFrame 𝕜 n k hkn) = unitaryHaarFrameLaw 𝕜 n k hkn := by
  let η := ν.map (unitaryQRFrame 𝕜 n k hkn)
  have : IsProbabilityMeasure η :=
    Measure.isProbabilityMeasure_map (measurable_unitaryQRFrame 𝕜 n k hkn).aemeasurable
  apply measure_eq_unitaryHaarFrameLaw_of_invariant 𝕜 hkn η
  intro O
  let T : Matrix (Fin n) (Fin k) 𝕜 → Matrix (Fin n) (Fin k) 𝕜 := fun G => O.val*G
  have hT : Measurable T := measurable_const.matrix_mul measurable_id
  have heq : (fun G => O • unitaryQRFrame 𝕜 n k hkn G) =ᵐ[ν]
      (fun G => unitaryQRFrame 𝕜 n k hkn (T G)) := by
    filter_upwards [hfull] with G hG
    exact (unitaryQRFrame_unitary_mul 𝕜 hkn O G hG).symm
  change η.map (fun Q => O • Q) = η
  dsimp only [η]
  rw [Measure.map_map (by fun_prop) (measurable_unitaryQRFrame 𝕜 n k hkn)]
  change ν.map (fun G => O • unitaryQRFrame 𝕜 n k hkn G) = _
  rw [Measure.map_congr heq]
  change ν.map ((unitaryQRFrame 𝕜 n k hkn) ∘ T) = _
  rw [← Measure.map_map (measurable_unitaryQRFrame 𝕜 n k hkn) hT,(hinv O).map_eq]

end NLAlib
