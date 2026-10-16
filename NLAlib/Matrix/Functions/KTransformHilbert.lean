import NLAlib.Matrix.Functions.KTransformPositivity
import NLAlib.Matrix.Norms.HermitianFrobenius

/-! # The actual K stability operator in the real Frobenius Hilbert space -/
noncomputable section
open MeasureTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual averaged K stability map, restricted and equipped with its
source Frobenius norm. Its matrix action is unchanged. -/
def matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n :=
  hermitianFrobeniusMap (matrixKStabilityMap ν α S).toLinearMap
    (fun _ h => isHermitian_matrixKStabilityMap ν hν α hα S hS hgap h)

/-- Realization is exactly the source integral operator. -/
@[simp] theorem matrixKStabilityFrobenius_apply
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) (x : HermitianFrobenius ℂ n) :
    hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν hν α hα S hS hgap x) =
      matrixKStabilityMap ν α S (hermitianFrobeniusMatrix ℂ n x) := rfl

/-- The actual Frobenius operator is symmetric. -/
theorem isSymmetric_matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    (matrixKStabilityFrobenius ν hν α hα S hS hgap).IsSymmetric := by
  intro x y
  change frobInner (matrixKStabilityMap ν α S (hermitianFrobeniusMatrix ℂ n x))
    (hermitianFrobeniusMatrix ℂ n y) = frobInner (hermitianFrobeniusMatrix ℂ n x)
    (matrixKStabilityMap ν α S (hermitianFrobeniusMatrix ℂ n y))
  exact (frobInner_matrixKStabilityMap_comm ν hν α S hS hgap _ _).symm

/-- The actual Frobenius operator preserves the source PSD cone. -/
theorem posSemidef_matrixKStabilityFrobenius
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 ≤ α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (x : HermitianFrobenius ℂ n) (hx : (hermitianFrobeniusMatrix ℂ n x).PosSemidef) :
    (hermitianFrobeniusMatrix ℂ n (matrixKStabilityFrobenius ν hν α hα S hS hgap x)).PosSemidef := by
  rw [matrixKStabilityFrobenius_apply]
  exact posSemidef_matrixKStabilityMap ν hν α hα S hS hgap hx

/-- The actual derivative restricts to the real Hermitian space. -/
theorem isHermitian_matrixKTransformDeriv
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    {Δ : Matrix n n ℂ} (hΔ : Δ.IsHermitian) :
    (matrixKTransformDeriv ν α S Δ).IsHermitian := by
  let R := cfc (fun x => (Real.sqrt x)⁻¹) S
  have hR : R.IsHermitian := cfc_predicate _ _
  have hH : (R*Δ*R).IsHermitian := by
    simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hΔ
  have hD := hH.sub (isHermitian_matrixKStabilityMap ν hν α hα.le S hS hgap hH)
  rw [matrixKTransformDeriv_eq_congruence ν hν α (ne_of_gt hα) S hS hgap Δ]
  have hh : (R * (R*Δ*R-matrixKStabilityMap ν α S (R*Δ*R)) * R).IsHermitian := by
    simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hD
  exact hh.smul (IsSelfAdjoint.all (α⁻¹))

end NLAlib
