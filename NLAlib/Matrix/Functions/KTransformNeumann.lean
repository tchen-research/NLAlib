import NLAlib.Matrix.Functions.KTransformStability

/-! # The actual K-transform Neumann inverse and its canonical supersolution -/
noncomputable section
open MeasureTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Below the actual Frobenius norm threshold, the true inverse of `I-L`
preserves the PSD cone, and its value on the identity is a positive
supersolution dominating the identity with exactly unit gap. The inverse is
also the convergent Neumann series by `hermitianNeumannInverse_eq_inverse`.
Source: user derivations (F23).
atlas: matrix-k-transform-stability (partial) -/
theorem matrixKTransform_neumann_of_norm_lt_one
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : S.val.PosDef)
    (hgap : ∀ T ∈ ν.support, (S.val⁻¹+T.val).PosDef)
    (hnorm : ‖matrixKStabilityFrobenius ν hν α hα.le S.val hS hgap‖<1) :
    let L := matrixKStabilityFrobenius ν hν α hα.le S.val hS hgap
    let I := toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)
    let Y := Ring.inverse (1-L) I
    (∀ x : HermitianFrobenius ℂ n, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (Ring.inverse (1-L) x)).PosSemidef) ∧
    (hermitianFrobeniusMatrix ℂ n Y).PosDef ∧
      (1 : Matrix n n ℂ) ≤ hermitianFrobeniusMatrix ℂ n Y ∧
      hermitianFrobeniusMatrix ℂ n (Y-L Y)=1 := by
  let L := matrixKStabilityFrobenius ν hν α hα.le S.val hS hgap
  let I := toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)
  have hc := posSemidef_matrixKStabilityFrobenius ν hν α hα.le S.val hS hgap
  change (∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
    (hermitianFrobeniusMatrix ℂ n (Ring.inverse (1-L) x)).PosSemidef) ∧
    (hermitianFrobeniusMatrix ℂ n (Ring.inverse (1-L) I)).PosDef ∧
    (1 : Matrix n n ℂ) ≤ hermitianFrobeniusMatrix ℂ n (Ring.inverse (1-L) I) ∧
    hermitianFrobeniusMatrix ℂ n (Ring.inverse (1-L) I-L (Ring.inverse (1-L) I))=1
  rw [← hermitianNeumannInverse_eq_inverse L hnorm]
  have hge := one_le_hermitianNeumannInverse_one L hc hnorm
  have hpd : (hermitianFrobeniusMatrix ℂ n (hermitianNeumannInverse L I)).PosDef := by
    have hp := Matrix.PosDef.one.add_posSemidef (Matrix.le_iff.mp hge)
    simpa only [add_sub_cancel] using hp
  refine ⟨fun x hx => posSemidef_hermitianNeumannInverse L hc hnorm hx,hpd,hge,?_⟩
  rw [hermitianNeumannInverse_sub_map L hnorm I]
  rfl

end NLAlib
