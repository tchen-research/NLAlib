import NLAlib.Matrix.Functions.KTransformCongruenceOrder
import NLAlib.Matrix.Functions.PositiveConeStability

/-! # Source K-transform Frobenius stability equivalences -/
noncomputable section
open MeasureTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Invertible whitening transports the actual derivative quadratic test to
strict Hilbert positivity of the actual Frobenius stability operator. -/
theorem matrixKTransform_quadratic_iff
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    (∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
    (∀ x : HermitianFrobenius ℂ n, x≠0 →
      0 < inner ℝ x (x-matrixKStabilityFrobenius ν hν α hα.le S hS hgap x)) := by
  let Q := cfc Real.sqrt S
  let R := cfc (fun x => (Real.sqrt x)⁻¹) S
  have hQ : Q.IsHermitian := cfc_predicate _ _
  have hR : R.IsHermitian := cfc_predicate _ _
  constructor
  · intro h x hx
    let H := hermitianFrobeniusMatrix ℂ n x
    let Δ := Q*H*Q
    have hΔ : Δ.IsHermitian := by
      simpa only [hQ.eq] using Matrix.isHermitian_mul_mul_conjTranspose Q
        (isHermitian_hermitianFrobeniusMatrix x)
    have hΔ0 : Δ≠0 := by
      intro hz
      have he : R*Δ*R=H := invSqrt_sqrt_congruence S hS H
      rw [hz,Matrix.mul_zero,Matrix.zero_mul] at he
      apply hx
      apply (hermitianFrobeniusEquiv ℂ n).injective
      exact Subtype.ext he.symm
    have hp := h Δ hΔ hΔ0
    have he := frobInner_matrixKTransformDeriv ν hν α (ne_of_gt hα) S hS hgap Δ
    dsimp only at he
    rw [invSqrt_sqrt_congruence S hS H] at he
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hα)).mp hp
  · intro h Δ hΔ hΔ0
    let H := R*Δ*R
    have hH : H.IsHermitian := by
      simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hΔ
    let x := toHermitianFrobenius hH
    have hx : x≠0 := by
      intro hz
      have hh := congrArg (hermitianFrobeniusMatrix ℂ n) hz
      change H=0 at hh
      have he : Q*H*Q=Δ := sqrt_invSqrt_congruence S hS Δ
      rw [hh,Matrix.mul_zero,Matrix.zero_mul] at he
      exact hΔ0 he.symm
    have hp := h x hx
    rw [frobInner_matrixKTransformDeriv ν hν α (ne_of_gt hα) S hS hgap Δ]
    exact mul_pos (inv_pos.mpr hα) hp

/-- The derivative's strict Frobenius positivity is equivalent to the actual
Frobenius operator norm being below one. Source (F22).
atlas: matrix-k-transform-stability (partial) -/
theorem matrixKTransform_quadratic_iff_norm_lt_one [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    (∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
    ‖matrixKStabilityFrobenius ν hν α hα.le S hS hgap‖<1 := by
  rw [matrixKTransform_quadratic_iff ν hν α hα S hS hgap]
  exact inner_sub_map_pos_iff_norm_lt_one _
    (isSymmetric_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)
    (posSemidef_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)

/-- The actual Frobenius norm test is equivalent to a strict positive matrix
supersolution, stated on source matrices rather than a surrogate operator. -/
theorem matrixKTransform_norm_iff_supersolution [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    ‖matrixKStabilityFrobenius ν hν α hα.le S hS hgap‖<1 ↔
    ∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y-matrixKStabilityMap ν α S Y).PosDef := by
  have he := (positiveCone_stability_iff
    (matrixKStabilityFrobenius ν hν α hα.le S hS hgap)
    (isSymmetric_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)
    (posSemidef_matrixKStabilityFrobenius ν hν α hα.le S hS hgap)).2
  rw [he]
  constructor
  · rintro ⟨Y,hY,hg⟩
    exact ⟨hermitianFrobeniusMatrix ℂ n Y,hY,hg⟩
  · rintro ⟨Y,hY,hg⟩
    exact ⟨toHermitianFrobenius hY.isHermitian,hY,hg⟩

/-- Positive matrix supersolutions and positive derivative witnesses are
exactly equivalent under actual square-root congruence. Source (F23). -/
theorem matrixKTransform_supersolution_iff_derivative_witness
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    (∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y-matrixKStabilityMap ν α S Y).PosDef) ↔
    ∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S B).PosDef := by
  constructor
  · rintro ⟨Y,hY,hg⟩
    refine ⟨cfc Real.sqrt S*Y*cfc Real.sqrt S,
      (posDef_sqrt_congruence_iff S hS Y).mpr hY,?_⟩
    rw [posDef_matrixKTransformDeriv_iff ν hν α hα S hS hgap,
      invSqrt_sqrt_congruence S hS Y]
    exact hg
  · rintro ⟨B,hB,hg⟩
    exact ⟨_,(posDef_invSqrt_congruence_iff S hS B).mpr hB,
      (posDef_matrixKTransformDeriv_iff ν hν α hα S hS hgap B).mp hg⟩

/-- All four source stability conditions are equivalent for the genuine
compactly supported matrix probability measure and its actual derivative.
Only support points need satisfy the strict denominator gap.
Source: user derivations (F20)--(F23).
atlas: matrix-k-transform-stability -/
theorem matrixKTransform_stability_iff [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : S.val.PosDef)
    (hgap : ∀ T ∈ ν.support, (S.val⁻¹+T.val).PosDef) :
    ((∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0 < frobInner Δ (matrixKTransformDeriv ν α S.val Δ)) ↔
      ‖matrixKStabilityFrobenius ν hν α hα.le S.val hS hgap‖<1) ∧
    (‖matrixKStabilityFrobenius ν hν α hα.le S.val hS hgap‖<1 ↔
      ∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y-matrixKStabilityMap ν α S.val Y).PosDef) ∧
    ((∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y-matrixKStabilityMap ν α S.val Y).PosDef) ↔
      ∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S.val B).PosDef) :=
  ⟨matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S.val hS hgap,
    matrixKTransform_norm_iff_supersolution ν hν α hα S.val hS hgap,
    matrixKTransform_supersolution_iff_derivative_witness ν hν α hα S.val hS hgap⟩

end NLAlib
