import NLAlib.Polynomial.OrthogonalPolynomials.AlphaSensitivity
import NLAlib.Polynomial.OrthogonalPolynomials.BetaSensitivity
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional
import NLAlib.Matrix.Perturbation.MapConditioning

/-!
# The actual moment-to-recurrence map and its Jacobian

Finite fixed polynomial coordinates parameterize the moment functional. The
output contains all requested diagonals followed by mass and positive-order
monic subdiagonals. The mass slot is separate from the zero recurrence boundary.
Source: Gautschi (2004), §2.1; AQ28–AQ31 in the operator re-derivations.
-/

noncomputable section
open Polynomial
namespace NLAlib

set_option backward.isDefEq.respectTransparency false

/-- The recurrence data map for fixed polynomial moment coordinates. -/
def momentRecurrenceMap {d : ℕ} (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) (n : ℕ)
    (m : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin n ⊕ Fin n) :=
  WithLp.toLp 2 (fun s =>
    let L := coordinateMomentFunctional c m.ofLp
    Sum.elim (fun i : Fin n => orthogonalRecurrenceAlpha L i.val)
      (fun i : Fin n => if i.val = 0 then L 1 else orthogonalRecurrenceBeta L i.val) s)

/-- The explicit sensitivity matrix in the declared alpha-then-beta output order. -/
def momentSensitivityMatrix {d : ℕ} (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) (n : ℕ)
    (m : EuclideanSpace ℝ (Fin d)) : Matrix (Fin n ⊕ Fin n) (Fin d) ℝ :=
  fun s k =>
    let L := coordinateMomentFunctional c m.ofLp
    Sum.elim (fun i : Fin n => c k (orthogonalRecurrenceAlphaSensitivityPolynomial L i.val))
      (fun i : Fin n => if i.val = 0 then c k 1 else
        c k (orthogonalRecurrenceBetaSensitivityPolynomial L i.val)) s

private theorem contDiff_coordinateMomentFunctional_ofLp_apply {d : ℕ}
    (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) (p : ℝ[X]) :
    ContDiff ℝ 1 (fun m : EuclideanSpace ℝ (Fin d) => coordinateMomentFunctional c m.ofLp p) :=
  (contDiff_coordinateMomentFunctional_apply c p).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff

/-- The actual finite moment-to-recurrence map is smooth on each positive
finite Hankel system, without requiring nearby representing measures.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem contDiffAt_momentRecurrenceMap {d n : ℕ}
    (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) {m : EuclideanSpace ℝ (Fin d)}
    (hM : (hankelMomentMatrix (coordinateMomentFunctional c m.ofLp) n).PosDef) :
    ContDiffAt ℝ 1 (momentRecurrenceMap c n) m := by
  have hL : ∀ k, ContDiffAt ℝ 1
      (fun v : EuclideanSpace ℝ (Fin d) => coordinateMomentFunctional c v.ofLp (X ^ k)) m :=
    fun k => (contDiff_coordinateMomentFunctional_ofLp_apply c (X ^ k)).contDiffAt
  have hraw : ContDiffAt ℝ 1 (fun v : EuclideanSpace ℝ (Fin d) =>
      fun s : Fin n ⊕ Fin n =>
        Sum.elim (fun i : Fin n => orthogonalRecurrenceAlpha (coordinateMomentFunctional c v.ofLp) i.val)
          (fun i : Fin n => if i.val = 0 then coordinateMomentFunctional c v.ofLp 1 else
            orthogonalRecurrenceBeta (coordinateMomentFunctional c v.ofLp) i.val) s) m := by
    apply contDiffAt_pi.mpr
    intro s
    cases s with
    | inl i =>
      exact contDiffAt_orthogonalRecurrenceAlpha hL
        (hankelMomentDet_ne_zero_of_posDef_of_le hM i.isLt.le)
        (orthogonalPolynomialNorm_pos_of_posDef hM i.isLt).ne'
    | inr i =>
      by_cases hi : i.val = 0
      · simp only [Sum.elim_inr, hi]
        exact (contDiff_coordinateMomentFunctional_ofLp_apply c 1).contDiffAt
      · simp only [Sum.elim_inr, if_neg hi]
        exact contDiffAt_orthogonalRecurrenceBeta hL
          (hankelMomentDet_ne_zero_of_posDef_of_le hM i.isLt.le)
          (hankelMomentDet_ne_zero_of_posDef_of_le hM (by have := i.isLt; omega))
          (orthogonalPolynomialNorm_pos_of_posDef hM (by have := i.isLt; omega)).ne'
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ⊕ Fin n => ℝ)).symm.contDiff.contDiffAt.comp m hraw

/-- The actual Euclidean Jacobian of the moment-to-recurrence map is the
fixed-coordinate sensitivity matrix, including the separate mass row.
Source: AQ31. For a fixed polynomial basis, take `c` to be its dual coordinates.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem euclideanJacobian_momentRecurrenceMap_eq {d n : ℕ}
    (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) {m : EuclideanSpace ℝ (Fin d)}
    (hM : (hankelMomentMatrix (coordinateMomentFunctional c m.ofLp) n).PosDef) :
    euclideanJacobian (momentRecurrenceMap c n) m = momentSensitivityMatrix c n m := by
  let L := coordinateMomentFunctional c m.ofLp
  have hf := (contDiffAt_momentRecurrenceMap c hM).differentiableAt (by norm_num)
  have hline (t : ℝ) (k : Fin d) :
      coordinateMomentFunctional c (m + t • EuclideanSpace.single k 1).ofLp = L + t • c k := by
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.ofLp_single] using
      coordinateMomentFunctional_add_smul_single c m.ofLp t k
  ext s k
  rw [euclideanJacobian_apply_eq_deriv hf]
  cases s with
  | inl i =>
    have h := hasDerivAt_orthogonalRecurrenceAlpha_affine L (c k) i.val
      (fun j hj => hankelMomentDet_ne_zero_of_posDef_of_le hM (by have := i.isLt; omega))
      (orthogonalPolynomialNorm_pos_of_posDef hM i.isLt).ne'
    simpa only [momentRecurrenceMap, PiLp.toLp_apply, Sum.elim_inl, hline,
      momentSensitivityMatrix, L] using h.deriv
  | inr i =>
    by_cases hi : i.val = 0
    · have h : HasDerivAt (fun t : ℝ => (L + t • c k) 1) (c k 1) 0 := by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        convert (hasDerivAt_const 0 (L 1)).fun_add ((hasDerivAt_id 0).mul_const (c k 1)) using 1
        all_goals first | rfl | simp
      simpa only [momentRecurrenceMap, PiLp.toLp_apply, Sum.elim_inr, hi, ite_true,
        hline, momentSensitivityMatrix, L] using h.deriv
    · have h := hasDerivAt_orthogonalRecurrenceBeta_affine L (c k)
        (show 0 < i.val by omega)
        (hankelMomentDet_ne_zero_of_posDef_of_le hM i.isLt.le)
        (hankelMomentDet_ne_zero_of_posDef_of_le hM (by have := i.isLt; omega))
        (orthogonalPolynomialNorm_pos_of_posDef hM i.isLt).ne'
        (orthogonalPolynomialNorm_pos_of_posDef hM (by have := i.isLt; omega)).ne'
      simpa only [momentRecurrenceMap, PiLp.toLp_apply, Sum.elim_inr, if_neg hi,
        hline, momentSensitivityMatrix, L] using h.deriv

/-- The absolute local condition number is the spectral norm of the actual
moment sensitivity matrix. Source: AQ31, Gautschi (2004), Definition 2.3.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem mapAbsCondition_momentRecurrenceMap_eq_specNorm {d n : ℕ}
    (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) {m : EuclideanSpace ℝ (Fin d)}
    (hM : (hankelMomentMatrix (coordinateMomentFunctional c m.ofLp) n).PosDef) :
    mapAbsCondition (momentRecurrenceMap c n) m = specNorm (momentSensitivityMatrix c n m) := by
  rw [← specNorm_euclideanJacobian
    ((contDiffAt_momentRecurrenceMap c hM).differentiableAt (by norm_num)),
    euclideanJacobian_momentRecurrenceMap_eq c hM]

/-- The normwise relative local condition number includes both the input and
output normalization factors. Source: Gautschi (2004), Definition 2.4.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem mapNormRelativeCondition_momentRecurrenceMap_eq {d n : ℕ}
    (c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)) {m : EuclideanSpace ℝ (Fin d)}
    (hM : (hankelMomentMatrix (coordinateMomentFunctional c m.ofLp) n).PosDef) :
    mapNormRelativeCondition (momentRecurrenceMap c n) m =
      specNorm (momentSensitivityMatrix c n m) * ‖m‖ / ‖momentRecurrenceMap c n m‖ := by
  rw [mapNormRelativeCondition, mapAbsCondition_momentRecurrenceMap_eq_specNorm c hM]

end NLAlib
