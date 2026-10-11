/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactCoordinateSymmetry

set_option autoImplicit false

/-!
# Exact-s conditional coordinate barycenter

The support-moment identity gives the actual conditional scaled iid barycenter.
Ported from `SparseFockFormal.UniformExactSBarycenter` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseStackModel

noncomputable section

/-! ## Exact disintegration -/

/-- Summing coordinate fiber moments against the exact column recovers the
support-size overlap moment.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem weighted_coordinateFiberMoment_eq_minFiber {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) :
    (∑ r, columnValue x r * coordinateFiberMoment hb hs x r) =
      supportFiberMoment hb hs (fun k => (min k s : ℝ)) x := by
  classical
  rw [supportFiberMoment]
  simp only [coordinateFiberMoment]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : Compatible y x
  · have hoverlap := compatible_inner_eq_min hxy
    calc
      (∑ r, columnValue x r *
          ((jointColumnLaw hb hs).weight (y, x) * flatYValue y r)) =
          (jointColumnLaw hb hs).weight (y, x) *
            (∑ r, columnValue x r * flatYValue y r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = (jointColumnLaw hb hs).weight (y, x) *
          (min (totalSupport y) s : ℝ) := by rw [hoverlap]
  · have hk := selectionKernel_weight_of_not_compatible hb hs y x hxy
    have hj : (jointColumnLaw hb hs).weight (y, x) = 0 := by
      change (nestedYLaw hb s).weight y * (selectionKernel hb hs y).weight x = 0
      rw [hk, mul_zero]
    simp [hj]

/-- Weighted active coordinate fiber moments have the stated support-fiber identity.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem weighted_coordinateFiberMoment_eq {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) :
    (∑ r, columnValue x r * coordinateFiberMoment hb hs x r) =
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
        ((s : ℝ) * couplingA (s := s) hb) := by
  rw [weighted_coordinateFiberMoment_eq_minFiber hb hs]
  rw [supportFiberMoment_eq_weight_mul_expect hb hs]
  congr 1
  rw [couplingA]
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  field_simp [hsR]

/-- The support-weighted coordinate moment equals sparsity times one sign-aligned active moment.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem weighted_coordinateFiberMoment_eq_s_mul_active {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r : Fin (s * b))
    (hr : r ∈ (x.1 : Finset (Fin (s * b)))) :
    (∑ t, columnValue x t * coordinateFiberMoment hb hs x t) =
      (s : ℝ) * (columnValue x r * coordinateFiberMoment hb hs x r) := by
  classical
  have hterm (t : Fin (s * b)) :
      columnValue x t * coordinateFiberMoment hb hs x t =
        if t ∈ (x.1 : Finset (Fin (s * b))) then
          columnValue x r * coordinateFiberMoment hb hs x r
        else 0 := by
    by_cases ht : t ∈ (x.1 : Finset (Fin (s * b)))
    · rw [if_pos ht]
      exact (aligned_coordinateFiberMoment_eq hb hs x r t hr ht).symm
    · rw [if_neg ht]
      have ht' : t ∉ x.1 := fun h =>
        ht (Set.powersetCard.mem_coe_iff.mpr h)
      rw [columnValue_of_notMem x ht', zero_mul]
  calc
    (∑ t : Fin (s * b),
        columnValue x t * coordinateFiberMoment hb hs x t) =
        ∑ t : Fin (s * b),
        if t ∈ (x.1 : Finset (Fin (s * b))) then
          columnValue x r * coordinateFiberMoment hb hs x r else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      exact hterm t
    _ =
        ((x.1 : Finset (Fin (s * b))).card : ℝ) *
          (columnValue x r * coordinateFiberMoment hb hs x r) := by simp
    _ = (s : ℝ) *
        (columnValue x r * coordinateFiberMoment hb hs x r) := by
      rw [x.1.prop]

/-- A sign-aligned active coordinate moment equals uniform column mass times the coupling normalization.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem active_aligned_moment_value {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r : Fin (s * b))
    (hr : r ∈ (x.1 : Finset (Fin (s * b)))) :
    columnValue x r * coordinateFiberMoment hb hs x r =
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
        couplingA (s := s) hb := by
  have hsum1 := weighted_coordinateFiberMoment_eq hb hs x
  have hsum2 := weighted_coordinateFiberMoment_eq_s_mul_active hb hs x r hr
  rw [hsum2] at hsum1
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  nlinarith

/-- Every coordinate fiber moment is the coupling normalization times column mass and signed column value.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordinateFiberMoment_eq {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r : Fin (s * b)) :
    coordinateFiberMoment hb hs x r =
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
        couplingA (s := s) hb * columnValue x r := by
  classical
  by_cases hr : r ∈ (x.1 : Finset (Fin (s * b)))
  · have hr' : r ∈ x.1 := Set.powersetCard.mem_coe_iff.mp hr
    have ha := active_aligned_moment_value hb hs x r hr
    rw [columnValue_of_mem x hr'] at ha ⊢
    calc
      coordinateFiberMoment hb hs x r =
          1 * coordinateFiberMoment hb hs x r := by ring
      _ = (x.2 r).val ^ 2 * coordinateFiberMoment hb hs x r := by
        rw [Sign.val_sq]
      _ = ((x.2 r).val * coordinateFiberMoment hb hs x r) *
          (x.2 r).val := by ring
      _ = ((exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
          couplingA (s := s) hb) * (x.2 r).val := by rw [ha]
      _ = _ := by ring
  · have hr' : r ∉ x.1 := fun h =>
        hr (Set.powersetCard.mem_coe_iff.mpr h)
    rw [coordinateFiberMoment_off hb hs x r hr,
      columnValue_of_notMem x hr', mul_zero]

/-- Unscaled coordinate barycenter of the iid ternary column.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_barycenter_coordinate {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r : Fin (s * b)) :
    (conditionalYLaw hb hs x).expect (fun y => flatYValue y r) =
      couplingA (s := s) hb * columnValue x r := by
  rw [FiniteLaw.expect]
  simp only [conditionalYLaw_weight]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  change coordinateFiberMoment hb hs x r /
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x = _
  rw [coordinateFiberMoment_eq hb hs]
  field_simp [ne_of_gt (exactColumnWeight_pos hb x)]

/-- After inverse-coefficient scaling, the conditional barycenter is exactly
the signed exact-s column.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_scaled_barycenter_coordinate {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) (r : Fin (s * b)) :
    (conditionalYLaw hb hs x).expect
      (fun y => exactScale (s := s) hb * flatYValue y r) =
      columnValue x r := by
  rw [FiniteLaw.expect_smul, conditional_barycenter_coordinate hb hs]
  rw [exactScale]
  have ha := couplingA_pos hb hs
  field_simp [ne_of_gt ha]

end

end NLAlib.SparseFock.UniformExactS
