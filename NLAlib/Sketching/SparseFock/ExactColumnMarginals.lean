/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactSelectionSymmetry

set_option autoImplicit false

/-!
# Uniform exact-s column marginal

The transitive column action and normalization identify the true uniform exact-s marginal.
Ported from `SparseFockFormal.UniformExactSSymmetry` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseStackModel

noncomputable section

/-! ## The signed coordinate action -/

/-- The joint iid/exact-column law is invariant under joint signed coordinate permutations.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumnLaw_weight_transform {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) (x : ExactColumn (s * b) s) :
    (jointColumnLaw hb hs).weight
        (transformY pi eps y, transformColumn pi eps x) =
      (jointColumnLaw hb hs).weight (y, x) := by
  change (nestedYLaw hb s).weight (transformY pi eps y) *
      (selectionKernel hb hs (transformY pi eps y)).weight
        (transformColumn pi eps x) =
      (nestedYLaw hb s).weight y * (selectionKernel hb hs y).weight x
  rw [nestedYLaw_weight_transformY hb,
    selectionKernel_weight_transform hb hs]

/-! ## Uniform exact-column marginal -/

/-- Positive block size ensures exact sparsity does not exceed total row count.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactS_le_rows {b s : ℕ} (hb : 0 < b) : s ≤ s * b := by
  nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hb)]

/-- Any two literal exact columns are related by a signed row permutation,
including their redundant off-support signs.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exists_transformColumn_eq {m s : ℕ}
    (x z : ExactColumn m s) :
    ∃ (pi : Equiv.Perm (Fin m)) (eps : Fin m → Sign),
      transformColumn pi eps x = z := by
  classical
  obtain ⟨pi, hpi⟩ := Equiv.Perm.exists_map_finset_eq
    (x.1 : Finset (Fin m)) (z.1 : Finset (Fin m)) (by
      rw [x.1.prop, z.1.prop])
  let eps : Fin m → Sign := fun r => signMul (z.2 r) (x.2 (pi.symm r))
  refine ⟨pi, eps, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact hpi
  · funext r
    simp [transformColumn, eps]

/-- The second-coordinate fiber mass of the joint one-column law.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def xMarginal {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) : ℝ :=
  ∑ y, (jointColumnLaw hb hs).weight (y, x)

/-- The exact-column marginal is invariant under signed coordinate permutations.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_transform {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (x : ExactColumn (s * b) s) :
    xMarginal hb hs (transformColumn pi eps x) = xMarginal hb hs x := by
  calc
    xMarginal hb hs (transformColumn pi eps x) =
        ∑ y, (jointColumnLaw hb hs).weight
          (y, transformColumn pi eps x) := rfl
    _ = ∑ y, (jointColumnLaw hb hs).weight
          (transformY pi eps y, transformColumn pi eps x) := by
      exact ((transformYEquiv pi eps).sum_comp
        (fun y => (jointColumnLaw hb hs).weight
          (y, transformColumn pi eps x))).symm
    _ = ∑ y, (jointColumnLaw hb hs).weight (y, x) := by
      apply Finset.sum_congr rfl
      intro y _
      exact jointColumnLaw_weight_transform hb hs pi eps y x
    _ = xMarginal hb hs x := rfl

/-- Every exactly-s signed column has the same joint marginal mass.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_constant {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (x z : ExactColumn (s * b) s) :
    xMarginal hb hs x = xMarginal hb hs z := by
  obtain ⟨pi, eps, h⟩ := exists_transformColumn_eq x z
  rw [← h, xMarginal_transform]

/-- The exactly-s column marginal masses sum to one.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_xMarginal {b s : ℕ} (hb : 0 < b) (hs : 0 < s) :
    ∑ x, xMarginal hb hs x = 1 := by
  calc
    (∑ x, xMarginal hb hs x) =
        ∑ y, ∑ x, (jointColumnLaw hb hs).weight (y, x) := by
      simp only [xMarginal]
      exact Finset.sum_comm
    _ = ∑ z : NestedY b s × ExactColumn (s * b) s,
        (jointColumnLaw hb hs).weight z := by
      rw [Fintype.sum_prod_type]
    _ = 1 := (jointColumnLaw hb hs).sum_weight

/-- The fill/thin coupling has the literal uniform signed exact-s marginal.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem xMarginal_eq_exactColumnWeight {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (x : ExactColumn (s * b) s) :
    xMarginal hb hs x =
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x := by
  classical
  let : Nonempty (ExactColumn (s * b) s) :=
    exactColumnNonempty (exactS_le_rows (s := s) hb)
  have hconst : ∀ z : ExactColumn (s * b) s,
      xMarginal hb hs z = xMarginal hb hs x :=
    fun z => xMarginal_constant hb hs z x
  have hsum : (Fintype.card (ExactColumn (s * b) s) : ℝ) *
      xMarginal hb hs x = 1 := by
    calc
      (Fintype.card (ExactColumn (s * b) s) : ℝ) * xMarginal hb hs x =
          ∑ _z : ExactColumn (s * b) s, xMarginal hb hs x := by simp
      _ = ∑ z : ExactColumn (s * b) s, xMarginal hb hs z := by
        apply Finset.sum_congr rfl
        intro z _
        exact (hconst z).symm
      _ = 1 := sum_xMarginal hb hs
  rw [exactColumnLaw]
  change xMarginal hb hs x = 1 / (Fintype.card (ExactColumn (s * b) s) : ℝ)
  apply (eq_div_iff (by positivity :
    (Fintype.card (ExactColumn (s * b) s) : ℝ) ≠ 0)).2
  nlinarith

/-- The first-coordinate marginal is the nested iid law, directly from the
fact that every selection kernel has total mass one.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumn_y_marginal {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (y : NestedY b s) :
    (∑ x, (jointColumnLaw hb hs).weight (y, x)) =
      (nestedYLaw hb s).weight y := by
  change (∑ x, (nestedYLaw hb s).weight y *
    (selectionKernel hb hs y).weight x) = _
  rw [← Finset.mul_sum, (selectionKernel hb hs y).sum_weight, mul_one]

end

end NLAlib.SparseFock.UniformExactS
