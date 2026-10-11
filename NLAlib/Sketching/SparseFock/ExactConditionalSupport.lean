/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.UniformExactSSymmetry
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact-s conditional support moments

True conditional iid laws and symmetry-identification of their support moments.
Ported from `SparseFockFormal.UniformExactSBarycenter` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseStackModel

noncomputable section

/-! ## Exact disintegration -/

/-- Every exactly-s signed column has positive uniform mass.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactColumnWeight_pos {b s : ℕ} (hb : 0 < b)
    (x : ExactColumn (s * b) s) :
    0 < (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x := by
  classical
  let : Nonempty (ExactColumn (s * b) s) :=
    exactColumnNonempty (exactS_le_rows (s := s) hb)
  rw [exactColumnLaw]
  change 0 < 1 / (Fintype.card (ExactColumn (s * b) s) : ℝ)
  positivity

/-- The literal conditional law `Y | X=x`.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def conditionalYLaw {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) : FiniteLaw (NestedY b s) where
  weight y := (jointColumnLaw hb hs).weight (y, x) /
    (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x
  weight_nonneg y := div_nonneg
    ((jointColumnLaw hb hs).weight_nonneg (y, x))
    (exactColumnWeight_pos hb x).le
  sum_weight := by
    rw [← Finset.sum_div]
    change xMarginal hb hs x /
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x = 1
    rw [xMarginal_eq_exactColumnWeight hb hs x]
    exact div_self (ne_of_gt (exactColumnWeight_pos hb x))

/-- The iid law conditional on one exact column is its joint mass divided by the column mass.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem conditionalYLaw_weight {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (x : ExactColumn (s * b) s)
    (y : NestedY b s) :
    (conditionalYLaw hb hs x).weight y =
      (jointColumnLaw hb hs).weight (y, x) /
        (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x := rfl

/-- Bayes identity for one exact-s column.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumn_disintegrates {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (y : NestedY b s) (x : ExactColumn (s * b) s) :
    (jointColumnLaw hb hs).weight (y, x) =
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
        (conditionalYLaw hb hs x).weight y := by
  rw [conditionalYLaw_weight]
  field_simp [ne_of_gt (exactColumnWeight_pos hb x)]

/-- Mixing the conditional laws against the exact-column law recovers the iid
ternary law exactly.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditionalYLaw_mixture {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (y : NestedY b s) :
    (∑ x, (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
      (conditionalYLaw hb hs x).weight y) =
      (nestedYLaw hb s).weight y := by
  simp_rw [← jointColumn_disintegrates hb hs y]
  exact jointColumn_y_marginal hb hs y

/-! ## Support-size observables are independent of the exact column -/

/-- Unnormalized joint fiber expectation of an observable depending only on
the iid support size.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def supportFiberMoment {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (phi : ℕ → ℝ) (x : ExactColumn (s * b) s) : ℝ :=
  ∑ y, (jointColumnLaw hb hs).weight (y, x) * phi (totalSupport y)

/-- The support fiber moment is invariant under transforming its exact-column label.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem supportFiberMoment_transform {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (phi : ℕ → ℝ)
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (x : ExactColumn (s * b) s) :
    supportFiberMoment hb hs phi (transformColumn pi eps x) =
      supportFiberMoment hb hs phi x := by
  calc
    supportFiberMoment hb hs phi (transformColumn pi eps x) =
        ∑ y, (jointColumnLaw hb hs).weight
          (y, transformColumn pi eps x) * phi (totalSupport y) := rfl
    _ = ∑ y, (jointColumnLaw hb hs).weight
          (transformY pi eps y, transformColumn pi eps x) *
            phi (totalSupport (transformY pi eps y)) := by
      exact ((transformYEquiv pi eps).sum_comp
        (fun y => (jointColumnLaw hb hs).weight
          (y, transformColumn pi eps x) * phi (totalSupport y))).symm
    _ = ∑ y, (jointColumnLaw hb hs).weight (y, x) *
          phi (totalSupport y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [jointColumnLaw_weight_transform hb hs, totalSupport_transformY]
    _ = supportFiberMoment hb hs phi x := rfl

/-- The support fiber moment is constant across exact-column labels.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem supportFiberMoment_constant {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (phi : ℕ → ℝ)
    (x z : ExactColumn (s * b) s) :
    supportFiberMoment hb hs phi x = supportFiberMoment hb hs phi z := by
  obtain ⟨pi, eps, h⟩ := exists_transformColumn_eq x z
  rw [← h, supportFiberMoment_transform]

/-- Summing support fiber moments recovers the unconditional support observable expectation.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_supportFiberMoment {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (phi : ℕ → ℝ) :
    (∑ x, supportFiberMoment hb hs phi x) =
      (nestedYLaw hb s).expect (fun y => phi (totalSupport y)) := by
  rw [FiniteLaw.expect]
  calc
    (∑ x, supportFiberMoment hb hs phi x) =
        ∑ y, ∑ x, (jointColumnLaw hb hs).weight (y, x) *
          phi (totalSupport y) := by
      simp only [supportFiberMoment]
      rw [Finset.sum_comm]
    _ = ∑ y, (nestedYLaw hb s).weight y * phi (totalSupport y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_mul, jointColumn_y_marginal]

/-- Each support fiber moment is uniform column mass times the unconditional support expectation.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem supportFiberMoment_eq_weight_mul_expect {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (phi : ℕ → ℝ)
    (x : ExactColumn (s * b) s) :
    supportFiberMoment hb hs phi x =
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x *
        (nestedYLaw hb s).expect (fun y => phi (totalSupport y)) := by
  classical
  let : Nonempty (ExactColumn (s * b) s) :=
    exactColumnNonempty (exactS_le_rows (s := s) hb)
  let N : ℝ := Fintype.card (ExactColumn (s * b) s)
  have hconst : ∀ z : ExactColumn (s * b) s,
      supportFiberMoment hb hs phi z = supportFiberMoment hb hs phi x :=
    fun z => supportFiberMoment_constant hb hs phi z x
  have hN : N * supportFiberMoment hb hs phi x =
      (nestedYLaw hb s).expect (fun y => phi (totalSupport y)) := by
    calc
      N * supportFiberMoment hb hs phi x =
          ∑ _z : ExactColumn (s * b) s,
            supportFiberMoment hb hs phi x := by simp [N]
      _ = ∑ z : ExactColumn (s * b) s,
          supportFiberMoment hb hs phi z := by
        apply Finset.sum_congr rfl
        intro z _
        exact (hconst z).symm
      _ = _ := sum_supportFiberMoment hb hs phi
  rw [exactColumnLaw]
  change supportFiberMoment hb hs phi x =
    (1 / N) * (nestedYLaw hb s).expect (fun y => phi (totalSupport y))
  have hN0 : N ≠ 0 := by
    dsimp [N]
    positivity
  calc
    supportFiberMoment hb hs phi x =
        (nestedYLaw hb s).expect (fun y => phi (totalSupport y)) / N := by
      apply (eq_div_iff hN0).2
      simpa [mul_comm] using hN
    _ = (1 / N) *
        (nestedYLaw hb s).expect (fun y => phi (totalSupport y)) := by
      field_simp [hN0]

/-- The conditional mean of a support-cardinality observable equals its unconditional mean.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_expect_supportFunction {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (phi : ℕ → ℝ)
    (x : ExactColumn (s * b) s) :
    (conditionalYLaw hb hs x).expect (fun y => phi (totalSupport y)) =
      (nestedYLaw hb s).expect (fun y => phi (totalSupport y)) := by
  rw [FiniteLaw.expect]
  simp only [conditionalYLaw_weight]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  change supportFiberMoment hb hs phi x /
      (exactColumnLaw (exactS_le_rows (s := s) hb)).weight x = _
  rw [supportFiberMoment_eq_weight_mul_expect hb hs]
  field_simp [ne_of_gt (exactColumnWeight_pos hb x)]

/-- The conditional mean of support cardinality capped at sparsity equals its unconditional mean.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem conditional_expect_minSupport {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (x : ExactColumn (s * b) s) :
    (conditionalYLaw hb hs x).expect
      (fun y => (min (totalSupport y) s : ℝ)) =
      (s : ℝ) * couplingA (s := s) hb := by
  calc
    (conditionalYLaw hb hs x).expect
        (fun y => (min (totalSupport y) s : ℝ)) =
        (nestedYLaw hb s).expect
          (fun y => (min (totalSupport y) s : ℝ)) := by
      exact conditional_expect_supportFunction hb hs
        (fun k => (min k s : ℝ)) x
    _ = (s : ℝ) * couplingA (s := s) hb := by
      rw [couplingA]
      have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
      field_simp [hsR]

/-! ## Coordinate moments -/

/-- Columns with the same support and the same signs on that support are
indistinguishable to the fill/thin compatibility relation.

Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem compatible_congr_column {b s : ℕ} (y : NestedY b s)
    (x z : ExactColumn (s * b) s)
    (hsupport : (x.1 : Finset (Fin (s * b))) =
      (z.1 : Finset (Fin (s * b))))
    (hsign : ∀ r ∈ (x.1 : Finset (Fin (s * b))), x.2 r = z.2 r) :
    Compatible y x ↔ Compatible y z := by
  classical
  unfold Compatible
  split_ifs with hlarge
  · constructor
    · rintro ⟨hsub, hmatch⟩
      constructor
      · simpa [← hsupport] using hsub
      · intro r hr
        have hrx : r ∈ (x.1 : Finset (Fin (s * b))) := by
          simpa [hsupport] using hr
        simpa [← hsign r hrx] using hmatch r hrx
    · rintro ⟨hsub, hmatch⟩
      constructor
      · simpa [hsupport] using hsub
      · intro r hr
        have hrz : r ∈ (z.1 : Finset (Fin (s * b))) := by
          simpa [← hsupport] using hr
        simpa [hsign r hr] using hmatch r hrz
  · constructor
    · rintro ⟨hsub, hmatch⟩
      constructor
      · simpa [← hsupport] using hsub
      · intro r hr
        have hrx := hsub hr
        simpa [← hsign r hrx] using hmatch r hr
    · rintro ⟨hsub, hmatch⟩
      constructor
      · simpa [hsupport] using hsub
      · intro r hr
        have hrx : r ∈ (x.1 : Finset (Fin (s * b))) := by
          have : r ∈ (z.1 : Finset (Fin (s * b))) := hsub hr
          simpa [← hsupport] using this
        simpa [hsign r hrx] using hmatch r hr

/-- Selection weight depends on an exact column only through its signed coordinate values.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selectionKernel_weight_congr_column {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (y : NestedY b s)
    (x z : ExactColumn (s * b) s)
    (hsupport : (x.1 : Finset (Fin (s * b))) =
      (z.1 : Finset (Fin (s * b))))
    (hsign : ∀ r ∈ (x.1 : Finset (Fin (s * b))), x.2 r = z.2 r) :
    (selectionKernel hb hs y).weight x =
      (selectionKernel hb hs y).weight z := by
  have hc := compatible_congr_column y x z hsupport hsign
  by_cases hxy : Compatible y x
  · have hyz := hc.mp hxy
    rw [selectionKernel_weight_of_compatible hb hs _ _ hxy,
      selectionKernel_weight_of_compatible hb hs _ _ hyz]
  · have hyz : ¬ Compatible y z := by simpa [hc] using hxy
    rw [selectionKernel_weight_of_not_compatible hb hs _ _ hxy,
      selectionKernel_weight_of_not_compatible hb hs _ _ hyz]

/-- Joint-law mass is unchanged when exact columns have equal signed coordinate values.
Source: ported from `SparseFockFormal.UniformExactSBarycenter`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jointColumnLaw_weight_congr_column {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s) (y : NestedY b s)
    (x z : ExactColumn (s * b) s)
    (hsupport : (x.1 : Finset (Fin (s * b))) =
      (z.1 : Finset (Fin (s * b))))
    (hsign : ∀ r ∈ (x.1 : Finset (Fin (s * b))), x.2 r = z.2 r) :
    (jointColumnLaw hb hs).weight (y, x) =
      (jointColumnLaw hb hs).weight (y, z) := by
  change (nestedYLaw hb s).weight y * (selectionKernel hb hs y).weight x =
    (nestedYLaw hb s).weight y * (selectionKernel hb hs y).weight z
  rw [selectionKernel_weight_congr_column hb hs y x z hsupport hsign]

end

end NLAlib.SparseFock.UniformExactS
