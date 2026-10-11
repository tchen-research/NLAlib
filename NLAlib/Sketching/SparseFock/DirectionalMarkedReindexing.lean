/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.DirectionalMarkedCoefficients

set_option autoImplicit false

/-!
# Directional marked-pair reindexing

Fiber energies and exact equivalences for finite row-pair marks.
Ported from `SparseFockFormal.DirectionalConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace DirectionalConcrete

open ParsevalFrame LocalOperator BandInventory FiniteOperator ExternalOperator
  GlobalBands NamedBands FiniteHilbert
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The nested row/light sum is exactly a sum over the global light-site set.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_rows_light_eq_sum_light (σ : Pattern m n)
    {A : Type*} [AddCommMonoid A] (f : Site m n → A) :
    (∑ r, ∑ c ∈ σ.lightInRow r, f (r, c)) =
      ∑ s ∈ σ.light, f s := by
  classical
  simp only [Pattern.lightInRow, Pattern.light, Finset.sum_filter]
  rw [Fintype.sum_prod_type]

/-- Finite-family Cauchy--Schwarz in the exact Euclidean coordinate model.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normSq_sum_le_card {α : Type*} [DecidableEq α]
    (s : Finset α) (z : α → EVec d) :
    ParsevalFrame.normSq (∑ a ∈ s, z a) ≤
      (s.card : ℝ) * ∑ a ∈ s, ParsevalFrame.normSq (z a) := by
  simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  calc
    (∑ k, (∑ a ∈ s, z a k) * ∑ a ∈ s, z a k) =
        ∑ k, (∑ a ∈ s, z a k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ k, (s.card : ℝ) * ∑ a ∈ s, (z a k) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ a ∈ s, ∑ k, z a k * z a k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The fiber of a full coordinate vector at one Fock pattern.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def fullFiber (v : Fin d × Pattern m n → ℝ) (σ : Pattern m n) : EVec d :=
  WithLp.toLp 2 (fun k ↦ v (k, σ))

/-- The full finite coordinate energy is the sum of its external-fiber energies.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem full_normSq_eq_sum_fiber (v : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq v =
      ∑ σ, ParsevalFrame.normSq (fullFiber v σ) := by
  simp only [FiniteHilbert.normSq, ParsevalFrame.normSq, PiLp.inner_apply,
    Real.inner_apply, fullFiber]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The mixed raising output fiber is its finite sum of marked frame-vector contributions.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_fullFiber (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n) :
    fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) σ =
      ∑ s ∈ σ.light, yPlusMarked F x σ s.1 s.2 := by
  ext k
  rw [show fullFiber (Matrix.mulVec (Yplus m (frameRows F)) x) σ k =
      Matrix.mulVec (Yplus m (frameRows F)) x (k, σ) by rfl]
  rw [Yplus_mulVec_marked]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    sum_rows_light_eq_sum_light σ
      (fun s ↦ yPlusMarked F x σ s.1 s.2 k)

/-- The mixed preserving output fiber is its finite sum of marked frame-vector contributions.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_fullFiber (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n) :
    fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) σ =
      ∑ s ∈ σ.light, yZeroMarked F x σ s.1 s.2 := by
  ext k
  rw [show fullFiber (Matrix.mulVec (Yzero m (frameRows F)) x) σ k =
      Matrix.mulVec (Yzero m (frameRows F)) x (k, σ) by rfl]
  rw [Yzero_mulVec_marked]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    sum_rows_light_eq_sum_light σ
      (fun s ↦ yZeroMarked F x σ s.1 s.2 k)

/-- The heavy correction output fiber is its finite sum of marked frame-vector contributions.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_fullFiber (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n) :
    fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) σ =
      ∑ s ∈ σ.light, hprimeMarked F x σ s.1 s.2 := by
  ext k
  rw [show fullFiber (Matrix.mulVec (Hprime m (frameRows F)) x) σ k =
      Matrix.mulVec (Hprime m (frameRows F)) x (k, σ) by rfl]
  rw [Hprime_mulVec_marked]
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
    sum_rows_light_eq_sum_light σ
      (fun s ↦ hprimeMarked F x σ s.1 s.2 k)

/-- A pattern with an ordered pair of distinct marked columns in one row and
prescribed local output states.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure RowMark (m n : ℕ) (a b : Level) where
  pattern : Pattern m n
  row : Fin m
  left : Fin n
  right : Fin n
  ne : left ≠ right
  left_state : pattern (row, left) = a
  right_state : pattern (row, right) = b
  deriving DecidableEq, Fintype

/-- The columns in one row carrying a prescribed local state.  This generic
version lets the marked-tuple arguments treat fresh, light, and heavy sites
uniformly.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def levelInRow (p : Pattern m n) (r : Fin m) (a : Level) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ p (r, i) = a

/-- A column belongs to a row-level set precisely when that site has the specified level.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem mem_levelInRow {p : Pattern m n} {r : Fin m}
    {a : Level} {i : Fin n} :
    i ∈ levelInRow p r a ↔ p (r, i) = a := by
  simp [levelInRow]

/-- The row-level-zero set is exactly the fresh-site set.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem levelInRow_zero (p : Pattern m n) (r : Fin m) :
    levelInRow p r .zero = p.freshInRow r := by
  ext i
  simp [levelInRow, Pattern.freshInRow]

/-- The row-level-one set is exactly the light-site set.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem levelInRow_one (p : Pattern m n) (r : Fin m) :
    levelInRow p r .one = p.lightInRow r := by
  ext i
  simp [levelInRow, Pattern.lightInRow]

/-- The row-level-two set is exactly the heavy-site set.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem levelInRow_two (p : Pattern m n) (r : Fin m) :
    levelInRow p r .two = p.heavyInRow r := by
  ext i
  simp [levelInRow, Pattern.heavyInRow]

/-- Nested sigma-type presentation of the same marked data.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev NestedRowMark (m n : ℕ) (a b : Level) :=
  Σ p : Pattern m n, Σ r : Fin m,
    Σ i : {i : Fin n // p (r, i) = a},
      {j : Fin n // j ≠ i.1 ∧ p (r, j) = b}

/-- A `RowMark` is precisely a pattern, row, first state-constrained column,
and a distinct second state-constrained column.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rowMarkNestedEquiv (a b : Level) :
    RowMark m n a b ≃ NestedRowMark m n a b where
  toFun z := ⟨z.pattern, z.row, ⟨z.left, z.left_state⟩,
    ⟨z.right, z.ne.symm, z.right_state⟩⟩
  invFun z :=
    { pattern := z.1
      row := z.2.1
      left := z.2.2.1.1
      right := z.2.2.2.1
      ne := z.2.2.2.2.1.symm
      left_state := z.2.2.1.2
      right_state := z.2.2.2.2.2 }
  left_inv z := by
    cases z
    rfl
  right_inv z := by
    rcases z with ⟨p, r, i, j⟩
    rfl

/-- Summing over a finite predicate subtype equals summing over the corresponding filter.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_subtype_eq_filter {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (g : α → ℝ) :
    (∑ x : {x // p x}, g x.1) = ∑ x ∈ Finset.univ.filter p, g x := by
  symm
  exact Finset.sum_subtype (Finset.univ.filter p) (by simp) g

/-- Expands a sum over marked patterns into the paper's row-local nested
sum.  The `erase` is exactly the ordered distinctness condition.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_rowMark_eq_nested (a b : Level)
    (g : Pattern m n → Fin m → Fin n → Fin n → ℝ) :
    (∑ z : RowMark m n a b, g z.pattern z.row z.left z.right) =
      ∑ p, ∑ r, ∑ i ∈ levelInRow p r a,
        ∑ j ∈ (levelInRow p r b).erase i, g p r i j := by
  rw [Fintype.sum_equiv (rowMarkNestedEquiv (m := m) (n := n) a b)
    (fun z ↦ g z.pattern z.row z.left z.right)
    (fun z ↦ g z.1 z.2.1 z.2.2.1.1 z.2.2.2.1) (by intro z; rfl)]
  simp_rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [sum_subtype_eq_filter]
  rw [sum_subtype_eq_filter (fun i : Fin n ↦ p (r, i) = a)
    (fun i ↦ ∑ j ∈ Finset.univ.filter
      (fun j : Fin n ↦ j ≠ i ∧ p (r, j) = b), g p r i j)]
  change (∑ i ∈ levelInRow p r a,
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin n ↦ j ≠ i ∧ p (r, j) = b), g p r i j) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Finset.univ.filter
      (fun j : Fin n ↦ j ≠ i ∧ p (r, j) = b) =
      (levelInRow p r b).erase i by
    ext j
    simp [levelInRow]]

/-- A row-pair mark is determined by its pattern, row, and ordered site labels.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[ext]
theorem rowMark_ext {a b : Level} {x y : RowMark m n a b}
    (hpattern : x.pattern = y.pattern)
    (hrow : x.row = y.row) (hleft : x.left = y.left)
    (hright : x.right = y.right) : x = y := by
  cases x with
  | mk xp xr xl xright xne xleftState xrightState =>
    cases y with
    | mk yp yr yl yright yne yleftState yrightState =>
      dsimp at hpattern hrow hleft hright
      subst yp
      subst yr
      subst yl
      subst yright
      rfl

/-- Restoring the marked pair's original levels undoes a two-site update.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem setPair_restore (p : Pattern m n) {s t : Site m n}
    (hst : s ≠ t) {oa ob ia ib : Level}
    (hs : p s = oa) (ht : p t = ob) :
    setPair (setPair p s ia t ib) s oa t ob = p := by
  funext x
  by_cases hxs : x = s
  · subst x
    simpa [setPair_apply_left _ hst] using hs.symm
  · by_cases hxt : x = t
    · subst x
      simpa using ht.symm
    · rw [setPair_apply_of_ne _ hxs hxt,
        setPair_apply_of_ne _ hxs hxt]

/-- The marked-pattern update is an actual finite equivalence; its inverse
restores the two output states.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rowMarkTransition (oa ob ia ib : Level) :
    RowMark m n oa ob ≃ RowMark m n ia ib where
  toFun z :=
    { pattern := setPair z.pattern (z.row, z.left) ia (z.row, z.right) ib
      row := z.row
      left := z.left
      right := z.right
      ne := z.ne
      left_state := setPair_apply_left z.pattern
        (by intro h; exact z.ne (congrArg Prod.snd h)) ia ib
      right_state := setPair_apply_right z.pattern _ _ ia ib }
  invFun z :=
    { pattern := setPair z.pattern (z.row, z.left) oa (z.row, z.right) ob
      row := z.row
      left := z.left
      right := z.right
      ne := z.ne
      left_state := setPair_apply_left z.pattern
        (by intro h; exact z.ne (congrArg Prod.snd h)) oa ob
      right_state := setPair_apply_right z.pattern _ _ oa ob }
  left_inv z := by
    cases z with
    | mk p r a c hne ha hc =>
      have hp := setPair_restore p
        (by intro h; exact hne (congrArg Prod.snd h))
        (oa := oa) (ob := ob) (ia := ia) (ib := ib) ha hc
      simp only
      apply rowMark_ext
      · exact hp
      · rfl
      · rfl
      · rfl
  right_inv z := by
    cases z with
    | mk p r a c hne ha hc =>
      have hp := setPair_restore p
        (by intro h; exact hne (congrArg Prod.snd h))
        (oa := ia) (ob := ib) (ia := oa) (ib := ob) ha hc
      simp only
      apply rowMark_ext
      · exact hp
      · rfl
      · rfl
      · rfl

/-- Exact multiplicity-one reindexing of any scalar observable along a marked
transition.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_rowMarkTransition (oa ob ia ib : Level)
    (f : RowMark m n ia ib → ℝ) :
    (∑ z : RowMark m n oa ob, f (rowMarkTransition oa ob ia ib z)) =
      ∑ z : RowMark m n ia ib, f z := by
  exact Equiv.sum_comp (rowMarkTransition oa ob ia ib) f

/-- A row-mark transition updates exactly the recorded pair of pattern sites.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rowMarkTransition_pattern (oa ob ia ib : Level)
    (z : RowMark m n oa ob) :
    (rowMarkTransition oa ob ia ib z).pattern =
      setPair z.pattern (z.row, z.left) ia (z.row, z.right) ib := rfl

/-- A row-mark transition retains the second site label.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rowMarkTransition_right (oa ob ia ib : Level)
    (z : RowMark m n oa ob) :
    (rowMarkTransition oa ob ia ib z).right = z.right := rfl

/-- Exact coefficient-square reindexing for `Y₊`; no tuple is dropped or
duplicated.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_marked_reindex (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ z : RowMark m n .two .one,
      (contract F z.right x
        (setPair z.pattern (z.row, z.left) .one
          (z.row, z.right) .zero)) ^ 2) =
      ∑ z : RowMark m n .one .zero,
        (contract F z.right x z.pattern) ^ 2 := by
  simpa only [rowMarkTransition_pattern, rowMarkTransition_right] using
    sum_rowMarkTransition (m := m) (n := n) .two .one .one .zero
      (fun z ↦ (contract F z.right x z.pattern) ^ 2)

/-- Exact coefficient-square reindexing for `Y₀`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_marked_reindex (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ z : RowMark m n .one .one,
      (contract F z.right x
        (setPair z.pattern (z.row, z.left) .two
          (z.row, z.right) .zero)) ^ 2) =
      ∑ z : RowMark m n .two .zero,
        (contract F z.right x z.pattern) ^ 2 := by
  simpa only [rowMarkTransition_pattern, rowMarkTransition_right] using
    sum_rowMarkTransition (m := m) (n := n) .one .one .two .zero
      (fun z ↦ (contract F z.right x z.pattern) ^ 2)

/-- Exact coefficient-square reindexing for the transpose light hop.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_marked_reindex (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ z : RowMark m n .zero .one,
      (contract F z.right x
        (setPair z.pattern (z.row, z.left) .one
          (z.row, z.right) .zero)) ^ 2) =
      ∑ z : RowMark m n .one .zero,
        (contract F z.right x z.pattern) ^ 2 := by
  simpa only [rowMarkTransition_pattern, rowMarkTransition_right] using
    sum_rowMarkTransition (m := m) (n := n) .zero .one .one .zero
      (fun z ↦ (contract F z.right x z.pattern) ^ 2)

end

end DirectionalConcrete

end NLAlib.SparseFock
