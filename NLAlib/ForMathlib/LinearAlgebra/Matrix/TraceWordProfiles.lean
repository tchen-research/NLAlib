import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic trace profiles for ordered words in two commuting generators

The exact monoid factorization and elementary count invariants
compute cyclic arcs in two commuting generators. A structural
`none` coefficient means identity; `some tag` always retains its coefficient,
even if its actual matrix equals identity. Only the two generators
commute. Coefficients never move past each other or past a resolvent.

Source: ordered common-resolvent expansions supporting Brailovskaya--van Handel,
arXiv:2201.05142v3, Lemma 6.9. Supports
independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
namespace List

private abbrev Arc := ℕ × ℕ
private abbrev TaggedBlock (κ : Type*) := Bool × Option κ
private abbrev ArcSegment (κ : Type*) := κ × Arc

private def arcLength (s : Arc) : ℕ := s.1 + s.2
private def prependArc (mode : Bool) (s : Arc) : Arc :=
  if mode then (s.1, s.2 + 1) else (s.1 + 1, s.2)
private def singletonArc (mode : Bool) : Arc := prependArc mode (0, 0)
private def addArc (s t : Arc) : Arc := (s.1 + t.1, s.2 + t.2)

private def arcValue {B : Type*} [Monoid B] (X Y : B) (s : Arc) : B := X ^ s.1 * Y ^ s.2
private def modeValue {B : Type*} (X Y : B) (mode : Bool) : B := if mode then Y else X
private def blockValue {B κ : Type*} [Monoid B] (X Y : B) (C : κ → B)
    (b : TaggedBlock κ) : B := modeValue X Y b.1 * b.2.elim 1 C
private def segmentValue {B κ : Type*} [Monoid B] (X Y : B) (C : κ → B)
    (s : ArcSegment κ) : B := C s.1 * arcValue X Y s.2

private def splitTaggedBlocks {κ : Type*} : List (TaggedBlock κ) → Arc × List (ArcSegment κ)
  | [] => ((0, 0), [])
  | (mode, c) :: w =>
    let t := splitTaggedBlocks w
    match c with
    | none => (prependArc mode t.1, t.2)
    | some tag => (singletonArc mode, (tag, t.1) :: t.2)

private theorem arcLength_prependArc (mode : Bool) (s : Arc) :
    arcLength (prependArc mode s) = arcLength s + 1 := by
  cases mode <;> simp [arcLength, prependArc] <;> omega

private theorem arcLength_singletonArc (mode : Bool) : arcLength (singletonArc mode) = 1 := by
  rw [singletonArc, arcLength_prependArc]
  rfl

private theorem arcValue_singletonArc {B : Type*} [Monoid B] (X Y : B) (mode : Bool) :
    arcValue X Y (singletonArc mode) = modeValue X Y mode := by
  cases mode <;> simp [arcValue, singletonArc, prependArc, modeValue]

private theorem arcValue_prependArc {B : Type*} [Monoid B] {X Y : B}
    (hXY : Commute X Y) (mode : Bool) (s : Arc) :
    arcValue X Y (prependArc mode s) = modeValue X Y mode * arcValue X Y s := by
  cases mode with
  | false => simp [arcValue, prependArc, modeValue, pow_succ', mul_assoc]
  | true =>
    change X ^ s.1 * Y ^ (s.2 + 1) = Y * (X ^ s.1 * Y ^ s.2)
    rw [pow_succ']
    calc
      X ^ s.1 * (Y * Y ^ s.2) = (X ^ s.1 * Y) * Y ^ s.2 := (mul_assoc _ _ _).symm
      _ = (Y * X ^ s.1) * Y ^ s.2 :=
        congrArg (fun t => t * Y ^ s.2) (hXY.pow_left s.1).eq
      _ = Y * (X ^ s.1 * Y ^ s.2) := mul_assoc _ _ _

private theorem arcValue_addArc {B : Type*} [Monoid B] {X Y : B}
    (hXY : Commute X Y) (s t : Arc) :
    arcValue X Y (addArc s t) = arcValue X Y s * arcValue X Y t := by
  simp only [arcValue, addArc, pow_add]
  calc
    (X ^ s.1 * X ^ t.1) * (Y ^ s.2 * Y ^ t.2) =
        X ^ s.1 * ((X ^ t.1 * Y ^ s.2) * Y ^ t.2) := by simp only [mul_assoc]
    _ = X ^ s.1 * ((Y ^ s.2 * X ^ t.1) * Y ^ t.2) :=
      congrArg (fun z => X ^ s.1 * (z * Y ^ t.2)) (hXY.pow_pow t.1 s.2).eq
    _ = (X ^ s.1 * Y ^ s.2) * (X ^ t.1 * Y ^ t.2) := by simp only [mul_assoc]

/-- The actual ordered monoid factorization of the computed compression.
Only adjacent X/Y factors are collected; no coefficient commutation occurs. -/
private theorem eval_splitTaggedBlocks {B κ : Type*} [Monoid B] {X Y : B}
    (hXY : Commute X Y) (C : κ → B) (w : List (TaggedBlock κ)) :
    (w.map (blockValue X Y C)).prod =
      arcValue X Y (splitTaggedBlocks w).1 *
        ((splitTaggedBlocks w).2.map (segmentValue X Y C)).prod := by
  induction w with
  | nil => simp [splitTaggedBlocks, arcValue]
  | cons b w ih =>
    obtain ⟨mode, c⟩ := b
    cases c with
    | none =>
      simp only [List.map_cons, List.prod_cons, blockValue, Option.elim_none, mul_one]
      change modeValue X Y mode * (w.map (blockValue X Y C)).prod =
        arcValue X Y (prependArc mode (splitTaggedBlocks w).1) *
          ((splitTaggedBlocks w).2.map (segmentValue X Y C)).prod
      rw [ih, arcValue_prependArc hXY, mul_assoc]
    | some tag =>
      simp only [List.map_cons, List.prod_cons, blockValue, Option.elim_some]
      change (modeValue X Y mode * C tag) * (w.map (blockValue X Y C)).prod =
        arcValue X Y (singletonArc mode) *
          (C tag * arcValue X Y (splitTaggedBlocks w).1 *
            ((splitTaggedBlocks w).2.map (segmentValue X Y C)).prod)
      rw [ih, arcValue_singletonArc]
      simp only [mul_assoc]

private theorem length_segments_splitTaggedBlocks {κ : Type*} (w : List (TaggedBlock κ)) :
    (splitTaggedBlocks w).2.length = (w.filter (fun b => b.2.isSome)).length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    obtain ⟨mode, c⟩ := b
    cases c <;> simp [splitTaggedBlocks, ih]

private theorem totalArcLength_splitTaggedBlocks {κ : Type*} (w : List (TaggedBlock κ)) :
    arcLength (splitTaggedBlocks w).1 +
      (((splitTaggedBlocks w).2.map (fun s => arcLength s.2)).sum) = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    obtain ⟨mode, c⟩ := b
    cases c with
    | none =>
      change arcLength (prependArc mode (splitTaggedBlocks w).1) +
        (((splitTaggedBlocks w).2.map (fun s => arcLength s.2)).sum) = w.length + 1
      rw [arcLength_prependArc]
      omega
    | some tag =>
      change arcLength (singletonArc mode) +
        (arcLength (splitTaggedBlocks w).1 +
          (((splitTaggedBlocks w).2.map (fun s => arcLength s.2)).sum)) = w.length + 1
      rw [arcLength_singletonArc]
      omega

private def closeSegments {κ : Type*} (lead : Arc) : List (ArcSegment κ) → List (ArcSegment κ)
  | [] => []
  | [(tag, s)] => [(tag, addArc s lead)]
  | s :: t :: w => s :: closeSegments lead (t :: w)

private theorem eval_closeSegments {B κ : Type*} [Monoid B] {X Y : B}
    (hXY : Commute X Y) (C : κ → B) (lead : Arc)
    (s : List (ArcSegment κ)) (hs : s ≠ []) :
    ((closeSegments lead s).map (segmentValue X Y C)).prod =
      (s.map (segmentValue X Y C)).prod * arcValue X Y lead := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons t s ih =>
    cases s with
    | nil =>
      obtain ⟨tag, a⟩ := t
      simp [closeSegments, segmentValue, arcValue_addArc hXY, mul_assoc]
    | cons u s =>
      simp only [closeSegments, List.map_cons, List.prod_cons]
      rw [ih (by simp)]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

private theorem arcLength_addArc (s t : Arc) :
    arcLength (addArc s t) = arcLength s + arcLength t := by
  simp only [arcLength, addArc]
  omega

private theorem leadingArc_pos_of_ne_nil {κ : Type*} (w : List (TaggedBlock κ)) (hw : w ≠ []) :
    0 < arcLength (splitTaggedBlocks w).1 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons b w =>
    obtain ⟨mode, c⟩ := b
    cases c with
    | none =>
      change 0 < arcLength (prependArc mode (splitTaggedBlocks w).1)
      rw [arcLength_prependArc]
      omega
    | some tag =>
      change 0 < arcLength (singletonArc mode)
      rw [arcLength_singletonArc]
      decide

private def positiveInternalArcs {κ : Type*} : List (ArcSegment κ) → Prop
  | [] => True
  | [_] => True
  | s :: t :: w => 0 < arcLength s.2 ∧ positiveInternalArcs (t :: w)

private theorem positiveInternalArcs_splitTaggedBlocks {κ : Type*} (w : List (TaggedBlock κ)) :
    positiveInternalArcs (splitTaggedBlocks w).2 := by
  induction w with
  | nil => trivial
  | cons b w ih =>
    obtain ⟨mode, c⟩ := b
    cases c with
    | none => exact ih
    | some tag =>
      change positiveInternalArcs ((tag, (splitTaggedBlocks w).1) :: (splitTaggedBlocks w).2)
      cases ht : (splitTaggedBlocks w).2 with
      | nil => trivial
      | cons t s =>
        have hw : w ≠ [] := by
          intro hw
          subst w
          simp [splitTaggedBlocks] at ht
        exact ⟨leadingArc_pos_of_ne_nil w hw, by simpa only [ht] using ih⟩

private theorem map_tags_closeSegments {κ : Type*} (lead : Arc) (s : List (ArcSegment κ)) :
    (closeSegments lead s).map Prod.fst = s.map Prod.fst := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    cases s with
    | nil => rfl
    | cons u s =>
      simp only [closeSegments, List.map_cons]
      exact congrArg (List.cons t.1) ih

private theorem totalArcLength_closeSegments {κ : Type*} (lead : Arc)
    (s : List (ArcSegment κ)) (hs : s ≠ []) :
    ((closeSegments lead s).map (fun t => arcLength t.2)).sum =
      (s.map (fun t => arcLength t.2)).sum + arcLength lead := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons t s ih =>
    cases s with
    | nil =>
      obtain ⟨tag, a⟩ := t
      simp [closeSegments, arcLength_addArc]
    | cons u s =>
      simp only [closeSegments, List.map_cons, List.sum_cons]
      rw [ih (by simp)]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

private theorem positiveArcs_closeSegments {κ : Type*} (lead : Arc)
    (hLead : 0 < arcLength lead) (s : List (ArcSegment κ))
    (hs : positiveInternalArcs s) :
    ∀ t ∈ closeSegments lead s, 0 < arcLength t.2 := by
  induction s with
  | nil => simp [closeSegments]
  | cons t s ih =>
    cases s with
    | nil =>
      intro u hu
      simp only [closeSegments, List.mem_singleton] at hu
      subst u
      rw [arcLength_addArc]
      omega
    | cons u s =>
      obtain ⟨ht, hrest⟩ := hs
      intro v hv
      simp only [closeSegments, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ht
      · exact ih hrest v hv

private theorem segments_ne_nil_of_marked {κ : Type*} (w : List (TaggedBlock κ))
    (hMarked : 0 < (w.filter (fun b => b.2.isSome)).length) :
    (splitTaggedBlocks w).2 ≠ [] := by
  intro hs
  have hc := length_segments_splitTaggedBlocks w
  rw [hs, List.length_nil] at hc
  omega

/-- The actual computed cyclic closure preserves every coefficient tag,
accounts for every resolvent, and makes every arc strictly positive. -/
private theorem closedSegments_spec {κ : Type*} (w : List (TaggedBlock κ))
    (hMarked : 0 < (w.filter (fun b => b.2.isSome)).length) :
    let c := closeSegments (splitTaggedBlocks w).1 (splitTaggedBlocks w).2
    c.length = (w.filter (fun b => b.2.isSome)).length ∧
      (c.map (fun t => arcLength t.2)).sum = w.length ∧
      (∀ t ∈ c, 0 < arcLength t.2) := by
  have hs := segments_ne_nil_of_marked w hMarked
  have hw : w ≠ [] := by intro hw; subst w; simp at hMarked
  dsimp only
  constructor
  · have ht := congrArg List.length
      (map_tags_closeSegments (splitTaggedBlocks w).1 (splitTaggedBlocks w).2)
    simpa only [List.length_map, length_segments_splitTaggedBlocks] using ht
  constructor
  · rw [totalArcLength_closeSegments _ _ hs, Nat.add_comm]
    exact totalArcLength_splitTaggedBlocks w
  · exact positiveArcs_closeSegments _ (leadingArc_pos_of_ne_nil w hw) _
      (positiveInternalArcs_splitTaggedBlocks w)

/-- This is an exact matrix trace identity for the computed ordered blocks,
not a supplied cyclic-decomposition hypothesis. -/
private theorem trace_eval_closedSegments {𝕜 n κ : Type*} [CommSemiring 𝕜]
    [Fintype n] [DecidableEq n] {X Y : Matrix n n 𝕜} (hXY : Commute X Y)
    (C : κ → Matrix n n 𝕜) (w : List (TaggedBlock κ))
    (hMarked : 0 < (w.filter (fun b => b.2.isSome)).length) :
    (w.map (blockValue X Y C)).prod.trace =
      (((closeSegments (splitTaggedBlocks w).1 (splitTaggedBlocks w).2).map
        (segmentValue X Y C)).prod).trace := by
  have hs := segments_ne_nil_of_marked w hMarked
  rw [eval_splitTaggedBlocks hXY C w, Matrix.trace_mul_comm,
    eval_closeSegments hXY C _ _ hs]

private def markedCount {κ : Type*} {N : ℕ} (w : Fin N → TaggedBlock κ) : ℕ :=
  ∑ j, if (w j).2.isSome then 1 else 0

private theorem length_filter_eq_sum_marks {κ : Type*} (w : List (TaggedBlock κ)) :
    (w.filter (fun b => b.2.isSome)).length =
      (w.map (fun b => if b.2.isSome then 1 else 0)).sum := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    obtain ⟨mode, c⟩ := b
    cases c with
    | none => simp [ih]
    | some tag =>
      simp [ih]
      omega

private theorem length_filter_ofFn_eq_markedCount {κ : Type*} {N : ℕ}
    (w : Fin N → TaggedBlock κ) :
    ((List.ofFn w).filter (fun b => b.2.isSome)).length = markedCount w := by
  rw [length_filter_eq_sum_marks, List.map_ofFn, Fin.sum_ofFn]
  rfl

private def profileBlock {κ : Type*} {N : ℕ} (w : Fin N → TaggedBlock κ)
    (m : Fin N → ℕ) (j : Fin N) : List (TaggedBlock (κ ⊕ Fin N)) :=
  List.replicate (m j) ((w j).1, some (Sum.inr j)) ++
    [((w j).1, (w j).2.map Sum.inl)]

private def profileBlocks {κ : Type*} {N : ℕ} (w : Fin N → TaggedBlock κ)
    (m : Fin N → ℕ) : List (TaggedBlock (κ ⊕ Fin N)) :=
  (List.ofFn (profileBlock w m)).flatten

private theorem length_profileBlocks {κ : Type*} {N : ℕ}
    (w : Fin N → TaggedBlock κ) (m : Fin N → ℕ) :
    (profileBlocks w m).length = N + ∑ j, m j := by
  simp only [profileBlocks, List.length_flatten, List.map_ofFn, Function.comp_def,
    profileBlock, List.length_append, List.length_replicate, List.length_singleton,
    Fin.sum_ofFn, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

private theorem length_filter_flatten {α : Type*} (f : α → Bool) (w : List (List α)) :
    (w.flatten.filter f).length = (w.map (fun t => (t.filter f).length)).sum := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    change ((t ++ w.flatten).filter f).length =
      (t.filter f).length + (w.map (fun t => (t.filter f).length)).sum
    rw [List.filter_append, List.length_append, ih]

private theorem markedCount_profileBlocks {κ : Type*} {N : ℕ}
    (w : Fin N → TaggedBlock κ) (m : Fin N → ℕ) :
    ((profileBlocks w m).filter (fun b => b.2.isSome)).length =
      markedCount w + ∑ j, m j := by
  have hblock (j : Fin N) :
      ((profileBlock w m j).filter (fun b => b.2.isSome)).length =
        m j + (if (w j).2.isSome then 1 else 0) := by
    cases hc : (w j).2 <;> simp [profileBlock, hc]
  rw [profileBlocks, length_filter_flatten, List.map_ofFn, Fin.sum_ofFn]
  simp only [Function.comp_def]
  simp_rw [hblock]
  rw [Finset.sum_add_distrib]
  simp only [markedCount, Nat.add_comm]

/-- This exact identity keeps every correction in its original Neumann block. -/
private theorem eval_profileBlocks {B κ : Type*} [Monoid B] (X Y : B)
    {N : ℕ} (w : Fin N → TaggedBlock κ) (m : Fin N → ℕ)
    (C : κ → B) (H : Fin N → B) :
    ((profileBlocks w m).map (blockValue X Y (Sum.elim C H))).prod =
      (List.ofFn (fun j => (modeValue X Y (w j).1 * H j) ^ m j *
        modeValue X Y (w j).1 * (w j).2.elim 1 C)).prod := by
  have hblock (j : Fin N) :
      ((profileBlock w m j).map (blockValue X Y (Sum.elim C H))).prod =
        (modeValue X Y (w j).1 * H j) ^ m j *
          modeValue X Y (w j).1 * (w j).2.elim 1 C := by
    cases hc : (w j).2 <;> simp [profileBlock, blockValue, hc, mul_assoc]
  simp only [profileBlocks, List.map_flatten, List.prod_flatten,
    List.map_ofFn, Function.comp_def]
  exact congrArg (fun f : Fin N → B => (List.ofFn f).prod) (funext hblock)

/-- Computed cyclic arcs and coefficient labels for an actual ordered Neumann
profile. This data depends only on structural tags and the profile, before any
matrix interpretation or summand-family index is supplied. A `some` tag is
retained even when its interpreted coefficient is zero or identity. -/
def cyclicProfileArcs {κ : Type*} {N : ℕ} (w : Fin N → Bool × Option κ)
    (m : Fin N → ℕ) : List ((κ ⊕ Fin N) × (ℕ × ℕ)) :=
  closeSegments (splitTaggedBlocks (profileBlocks w m)).1
    (splitTaggedBlocks (profileBlocks w m)).2

/-- The computed profile has one coefficient per original marked slot and per
Neumann insertion, accounts for every resolvent, and has positive cyclic arcs. -/
theorem cyclicProfileArcs_spec {κ : Type*} {N : ℕ}
    (w : Fin N → Bool × Option κ) (m : Fin N → ℕ)
    (hMarked : 0 < ((List.ofFn w).filter (fun b => b.2.isSome)).length) :
    (cyclicProfileArcs w m).length =
        ((List.ofFn w).filter (fun b => b.2.isSome)).length + ∑ j, m j ∧
      ((cyclicProfileArcs w m).map (fun s => s.2.1 + s.2.2)).sum = N + ∑ j, m j ∧
      (∀ s ∈ cyclicProfileArcs w m, 0 < s.2.1 + s.2.2) := by
  have hMarks : 0 < markedCount w := by
    rw [← length_filter_ofFn_eq_markedCount]
    exact hMarked
  have hProfile : 0 < ((profileBlocks w m).filter (fun b => b.2.isSome)).length := by
    rw [markedCount_profileBlocks]
    exact hMarks.trans_le (Nat.le_add_right _ _)
  obtain ⟨hlen, hdegree, hpos⟩ := closedSegments_spec (profileBlocks w m) hProfile
  dsimp only [cyclicProfileArcs]
  refine ⟨?_, ?_, hpos⟩
  · rw [hlen, markedCount_profileBlocks, ← length_filter_ofFn_eq_markedCount]
  · simpa only [arcLength, length_profileBlocks] using hdegree

/-- The same structurally computed arcs give the exact profile trace for all
matrix coefficient interpretations. Only the two generators commute; no
coefficient is moved across a matrix. -/
theorem _root_.Matrix.trace_profile_word_eq_cyclicProfileArcs
    {𝕜 n κ : Type*} [CommSemiring 𝕜] [Fintype n] [DecidableEq n]
    {X Y : Matrix n n 𝕜} (hXY : Commute X Y) {N : ℕ}
    (w : Fin N → Bool × Option κ) (m : Fin N → ℕ)
    (hMarked : 0 < ((List.ofFn w).filter (fun b => b.2.isSome)).length)
    (C : κ → Matrix n n 𝕜) (H : Fin N → Matrix n n 𝕜) :
    (List.ofFn (fun j => ((if (w j).1 then Y else X) * H j) ^ m j *
      (if (w j).1 then Y else X) * (w j).2.elim 1 C)).prod.trace =
      ((cyclicProfileArcs w m).map (fun s =>
        Sum.elim C H s.1 * (X ^ s.2.1 * Y ^ s.2.2))).prod.trace := by
  have hMarks : 0 < markedCount w := by
    rw [← length_filter_ofFn_eq_markedCount]
    exact hMarked
  have hProfile : 0 < ((profileBlocks w m).filter (fun b => b.2.isSome)).length := by
    rw [markedCount_profileBlocks]
    exact hMarks.trans_le (Nat.le_add_right _ _)
  change (List.ofFn (fun j => (modeValue X Y (w j).1 * H j) ^ m j *
    modeValue X Y (w j).1 * (w j).2.elim 1 C)).prod.trace = _
  rw [← eval_profileBlocks X Y w m C H]
  exact trace_eval_closedSegments hXY (Sum.elim C H) (profileBlocks w m) hProfile

end List
