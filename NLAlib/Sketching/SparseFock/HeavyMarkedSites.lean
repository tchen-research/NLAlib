/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.NamedBands
import NLAlib.Sketching.SparseFock.FiniteHilbert
import NLAlib.Sketching.SparseFock.TypedBlockCS
import NLAlib.Sketching.SparseFock.ParsevalFrame
import NLAlib.Sketching.SparseFock.ConcreteLadder
import NLAlib.Sketching.SparseFock.DirectionalConcrete
import NLAlib.Sketching.SparseFock.MatrixTail
import NLAlib.Sketching.SparseFock.BandCoefficientBounds
import NLAlib.Sketching.SparseFock.BandEnvelope
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Marked heavy-site transitions

Finite marked-site replacements, equivalences, and occupation counting.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The row-local occupation grade used in the heavy-leg argument.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rowGrade (p : Pattern m n) (r : Fin m) : ℕ :=
  (p.lightInRow r).card + 2 * (p.heavyInRow r).card

/-- Summing the row occupation grades gives the total pattern grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_rowGrade (p : Pattern m n) :
    (∑ r, rowGrade p r) = p.grade := by
  classical
  simp only [rowGrade, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Pattern.card_light_eq_sum_card_lightInRow,
    ← Pattern.card_heavy_eq_sum_card_heavyInRow,
    Pattern.grade_eq_card_light_add_two_mul_card_heavy]

/-- Replace the level at one concrete site.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def setSite (p : Pattern m n) (s : Site m n) (a : Level) : Pattern m n :=
  Function.update p s a

/-- Replacing one site gives the specified level at that site.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem setSite_apply_self (p : Pattern m n) (s : Site m n) (a : Level) :
    setSite p s a s = a := by
  simp [setSite]

/-- Replacing one site leaves every distinct site unchanged.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem setSite_apply_of_ne (p : Pattern m n) {s t : Site m n}
    (hst : t ≠ s) (a : Level) :
    setSite p s a t = p t := by
  simp [setSite, hst]

/-- Restoring the original level undoes a marked-site replacement.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem setSite_restore (p : Pattern m n) (s : Site m n) {a b : Level}
    (hs : p s = a) : setSite (setSite p s b) s a = p := by
  funext t
  by_cases h : t = s
  · subst t
    simpa using hs.symm
  · simp [setSite, h]

/-- A marked-site replacement agrees with the original pattern outside that site.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem agreesOutsideSite_setSite (p : Pattern m n) (s : Site m n) (a : Level) :
    agreesOutsideSite s p (setSite p s a) := by
  intro t hts
  symm
  exact setSite_apply_of_ne p hts a

/-- Equality to a marked-site replacement is determined by the outside pattern and marked level.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem eq_setSite_iff {out inp : Pattern m n} {s : Site m n} (a : Level) :
    inp = setSite out s a ↔ agreesOutsideSite s out inp ∧ inp s = a := by
  constructor
  · rintro rfl
    exact ⟨agreesOutsideSite_setSite out s a, setSite_apply_self out s a⟩
  · rintro ⟨hout, hs⟩
    funext t
    by_cases hts : t = s
    · subst t
      simpa using hs
    · rw [setSite_apply_of_ne out hts]
      exact (hout t hts).symm

/-- Exact coefficient of a lifted one-site rank-one transition.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem siteKernel_ketBra_apply (s : Site m n) (outLevel inpLevel : Level)
    (out inp : Pattern m n) :
    siteKernel s (ketBra outLevel inpLevel) out inp =
      if out s = outLevel ∧ inp = setSite out s inpLevel then 1 else 0 := by
  classical
  simp only [siteKernel, ketBra]
  by_cases hoff : agreesOutsideSite s out inp
  · rw [if_pos hoff]
    by_cases ho : out s = outLevel
    · have heq : inp = setSite out s inpLevel ↔ inp s = inpLevel := by
        rw [eq_setSite_iff]
        simp [hoff]
      by_cases hi : inp s = inpLevel
      · simp [ho, heq.mpr hi]
      · have hne : inp ≠ setSite out s inpLevel := by
          intro h
          exact hi (heq.mp h)
        simp [ho, hi, hne]
    · simp [ho]
  · rw [if_neg hoff]
    have hne : inp ≠ setSite out s inpLevel := by
      intro h
      apply hoff
      rw [h]
      exact agreesOutsideSite_setSite out s inpLevel
    simp [hne]

/-- A pattern with one marked site in a specified local state.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure MarkedSite (m n : ℕ) (a : Level) where
  pattern : Pattern m n
  row : Fin m
  col : Fin n
  state : pattern (row, col) = a
  deriving DecidableEq, Fintype

/-- A marked-site record is determined by its pattern, row, and column.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem MarkedSite.ext' {a : Level} {x y : MarkedSite m n a}
    (hp : x.pattern = y.pattern) (hr : x.row = y.row) (hc : x.col = y.col) :
    x = y := by
  cases x
  cases y
  simp_all

/-- Marked sites are equivalent to patterns together with a row and a site in that level.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def markedSiteEquivSigma (a : Level) :
    MarkedSite m n a ≃
      Σ p : Pattern m n, Σ r : Fin m, {i : Fin n // p (r, i) = a} where
  toFun z := ⟨z.pattern, ⟨z.row, ⟨z.col, z.state⟩⟩⟩
  invFun z :=
    { pattern := z.1
      row := z.2.1
      col := z.2.2.1
      state := z.2.2.2 }
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨p, r, i⟩; rfl

/-- Expand a sum over a marked-state subtype into its literal pattern/row/site
sum.  This is the bookkeeping bridge used by both marked reindexings.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_markedSite (a : Level) (f : Pattern m n → Fin m → Fin n → ℝ) :
    (∑ p, ∑ r, ∑ i ∈ Finset.univ.filter (fun i ↦ p (r, i) = a), f p r i) =
      ∑ z : MarkedSite m n a, f z.pattern z.row z.col := by
  classical
  calc
    (∑ p, ∑ r, ∑ i ∈ Finset.univ.filter (fun i ↦ p (r, i) = a),
        f p r i) =
        ∑ p, ∑ r, ∑ i : {i : Fin n // p (r, i) = a}, f p r i := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_subtype _ (by simp) (f p r)
    _ = ∑ z : Σ p : Pattern m n,
          Σ r : Fin m, {i : Fin n // p (r, i) = a},
          f z.1 z.2.1 z.2.2.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro p _
      rw [Fintype.sum_sigma]
    _ = ∑ z : MarkedSite m n a, f z.pattern z.row z.col := by
      have h := Equiv.sum_comp (markedSiteEquivSigma (m := m) (n := n) a)
        (fun z : Σ p : Pattern m n,
          Σ r : Fin m, {i : Fin n // p (r, i) = a} ↦
            f z.1 z.2.1 z.2.2.1)
      simpa [markedSiteEquivSigma] using h.symm

/-- Changing the marked local state is a genuine finite equivalence.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def markedTransition (a b : Level) :
    MarkedSite m n a ≃ MarkedSite m n b where
  toFun z :=
    { pattern := setSite z.pattern (z.row, z.col) b
      row := z.row
      col := z.col
      state := setSite_apply_self _ _ _ }
  invFun z :=
    { pattern := setSite z.pattern (z.row, z.col) a
      row := z.row
      col := z.col
      state := setSite_apply_self _ _ _ }
  left_inv z := by
    cases z with
    | mk p r i h =>
      simp only
      exact MarkedSite.ext' (setSite_restore (b := b) p (r, i) h) rfl rfl
  right_inv z := by
    cases z with
    | mk p r i h =>
      simp only
      exact MarkedSite.ext' (setSite_restore (b := a) p (r, i) h) rfl rfl

/-- A marked-site sum may be reindexed without multiplicity loss.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_markedTransition (a b : Level)
    (f : MarkedSite m n b → ℝ) :
    (∑ z : MarkedSite m n a, f (markedTransition a b z)) =
      ∑ z : MarkedSite m n b, f z :=
  Equiv.sum_comp (markedTransition a b) f

/-- The marked-level transition reindexes a finite marked-site sum exactly.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_marked_reindex (a b : Level) (f : MarkedSite m n a → ℝ) :
    (∑ z : MarkedSite m n a, f z) =
      ∑ z : MarkedSite m n b, f ((markedTransition a b).symm z) := by
  have h := Equiv.sum_comp (markedTransition a b).symm f
  simpa using h.symm

/-- Promoting a non-heavy marked site inserts that column into its row's heavy sites.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem heavyInRow_setSite_two {p : Pattern m n} {r : Fin m} {i : Fin n}
    (_hi : p (r, i) ≠ .two) :
    (setSite p (r, i) .two).heavyInRow r = insert i (p.heavyInRow r) := by
  classical
  ext j
  simp only [Pattern.mem_heavyInRow, Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp
  · have hpair : (r, j) ≠ (r, i) := by
      intro h
      exact hji (congrArg Prod.snd h)
    rw [setSite_apply_of_ne p hpair]
    simp [hji]

/-- Setting a non-light marked site to level one inserts it into the row's light sites.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem lightInRow_setSite_one {p : Pattern m n} {r : Fin m} {i : Fin n}
    (_hi : p (r, i) ≠ .one) :
    (setSite p (r, i) .one).lightInRow r = insert i (p.lightInRow r) := by
  classical
  ext j
  simp only [Pattern.mem_lightInRow, Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp
  · have hpair : (r, j) ≠ (r, i) := by
      intro h
      exact hji (congrArg Prod.snd h)
    rw [setSite_apply_of_ne p hpair]
    simp [hji]

/-- Promoting a light marked site increases the row's heavy-site count by one.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem card_heavyInRow_setSite_two {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .one) :
    ((setSite p (r, i) .two).heavyInRow r).card =
      (p.heavyInRow r).card + 1 := by
  rw [heavyInRow_setSite_two (by simp [hi])]
  have hnot : i ∉ p.heavyInRow r := by simp [hi]
  simp [hnot]

/-- Demoting a heavy marked site increases the row's light-site count by one.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem card_lightInRow_setSite_one {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .two) :
    ((setSite p (r, i) .one).lightInRow r).card =
      (p.lightInRow r).card + 1 := by
  rw [lightInRow_setSite_one (by simp [hi])]
  have hnot : i ∉ p.lightInRow r := by simp [hi]
  simp [hnot]

/-- The heavy-site count after promotion is bounded by the initial row occupation grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem card_heavy_after_promote_le_rowGrade
    {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .one) :
    ((setSite p (r, i) .two).heavyInRow r).card ≤ rowGrade p r := by
  rw [card_heavyInRow_setSite_two hi]
  have hpos : 1 ≤ (p.lightInRow r).card := by
    exact Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  simp only [rowGrade]
  omega

/-- The light-site count after demotion is bounded by the initial row occupation grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem card_light_after_demote_le_rowGrade
    {p : Pattern m n} {r : Fin m} {i : Fin n}
    (hi : p (r, i) = .two) :
    ((setSite p (r, i) .one).lightInRow r).card ≤ rowGrade p r := by
  rw [card_lightInRow_setSite_one hi]
  have hpos : 1 ≤ (p.heavyInRow r).card := by
    exact Finset.one_le_card.mpr ⟨i, by simp [hi]⟩
  simp only [rowGrade]
  omega

end

end NLAlib.SparseFock.HeavyBandsConcrete
