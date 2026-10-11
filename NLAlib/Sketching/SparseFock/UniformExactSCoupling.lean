/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.UniformExactSModel
import NLAlib.Sketching.SparseFock.SparseIIDTransfer
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Fill/thin coupling for uniform signed exact-s columns

The iid ternary column is stored in `s` blocks of length `b`, hence has
`m = s*b` coordinates.  The coupling thins its support uniformly when it is
too large and fills it uniformly (with fresh signs) when it is too small.

This file also proves the sharp coefficient estimate used by the original
SparseStack constants: the number of nonempty blocks is bounded by
`min(K,s)` and has expectation `s*(1-p0(b))`.
-/

open scoped BigOperators InnerProductSpace

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseIIDTransfer SparseStackModel

noncomputable section

variable {b s : ℕ}

/-- One iid ternary column, grouped into `s` blocks of length `b`.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev NestedY (b s : ℕ) := Fin s → YVector b

/-- Its literal iid product law.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def nestedYLaw {b : ℕ} (hb : 0 < b) (s : ℕ) : FiniteLaw (NestedY b s) :=
  FiniteLaw.independentProduct (fun _ : Fin s => yVectorLaw b hb)

/-- The nested iid block-vector law weight is its product mass.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem nestedYLaw_weight {b : ℕ} (hb : 0 < b) (s : ℕ)
    (y : NestedY b s) :
    (nestedYLaw hb s).weight y = ∏ g, (yVectorLaw b hb).weight (y g) := rfl

/-- Flatten the block presentation to the physical `s*b` rows.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flatOutcome {b s : ℕ} (y : NestedY b s) (r : Fin (s * b)) : EtaOutcome :=
  let ga := finProdFinEquiv.symm r
  y ga.1 ga.2

/-- Flattening a nested iid vector recovers its specified block and within-block outcome.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem flatOutcome_pair {b s : ℕ} (y : NestedY b s)
    (g : Fin s) (a : Fin b) :
    flatOutcome y (finProdFinEquiv (g, a)) = y g a := by
  simp [flatOutcome]

/-- Physical nonzero support of a nested iid column.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flatSupport {b s : ℕ} (y : NestedY b s) : Finset (Fin (s * b)) :=
  Finset.univ.filter fun r => flatOutcome y r ≠ .zero

/-- A flattened coordinate belongs to support precisely when its outcome is nonzero.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem mem_flatSupport {b s : ℕ} (y : NestedY b s)
    (r : Fin (s * b)) : r ∈ flatSupport y ↔ flatOutcome y r ≠ .zero := by
  simp [flatSupport]

/-- Total number `K` of nonzero iid coordinates.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def totalSupport {b s : ℕ} (y : NestedY b s) : ℕ :=
  (flatSupport y).card

/-- Total flattened support is the sum of within-block support cardinalities.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem totalSupport_eq_sum {b s : ℕ} (y : NestedY b s) :
    totalSupport y = ∑ g, supportSize (y g) := by
  classical
  rw [totalSupport, flatSupport]
  calc
    (Finset.univ.filter fun r : Fin (s * b) => flatOutcome y r ≠ .zero).card =
        ∑ r : Fin (s * b), if flatOutcome y r = .zero then 0 else 1 := by
      symm
      simpa using
        (Finset.sum_boole (R := ℕ)
          (fun r : Fin (s * b) => flatOutcome y r ≠ .zero) Finset.univ)
    _ = ∑ ga : Fin s × Fin b,
        if flatOutcome y (finProdFinEquiv ga) = .zero then 0 else 1 := by
      exact (finProdFinEquiv.sum_comp
        (fun r : Fin (s * b) => if flatOutcome y r = .zero then 0 else 1)).symm
    _ = ∑ g, ∑ a, if y g a = .zero then 0 else 1 := by
      rw [Fintype.sum_prod_type]
      simp only [flatOutcome_pair]
    _ = ∑ g, supportSize (y g) := by
      apply Finset.sum_congr rfl
      intro g _
      exact (supportSize_eq_sum (y g)).symm

/-- Indicator that one block contains a nonzero coordinate.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockActive (y : NestedY b s) (g : Fin s) : ℕ :=
  if supportSize (y g) = 0 then 0 else 1

/-- Number of nonempty blocks.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def activeBlockCount (y : NestedY b s) : ℕ := ∑ g, blockActive y g

/-- The number of active blocks is bounded by total support cardinality.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem activeBlockCount_le_totalSupport (y : NestedY b s) :
    activeBlockCount y ≤ totalSupport y := by
  rw [activeBlockCount, totalSupport_eq_sum]
  apply Finset.sum_le_sum
  intro g _
  unfold blockActive
  split
  · omega
  · omega

/-- The number of active blocks is bounded by the number of blocks.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem activeBlockCount_le_s (y : NestedY b s) : activeBlockCount y ≤ s := by
  rw [activeBlockCount]
  calc
    (∑ g : Fin s, blockActive y g) ≤ ∑ _g : Fin s, 1 := by
      apply Finset.sum_le_sum
      intro g _
      unfold blockActive
      split <;> omega
    _ = s := by simp

/-- The active-block count is bounded by the minimum of total support and block count.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem activeBlockCount_le_min (y : NestedY b s) :
    activeBlockCount y ≤ min (totalSupport y) s := by
  rw [Nat.le_min]
  exact ⟨activeBlockCount_le_totalSupport y, activeBlockCount_le_s y⟩

/-- Real indicator of a nonzero ternary vector.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def vectorActiveIndicator {b : ℕ} (y : YVector b) : ℝ :=
  if supportSize y = 0 then 0 else 1

/-- The mean active-vector indicator equals the nonempty-block probability.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_vectorActiveIndicator {b : ℕ} (hb : 0 < b) :
    (yVectorLaw b hb).expect vectorActiveIndicator = 1 - p0 b := by
  have hzero : {y : YVector b | supportSize y = 0} = {zeroY b} := by
    ext y
    simp [supportSize_eq_zero_iff]
  calc
    (yVectorLaw b hb).expect vectorActiveIndicator =
        (yVectorLaw b hb).prob ({zeroY b}ᶜ) := by
      rw [FiniteLaw.prob]
      apply (yVectorLaw b hb).expect_congr
      intro y
      by_cases hy : y = zeroY b
      · subst y
        simp [vectorActiveIndicator, FiniteLaw.indicator,
          supportSize_eq_zero_iff]
      · have hsupp : supportSize y ≠ 0 := by
          simpa [supportSize_eq_zero_iff] using hy
        simp [vectorActiveIndicator, FiniteLaw.indicator, hy, hsupp]
    _ = 1 - (yVectorLaw b hb).prob {zeroY b} :=
      FiniteLaw.prob_compl (yVectorLaw b hb) {zeroY b}
    _ = 1 - p0 b := by
      rw [FiniteLaw.prob_singleton, zeroY_weight hb]

/-- The expected active-block count is the block count times nonempty-block probability.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_activeBlockCount {b s : ℕ} (hb : 0 < b) :
    (nestedYLaw hb s).expect (fun y => (activeBlockCount y : ℝ)) =
      (s : ℝ) * (1 - p0 b) := by
  change (nestedYLaw hb s).expect
      (fun y => ((∑ g, blockActive y g : ℕ) : ℝ)) = _
  simp_rw [Nat.cast_sum]
  rw [expect_fintype_sum]
  have hcoord (g : Fin s) :
      (nestedYLaw hb s).expect (fun y => (blockActive y g : ℝ)) = 1 - p0 b := by
    calc
      (nestedYLaw hb s).expect (fun y => (blockActive y g : ℝ)) =
          (nestedYLaw hb s).expect (fun y => vectorActiveIndicator (y g)) := by
        apply (nestedYLaw hb s).expect_congr
        intro y
        simp [blockActive, vectorActiveIndicator]
      _ = (yVectorLaw b hb).expect vectorActiveIndicator := by
        exact FiniteLaw.expect_independentProduct_apply
          (fun _ : Fin s => yVectorLaw b hb) g vectorActiveIndicator
      _ = 1 - p0 b := expect_vectorActiveIndicator hb
  simp_rw [hcoord]
  simp
  ring

/-- The martingale coefficient `a = E[min(K,s)]/s`.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def couplingA {b s : ℕ} (hb : 0 < b) : ℝ :=
  (nestedYLaw hb s).expect (fun y => (min (totalSupport y) s : ℝ)) / (s : ℝ)

/-- The sharp block lower bound `a ≥ 1-p0(b)`.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_sub_p0_le_couplingA {b s : ℕ} (hb : 0 < b) (hs : 0 < s) :
    1 - p0 b ≤ couplingA (s := s) hb := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hpoint (y : NestedY b s) :
      (activeBlockCount y : ℝ) ≤ (min (totalSupport y) s : ℝ) := by
    exact_mod_cast activeBlockCount_le_min y
  have hexpect := (nestedYLaw hb s).expect_mono hpoint
  rw [expect_activeBlockCount hb] at hexpect
  rw [couplingA]
  apply (le_div_iff₀ hsR).2
  nlinarith

/-- The exact-s coupling normalization is positive at positive block count and block size.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem couplingA_pos {b s : ℕ} (hb : 0 < b) (hs : 0 < s) :
    0 < couplingA (s := s) hb :=
  (one_sub_p0_pos hb).trans_le (one_sub_p0_le_couplingA hb hs)

/-- Inverse scale in the exact-s coupling.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def exactScale {b s : ℕ} (hb : 0 < b) : ℝ :=
  (couplingA (s := s) hb)⁻¹

/-- The exact-s correction scale is bounded by the single-block support correction.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactScale_le_cB {b s : ℕ} (hb : 0 < b) (hs : 0 < s) :
    exactScale (s := s) hb ≤ cB b := by
  rw [exactScale, cB]
  exact inv_anti₀ (one_sub_p0_pos hb) (one_sub_p0_le_couplingA hb hs)

/-- The exact-s correction scale is bounded by the universal support-gap constant.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactScale_le_cStar {b s : ℕ} (hb : 0 < b) (hs : 0 < s) :
    exactScale (s := s) hb ≤ PaperParameters.cStar :=
  (exactScale_le_cB hb hs).trans (cB_le_cStar hb)

/-! ## Literal fill/thin kernel -/

/-- Rademacher sign carried by a nonzero ternary atom; zero receives `plus`.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def signOfOutcome : EtaOutcome → Sign
  | .neg => .minus
  | .zero => .plus
  | .pos => .plus

/-- Recovering and re-embedding the sign of a nonzero ternary outcome returns that outcome.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem outcomeOfSign_signOfOutcome_of_ne_zero
    {z : EtaOutcome} (hz : z ≠ .zero) : outcomeOfSign (signOfOutcome z) = z := by
  cases z <;> simp_all [signOfOutcome, outcomeOfSign]

/-- Compatibility relation for thinning or filling one iid column.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Compatible {b s : ℕ} (y : NestedY b s) (x : ExactColumn (s * b) s) : Prop :=
  if s ≤ totalSupport y then
    (x.1 : Finset (Fin (s * b))) ⊆ flatSupport y ∧
      ∀ r ∈ (x.1 : Finset (Fin (s * b))),
        flatOutcome y r = outcomeOfSign (x.2 r)
  else
    flatSupport y ⊆ (x.1 : Finset (Fin (s * b))) ∧
      ∀ r ∈ flatSupport y, flatOutcome y r = outcomeOfSign (x.2 r)

/-- Unscaled iid value at a physical row.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def flatYValue {b s : ℕ} (y : NestedY b s) (r : Fin (s * b)) : ℝ :=
  yValue (flatOutcome y r)

/-- Every compatible fill/thin choice has overlap exactly `min(K,s)`.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem compatible_inner_eq_min {b s : ℕ} {y : NestedY b s}
    {x : ExactColumn (s * b) s} (hxy : Compatible y x) :
    (∑ r, columnValue x r * flatYValue y r) =
      (min (totalSupport y) s : ℝ) := by
  classical
  by_cases hlarge : s ≤ totalSupport y
  · have h := hxy
    simp only [Compatible, if_pos hlarge] at h
    rcases h with ⟨hsub, hsign⟩
    have hterm (r : Fin (s * b)) :
        columnValue x r * flatYValue y r =
          if r ∈ (x.1 : Finset (Fin (s * b))) then 1 else 0 := by
      by_cases hr : r ∈ (x.1 : Finset (Fin (s * b)))
      · have hout := hsign r hr
        have hr' : r ∈ x.1 := Set.powersetCard.mem_coe_iff.mp hr
        rw [columnValue_of_mem x hr', flatYValue, hout,
          yValue_outcomeOfSign]
        simpa [hr, pow_two] using Sign.val_sq (x.2 r)
      · have hr' : r ∉ x.1 := fun hmem =>
          hr (Set.powersetCard.mem_coe_iff.mpr hmem)
        rw [columnValue_of_notMem x hr', if_neg hr]
        simp
    simp_rw [hterm]
    have hsum :
        (∑ r : Fin (s * b),
          if r ∈ (x.1 : Finset (Fin (s * b))) then (1 : ℝ) else 0) = s := by
      calc
        (∑ r : Fin (s * b),
          if r ∈ (x.1 : Finset (Fin (s * b))) then (1 : ℝ) else 0) =
            ((x.1 : Finset (Fin (s * b))).card : ℝ) := by simp
        _ = s := by rw [(x.1).prop]
    rw [hsum, min_eq_right (by exact_mod_cast hlarge)]
  · have h := hxy
    simp only [Compatible, if_neg hlarge] at h
    rcases h with ⟨hsub, hsign⟩
    have hterm (r : Fin (s * b)) :
        columnValue x r * flatYValue y r =
          if r ∈ flatSupport y then 1 else 0 := by
      by_cases hr : r ∈ flatSupport y
      · have hrx := hsub hr
        have hout := hsign r hr
        have hrx' : r ∈ x.1 := Set.powersetCard.mem_coe_iff.mp hrx
        rw [columnValue_of_mem x hrx', flatYValue, hout,
          yValue_outcomeOfSign]
        have hnzero : outcomeOfSign (x.2 r) ≠ .zero := by
          cases x.2 r <;> simp [outcomeOfSign]
        simpa [hr, hout, hnzero, pow_two] using Sign.val_sq (x.2 r)
      · have hyzero : flatOutcome y r = .zero := by
          by_contra hnzero
          exact hr ((mem_flatSupport y r).mpr hnzero)
        rw [if_neg hr, flatYValue, hyzero]
        simp [yValue]
    simp_rw [hterm]
    have hsum :
        (∑ r : Fin (s * b), if r ∈ flatSupport y then (1 : ℝ) else 0) =
          (totalSupport y : ℝ) := by
      rw [totalSupport]
      simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
        (Finset.sum_boole (R := ℝ)
          (fun r : Fin (s * b) => r ∈ flatSupport y) Finset.univ)
    rw [hsum, min_eq_left (by
      exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hlarge))]

/-- Exact columns compatible with one iid column.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev ChoiceColumn {b s : ℕ} (y : NestedY b s) :=
  {x : ExactColumn (s * b) s // Compatible y x}

/-- Every iid outcome admits a compatible exactly-s selector column.
Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem choiceColumn_nonempty {b s : ℕ} (hb : 0 < b) (_hs : 0 < s)
    (y : NestedY b s) : Nonempty (ChoiceColumn y) := by
  classical
  have hsm : s ≤ s * b := by
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hb)]
  by_cases hlarge : s ≤ totalSupport y
  · obtain ⟨t, htsub, htcard⟩ :=
      Finset.exists_subset_card_eq hlarge
    let S : ExactSupport (s * b) s := ⟨t, htcard⟩
    let signs : Fin (s * b) → Sign := fun r => signOfOutcome (flatOutcome y r)
    refine ⟨⟨(S, signs), ?_⟩⟩
    simp only [Compatible, if_pos hlarge]
    refine ⟨htsub, ?_⟩
    intro r hr
    symm
    apply outcomeOfSign_signOfOutcome_of_ne_zero
    exact (mem_flatSupport y r).mp (htsub hr)
  · have hKle : totalSupport y ≤ s := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hflatuniv : flatSupport y ⊆ (Finset.univ : Finset (Fin (s * b))) :=
      Finset.subset_univ _
    obtain ⟨t, hflat, htuniv, htcard⟩ :=
      Finset.exists_subsuperset_card_eq hflatuniv hKle (by simpa using hsm)
    let S : ExactSupport (s * b) s := ⟨t, htcard⟩
    let signs : Fin (s * b) → Sign := fun r => signOfOutcome (flatOutcome y r)
    refine ⟨⟨(S, signs), ?_⟩⟩
    simp only [Compatible, if_neg hlarge]
    refine ⟨hflat, ?_⟩
    intro r hr
    symm
    apply outcomeOfSign_signOfOutcome_of_ne_zero
    exact (mem_flatSupport y r).mp hr

/-- Uniform fill/thin choice, pushed to the exact-column space.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def selectionKernel {b s : ℕ} (hb : 0 < b) (hs : 0 < s)
    (y : NestedY b s) : FiniteLaw (ExactColumn (s * b) s) := by
  classical
  let : Nonempty (ChoiceColumn y) := choiceColumn_nonempty hb hs y
  exact FiniteLaw.map (FiniteLaw.uniform : FiniteLaw (ChoiceColumn y)) Subtype.val

/-- Joint law obtained by drawing iid `Y` and then its uniform fill/thin `X`.

Source: ported from `SparseFockFormal.UniformExactSCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def jointColumnLaw {b s : ℕ} (hb : 0 < b) (hs : 0 < s) :
    FiniteLaw (NestedY b s × ExactColumn (s * b) s) where
  weight z := (nestedYLaw hb s).weight z.1 * (selectionKernel hb hs z.1).weight z.2
  weight_nonneg z := mul_nonneg
    ((nestedYLaw hb s).weight_nonneg z.1)
    ((selectionKernel hb hs z.1).weight_nonneg z.2)
  sum_weight := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (selectionKernel hb hs _).sum_weight, mul_one]
    exact (nestedYLaw hb s).sum_weight

end

end NLAlib.SparseFock.UniformExactS
