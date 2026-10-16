import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! # A positive-matrix eigenpair by compact minimization

On a normalized linear subsolution slice, strict positivity keeps every
coordinate positive. Minimizing the maximum Collatz ratio there gives an
eigenvector: otherwise applying the matrix once strictly decreases every ratio.
This is a finite-dimensional variational construction, independent of a
fixed-point theorem. Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
private theorem mulVec_pos_of_pos_of_sum_one {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (i : ι) : 0 < (A *ᵥ x) i := by
  have hsum : 0 < ∑ j, x j := by rw [hs]; norm_num
  obtain ⟨j, hj⟩ : ∃ j, 0 < x j := by
    by_contra! h
    have hle := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => h j)
    linarith
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hA i j).le (hx j))
    ⟨j, mem_univ j, mul_pos (hA i j) hj⟩

private def positiveSubsolutionSlice (A : Matrix ι ι ℝ) (R : ℝ) : Set (ι → ℝ) :=
  Set.Icc 0 (fun _ => 1) ∩
    ({x | ∑ i, x i = 1} ∩ {x | ∀ i, (A *ᵥ x) i ≤ R * x i})

omit [DecidableEq ι] [Nonempty ι] in
private theorem isCompact_positiveSubsolutionSlice (A : Matrix ι ι ℝ) (R : ℝ) :
    IsCompact (positiveSubsolutionSlice A R) := by
  have hs : IsClosed {x : ι → ℝ | ∑ i, x i = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hb : IsClosed {x : ι → ℝ | ∀ i, (A *ᵥ x) i ≤ R * x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)
  exact isCompact_Icc.inter_right (hs.inter hb)

omit [DecidableEq ι] [Nonempty ι] in
private theorem pos_of_mem_positiveSubsolutionSlice {A : Matrix ι ι ℝ} {R : ℝ}
    (hA : ∀ i j, 0 < A i j) {x : ι → ℝ}
    (hx : x ∈ positiveSubsolutionSlice A R) (i : ι) : 0 < x i := by
  have hpos := mulVec_pos_of_pos_of_sum_one hA (fun j => hx.1.1 j) hx.2.1 i
  by_contra hi
  have hz : x i = 0 := le_antisymm (le_of_not_gt hi) (hx.1.1 i)
  have hbound := hx.2.2 i
  rw [hz, mul_zero] at hbound
  linarith

omit [DecidableEq ι] in
private theorem positive_eigenpair_of_nonempty_slice {A : Matrix ι ι ℝ} {R : ℝ}
    (hA : ∀ i j, 0 < A i j)
    (hK : (positiveSubsolutionSlice A R).Nonempty) :
    ∃ (r : ℝ) (p : ι → ℝ), 0 < r ∧ (∀ i, 0 < p i) ∧
      (∑ i, p i = 1) ∧ A *ᵥ p = r • p := by
  let f : (ι → ℝ) → ℝ := fun x =>
    Finset.univ.sup' Finset.univ_nonempty (fun i => (A *ᵥ x) i / x i)
  have hf : ContinuousOn f (positiveSubsolutionSlice A R) := by
    apply ContinuousOn.finset_sup'_apply
    intro i _
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact (pos_of_mem_positiveSubsolutionSlice hA hx i).ne'
  obtain ⟨p, hp, hmin⟩ := (isCompact_positiveSubsolutionSlice A R).exists_isMinOn hK hf
  have hpp : ∀ i, 0 < p i := pos_of_mem_positiveSubsolutionSlice hA hp
  let r := f p
  have hratio (i : ι) : (A *ᵥ p) i / p i ≤ r := by
    exact Finset.le_sup' (fun i => (A *ᵥ p) i / p i) (mem_univ i)
  have hbound (i : ι) : (A *ᵥ p) i ≤ r * p i :=
    (div_le_iff₀ (hpp i)).mp (hratio i)
  have hrR : r ≤ R := Finset.sup'_le _ _ fun i _ =>
    (div_le_iff₀ (hpp i)).mpr (hp.2.2 i)
  have hAp : ∀ i, 0 < (A *ᵥ p) i :=
    mulVec_pos_of_pos_of_sum_one hA (fun i => (hpp i).le) hp.2.1
  have hr : 0 < r := by
    let i : ι := Classical.choice ‹Nonempty ι›
    exact (div_pos (hAp i) (hpp i)).trans_le (hratio i)
  refine ⟨r, p, hr, hpp, hp.2.1, ?_⟩
  by_contra heig
  have hstrict : ∃ j, (A *ᵥ p) j < r * p j := by
    by_contra! hj
    apply heig
    exact funext fun j => le_antisymm (hbound j) (hj j)
  obtain ⟨j, hj⟩ := hstrict
  have hAA (i : ι) : (A *ᵥ (A *ᵥ p)) i < r * (A *ᵥ p) i := by
    calc
      _ = ∑ k, A i k * (A *ᵥ p) k := rfl
      _ < ∑ k, A i k * (r * p k) := Finset.sum_lt_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hbound k) (hA i k).le)
        ⟨j, mem_univ j, mul_lt_mul_of_pos_left hj (hA i j)⟩
      _ = _ := by simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]; congr 1; funext k; ring
  let s : ℝ := ∑ i, (A *ᵥ p) i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hAp i) Finset.univ_nonempty
  let z : ι → ℝ := s⁻¹ • (A *ᵥ p)
  have hzpos (i : ι) : 0 < z i := mul_pos (inv_pos.mpr hs) (hAp i)
  have hzsum : ∑ i, z i = 1 := by
    simp only [z, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  have hAz (i : ι) : (A *ᵥ z) i < r * z i := by
    have h := mul_lt_mul_of_pos_left (hAA i) (inv_pos.mpr hs)
    simpa only [z, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] using h
  have hzK : z ∈ positiveSubsolutionSlice A R := by
    refine ⟨⟨fun i => (hzpos i).le, fun i => ?_⟩, hzsum, fun i => ?_⟩
    · exact (Finset.single_le_sum (fun k _ => (hzpos k).le) (mem_univ i)).trans_eq hzsum
    · exact (hAz i).le.trans (mul_le_mul_of_nonneg_right hrR (hzpos i).le)
  have hfr : f z < r := (Finset.sup'_lt_iff _).mpr fun i _ =>
    (div_lt_iff₀ (hzpos i)).mpr (hAz i)
  exact (not_lt_of_ge (hmin hzK)) hfr

omit [DecidableEq ι] in
/-- A strictly positive real matrix has a strictly positive, unit-sum right
eigenvector with a strictly positive eigenvalue. The eigenpair is constructed
by compact minimization, without an eigenpair hypothesis.
Source: Horn–Johnson, Chapter 8.
atlas: nonnegative-perron-eigenpair (partial) -/
theorem exists_positive_eigenpair_of_pos {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 < A i j) :
    ∃ (r : ℝ) (p : ι → ℝ), 0 < r ∧ (∀ i, 0 < p i) ∧
      (∑ i, p i = 1) ∧ A *ᵥ p = r • p := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  let x : ι → ℝ := fun _ => N⁻¹
  let R : ℝ := ∑ i, ∑ j, A i j
  have hrow (i : ι) : (∑ j, A i j) ≤ R :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => (hA k j).le) (mem_univ i)
  apply positive_eigenpair_of_nonempty_slice hA (R := R)
  refine ⟨x, ⟨⟨fun _ => (inv_pos.mpr hN).le, fun _ => ?_⟩, ?_, fun i => ?_⟩⟩
  · exact inv_le_one_of_one_le₀ hN1
  · change (∑ _ : ι, N⁻¹) = 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  · change (∑ j, A i j * N⁻¹) ≤ R * N⁻¹
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (inv_pos.mpr hN).le

end Matrix
