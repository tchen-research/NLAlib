import NLAlib.Matrix.Spectral.RestrictedInvertibilitySelection
import NLAlib.Matrix.Spectral.RankOneInertia
import NLAlib.Matrix.Basic.RankBounds

/-!
# A strict rank-increasing restricted-invertibility step

The weighted averaging certificate and the rank-one inertia theorem give an
actual column update that increases the rank, keeps every nonzero eigenvalue
strictly above the new barrier, and preserves the weighted potential.
Source: Spielman--Srivastava (2009), Theorem 2.
-/

noncomputable section

open scoped Matrix BigOperators MatrixOrder
open Matrix

namespace NLAlib.RestrictedInvertibility

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem card_eigenvalues_gt_eq_rank {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {b : ℝ} (hb : 0 < b) (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i) :
    (Finset.univ.filter fun i => b < hA.eigenvalues i).card = A.rank := by
  classical
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact ne_of_gt (hb.trans hi)
  · intro hi
    exact (hgap i).resolve_left hi

/-- A negative rank-one interaction increases the selected rank by one and
preserves a strict positive spectral gap. The proof compares the positive
inertia above the new barrier with the elementary rank upper bound; no
continuity of spectral paths is used. -/
theorem rank_add_vecMulVec_eq_and_eigenvalues_gap
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {b b' : ℝ}
    (hb' : 0 < b') (hbb' : b' ≤ b)
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i)
    (v : n → ℝ)
    (hinteraction : quadForm (A - b' • (1 : Matrix n n ℝ))⁻¹ v < -1) :
    (A + vecMulVec v v).rank = A.rank + 1 ∧
      ∀ i, (hA.add (by simpa only [star_trivial] using
        (posSemidef_vecMulVec_self_star v).isHermitian)).eigenvalues i = 0 ∨
        b' < (hA.add (by simpa only [star_trivial] using
          (posSemidef_vecMulVec_self_star v).isHermitian)).eigenvalues i := by
  classical
  have hv : (vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star v
  let hA' : (A + vecMulVec v v).IsHermitian := hA.add hv.isHermitian
  have hgap' : ∀ i, hA.eigenvalues i = 0 ∨ b' < hA.eigenvalues i := by
    intro i
    rcases hgap i with hi | hi
    · exact Or.inl hi
    · exact Or.inr (hbb'.trans_lt hi)
  have hc := inertiaPos_add_vecMulVec_eq_add_one_of_shift hA b' v
    (isUnit_shift_of_eigenvalues_gap hA hb' hgap')
    (by simpa [quadForm, star_trivial] using hinteraction)
  have hmat : A - b' • (1 : Matrix n n ℝ) + vecMulVec v v =
      A + vecMulVec v v - b' • (1 : Matrix n n ℝ) := by module
  rw [hmat, inertiaPos_sub_smul_one_eq_card hA' b',
    card_eigenvalues_gt_eq_rank hA hb' hgap'] at hc
  have hsub : (Finset.univ.filter fun i => b' < hA'.eigenvalues i) ⊆
      (Finset.univ.filter fun i => hA'.eigenvalues i ≠ 0) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      ne_of_gt (hb'.trans (Finset.mem_filter.mp hi).2)⟩
  have hlower : A.rank + 1 ≤ (A + vecMulVec v v).rank := by
    rw [← hc, hA'.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    exact Finset.card_le_card hsub
  have hupper : (A + vecMulVec v v).rank ≤ A.rank + 1 :=
    (rank_add_le _ _).trans (Nat.add_le_add_left (Matrix.rank_vecMulVec_le v v) _)
  have hrank := le_antisymm hupper hlower
  refine ⟨hrank, ?_⟩
  have heq : (Finset.univ.filter fun i => b' < hA'.eigenvalues i) =
      (Finset.univ.filter fun i => hA'.eigenvalues i ≠ 0) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [← Fintype.card_subtype, ← hA'.rank_eq_card_non_zero_eigs, hrank, hc]
  intro i
  by_cases hi : hA'.eigenvalues i = 0
  · exact Or.inl hi
  · right
    have hm : i ∈ Finset.univ.filter fun j => hA'.eigenvalues j ≠ 0 := by simp [hi]
    rw [← heq] at hm
    exact (Finset.mem_filter.mp hm).2

/-- One complete weighted lower-barrier step selects an original column.
It increases rank by exactly one, preserves the strict nonzero spectral gap,
and does not increase the weighted potential. Source:
Spielman--Srivastava (2009), proof of Theorem 2. -/
theorem exists_column_rank_eq_add_one_and_lowerPotential_le
    {I : Type*} [Fintype I] [Nonempty I] (v : I → n → ℝ)
    {A H : Matrix n n ℝ} (hA : A.IsHermitian) (hH : H.PosSemidef)
    (hframe : ∑ i, vecMulVec (v i) (v i) = H)
    {b δ Λ : ℝ} (hδ : 0 < δ) (hb : δ < b) (hΛ : 0 < Λ)
    (hHle : H ≤ Λ • (1 : Matrix n n ℝ))
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i)
    (hkernel : b * Λ ≤ δ * (H.trace - (A.rank : ℝ) * Λ))
    (hpot : lowerPotential H A b ≤ -(Fintype.card I : ℝ) - Λ / δ) :
    ∃ i,
      (A + vecMulVec (v i) (v i)).rank = A.rank + 1 ∧
      (∀ j, (hA.add (by simpa only [star_trivial] using
        (posSemidef_vecMulVec_self_star (v i)).isHermitian)).eigenvalues j = 0 ∨
        b - δ < (hA.add (by simpa only [star_trivial] using
          (posSemidef_vecMulVec_self_star (v i)).isHermitian)).eigenvalues j) ∧
      lowerPotential H (A + vecMulVec (v i) (v i)) (b - δ) ≤
        lowerPotential H A b := by
  let R : Matrix n n ℝ := (A - (b - δ) • (1 : Matrix n n ℝ))⁻¹
  let Δ : ℝ := lowerPotential H A b - lowerPotential H A (b - δ)
  have hh := lowerPotential_gap_pos_and_trace_sq_le hA hH hδ hb hΛ hHle hgap hkernel
  change 0 < Δ ∧ Λ * (H * R ^ 2).trace ≤ Δ * (Λ / δ + Δ) at hh
  have hR : R.IsHermitian := by
    apply Matrix.IsHermitian.inv
    apply hA.sub
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isHermitian_diagonal _
  obtain ⟨i, hi, hcert⟩ := exists_column_interaction_lt_neg_one v hframe hH hR
    hh.1 hΛ hδ hHle (show (H * R).trace = lowerPotential H A b - Δ by
      dsimp [R, Δ, lowerPotential]; ring) hpot hh.2
  have hspec := rank_add_vecMulVec_eq_and_eigenvalues_gap hA (sub_pos.mpr hb)
    (show b - δ ≤ b by linarith) hgap (v i) hi
  refine ⟨i, hspec.1, hspec.2, ?_⟩
  exact lowerPotential_add_vecMulVec_le (v i)
    (isUnit_shift_of_eigenvalues_gap hA (sub_pos.mpr hb) (by
      intro j
      rcases hgap j with hj | hj
      · exact Or.inl hj
      · exact Or.inr (by linarith))) hh.1
    (show lowerPotential H A (b - δ) = lowerPotential H A b - Δ by dsimp [Δ]; ring)
    hi hcert

end NLAlib.RestrictedInvertibility
