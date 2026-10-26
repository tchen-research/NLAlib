import NLAlib.Matrix.Functions.OperatorCapacitySpectral
import NLAlib.ForMathlib.Combinatorics.Hall.WeightedMatrix

/-!
# Rank nondecrease from near-balanced Kraus maps

The finite spectral transition matrix has a supported permutation when
its normalization defect is small. Every positive input eigenvalue then
forces a distinct positive output eigenvalue. This gives the rank clause
of GGOW, *Operator scaling: theory and applications*, arXiv:1511.03730v4,
Theorem 2.12 without a limiting argument or a capacity minimizer.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A nonnegative matrix with a supported permutation cannot reduce the
number of nonzero coordinates of a nonnegative vector. Each positive
coordinate is sent through its matched positive matrix entry. -/
theorem card_nonzero_le_card_nonzero_mulVec_of_perm_pos (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (σ : Equiv.Perm n) (hσ : ∀ i, 0 < C i (σ i))
    (x : n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    Fintype.card {j // x j ≠ 0} ≤ Fintype.card {i // (C *ᵥ x) i ≠ 0} := by
  classical
  let f : {j // x j ≠ 0} → {i // (C *ᵥ x) i ≠ 0} := fun j =>
    ⟨σ.symm j, by
      have hxpos : 0 < x j := lt_of_le_of_ne (hx j) j.property.symm
      have hterm : 0 < C (σ.symm j) (σ (σ.symm j)) * x (σ (σ.symm j)) :=
        mul_pos (hσ _) (by simpa only [Equiv.apply_symm_apply] using hxpos)
      have hle : C (σ.symm j) (σ (σ.symm j)) * x (σ (σ.symm j)) ≤
          (C *ᵥ x) (σ.symm j) := by
        change _ ≤ ∑ k, C (σ.symm j) k * x k
        exact Finset.single_le_sum
          (fun k _ => mul_nonneg (hC (σ.symm j) k) (hx k))
          (Finset.mem_univ (σ (σ.symm j)))
      exact (hterm.trans_le hle).ne'⟩
  apply Fintype.card_le_of_injective f
  intro a b hab
  apply Subtype.ext
  apply σ.symm.injective
  exact congrArg Subtype.val hab

end Matrix

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [DecidableEq n] in
private theorem card_mul_lt_one_of_le_div_card_add_one {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1)) :
    (Fintype.card n : ℝ) * ε < 1 := by
  have hn0 : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hbound := (le_div_iff₀
    (show (0 : ℝ) < (Fintype.card n : ℝ) + 1 by positivity)).mp hεsmall
  rcases eq_or_lt_of_le hε0 with hzero | hpos
  · simp [← hzero]
  · nlinarith

/-- A trace-preserving Kraus map with Frobenius defect at most
`ε ≤ 1/(card n + 1)` does not decrease the rank of any positive
semidefinite input. The proof counts positive eigenvalues through a
supported permutation of the actual spectral transition matrix.
Source: GGOW, arXiv:1511.03730v4, Theorem 2.12.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem rank_le_rank_krausMap_of_adjoint_normalized
    (A : ι → Matrix n n ℂ) (hA : krausMap (fun a => (A a)ᴴ) 1 = 1)
    {ε : ℝ} (hε : frobSq (krausMap A 1 - 1) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1))
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X.rank ≤ (krausMap A X).rank := by
  obtain ⟨W, hW, hcol, hrow, heig⟩ := exists_krausTransition_eigenvalues A hA hX
  have hε0 := (frobSq_nonneg (krausMap A 1 - 1)).trans hε
  have hdef : (Fintype.card n : ℝ) *
      ∑ i, ((∑ j, W i j) - 1) ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_left (hrow.trans hε) (Nat.cast_nonneg _)).trans_lt
      (card_mul_lt_one_of_le_div_card_add_one hε0 hεsmall)
  obtain ⟨σ, hσ⟩ := Matrix.exists_perm_pos_of_card_mul_sum_sq_row_sub_lt_one W hW hcol hdef
  have hcard := Matrix.card_nonzero_le_card_nonzero_mulVec_of_perm_pos
    W hW σ hσ hX.isHermitian.eigenvalues hX.eigenvalues_nonneg
  rw [heig] at hcard
  rw [hX.isHermitian.rank_eq_card_non_zero_eigs,
    (krausMap_posSemidef A X hX).isHermitian.rank_eq_card_non_zero_eigs]
  exact hcard

/-- A unital Kraus map whose adjoint Frobenius defect is at most
`ε ≤ 1/(card n + 1)` does not decrease the rank of any positive
semidefinite input. Source: GGOW, arXiv:1511.03730v4, Theorem 2.12.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem rank_le_rank_krausMap_of_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap A 1 = 1)
    {ε : ℝ} (hε : frobSq (krausMap (fun a => (A a)ᴴ) 1 - 1) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1))
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X.rank ≤ (krausMap A X).rank := by
  obtain ⟨W, hW, hrow, hcol, heig⟩ := exists_krausTransition_eigenvalues_of_unital A hA hX
  have hε0 := (frobSq_nonneg (krausMap (fun a => (A a)ᴴ) 1 - 1)).trans hε
  have hdef : (Fintype.card n : ℝ) *
      ∑ j, ((∑ i, W i j) - 1) ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_left (hcol.trans hε) (Nat.cast_nonneg _)).trans_lt
      (card_mul_lt_one_of_le_div_card_add_one hε0 hεsmall)
  obtain ⟨σ, hσ⟩ := Matrix.exists_perm_pos_of_card_mul_sum_sq_column_sub_lt_one W hW hrow hdef
  have hcard := Matrix.card_nonzero_le_card_nonzero_mulVec_of_perm_pos
    W hW σ hσ hX.isHermitian.eigenvalues hX.eigenvalues_nonneg
  rw [heig] at hcard
  rw [hX.isHermitian.rank_eq_card_non_zero_eigs,
    (krausMap_posSemidef A X hX).isHermitian.rank_eq_card_non_zero_eigs]
  exact hcard

end NLAlib
