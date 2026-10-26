import NLAlib.Matrix.Spectral.RestrictedInvertibilityStep
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite weighted lower-barrier selection

This file iterates the genuine column-selection step. The kernel estimate at
stage `t` is derived from `tr H - t Λ`, rather than added as an inductive
hypothesis about a changing kernel projector. Source: Spielman--Srivastava
(2009), Theorem 2.
-/

noncomputable section

open scoped Matrix BigOperators MatrixOrder
open Matrix

namespace NLAlib.RestrictedInvertibility

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- The frame operator of a finite sequence of selected labels. Repetitions
are allowed by the definition; a full rank theorem will exclude them. -/
def selectedFrameOperator {k : ℕ} (v : I → n → ℝ) (s : Fin k → I) : Matrix n n ℝ :=
  ∑ j, vecMulVec (v (s j)) (v (s j))

omit [Fintype I] [DecidableEq n] in
/-- A selected frame operator is positive semidefinite. -/
theorem selectedFrameOperator_posSemidef {k : ℕ} (v : I → n → ℝ) (s : Fin k → I) :
    (selectedFrameOperator v s).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun j _ => by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v (s j))

omit [Fintype I] [Fintype n] [DecidableEq n] in
private theorem selectedFrameOperator_snoc {k : ℕ} (v : I → n → ℝ)
    (s : Fin k → I) (i : I) :
    selectedFrameOperator v (Fin.snoc s i) = selectedFrameOperator v s + vecMulVec (v i) (v i) := by
  unfold selectedFrameOperator
  rw [Fin.sum_univ_castSucc]
  simp

private theorem lowerPotential_zero {H : Matrix n n ℝ} {b : ℝ} (hb : 0 < b) :
    lowerPotential H 0 b = -H.trace / b := by
  have hinv : ((-b) • (1 : Matrix n n ℝ))⁻¹ = (-b)⁻¹ • (1 : Matrix n n ℝ) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ (neg_ne_zero.mpr (ne_of_gt hb)), one_smul]
  unfold lowerPotential
  rw [zero_sub, ← neg_smul, hinv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  ring

private theorem eigenvalues_gap_of_eq {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A = B) (b : ℝ)
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i) :
    ∀ i, hB.eigenvalues i = 0 ∨ b < hB.eigenvalues i := by
  subst B
  exact hgap

/-- Finite weighted lower-barrier iteration selects exactly `k` vectors, has
rank `k`, and keeps every nonzero eigenvalue strictly above `b₀-kδ`.
All one-step certificates are derived from the decomposition of `H` and the
initial potential budget. Source: Spielman--Srivastava (2009), Theorem 2. -/
theorem exists_selectedFrameOperator_rank_eq_and_eigenvalues_gap
    [Nonempty I] (v : I → n → ℝ) {H : Matrix n n ℝ}
    (hH : H.PosSemidef) (hframe : ∑ i, vecMulVec (v i) (v i) = H)
    {b₀ δ Λ : ℝ} (hb₀ : 0 < b₀) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hHle : H ≤ Λ • (1 : Matrix n n ℝ))
    (hpot₀ : -H.trace / b₀ ≤ -(Fintype.card I : ℝ) - Λ / δ)
    (k : ℕ) (hk : (k : ℝ) * δ < b₀) :
    ∃ s : Fin k → I,
      (selectedFrameOperator v s).rank = k ∧
      (∀ j, ((selectedFrameOperator_posSemidef v s).isHermitian).eigenvalues j = 0 ∨
        b₀ - (k : ℝ) * δ <
          ((selectedFrameOperator_posSemidef v s).isHermitian).eigenvalues j) ∧
      lowerPotential H (selectedFrameOperator v s) (b₀ - (k : ℝ) * δ) ≤
        -(Fintype.card I : ℝ) - Λ / δ := by
  have hkernel₀ : b₀ * Λ ≤ δ * H.trace := by
    have hdiv : Λ / δ ≤ H.trace / b₀ := by
      have hm : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
      have hp : -(H.trace / b₀) ≤ -(Fintype.card I : ℝ) - Λ / δ := by
        simpa only [neg_div] using hpot₀
      linarith
    have hh := (div_le_div_iff₀ hδ hb₀).mp hdiv
    nlinarith
  have hind : ∀ t : ℕ, t ≤ k → ∃ s : Fin t → I,
      (selectedFrameOperator v s).rank = t ∧
      (∀ j, ((selectedFrameOperator_posSemidef v s).isHermitian).eigenvalues j = 0 ∨
        b₀ - (t : ℝ) * δ <
          ((selectedFrameOperator_posSemidef v s).isHermitian).eigenvalues j) ∧
      lowerPotential H (selectedFrameOperator v s) (b₀ - (t : ℝ) * δ) ≤
        -(Fintype.card I : ℝ) - Λ / δ := by
    intro t
    induction t with
    | zero =>
      intro _
      let s : Fin 0 → I := Fin.elim0
      have hs : selectedFrameOperator v s = 0 := by simp [selectedFrameOperator]
      refine ⟨s, ?_, ?_, ?_⟩
      · rw [hs, Matrix.rank_zero]
      · intro j
        left
        exact congrFun
          ((selectedFrameOperator_posSemidef v s).isHermitian.eigenvalues_eq_zero_iff.mpr hs) j
      · simpa only [Nat.cast_zero, zero_mul, sub_zero, hs, lowerPotential_zero hb₀] using hpot₀
    | succ t ih =>
      intro ht
      obtain ⟨s, hsRank, hsGap, hsPot⟩ := ih (Nat.le_of_succ_le ht)
      let A := selectedFrameOperator v s
      let hA := (selectedFrameOperator_posSemidef v s).isHermitian
      have htδ : ((t + 1 : ℕ) : ℝ) * δ < b₀ :=
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) hδ.le).trans_lt hk
      have hb : δ < b₀ - (t : ℝ) * δ := by push_cast at htδ; linarith
      have hkernel : (b₀ - (t : ℝ) * δ) * Λ ≤ δ * (H.trace - (A.rank : ℝ) * Λ) := by
        dsimp [A]
        rw [hsRank]
        nlinarith
      obtain ⟨i, hiRank, hiGap, hiPot⟩ :=
        exists_column_rank_eq_add_one_and_lowerPotential_le v hA hH hframe hδ hb hΛ
          hHle hsGap hkernel hsPot
      refine ⟨Fin.snoc s i, ?_, ?_, ?_⟩
      · rw [selectedFrameOperator_snoc]
        exact hiRank.trans (by rw [hsRank])
      · intro j
        have heq := selectedFrameOperator_snoc v s i
        have hh := eigenvalues_gap_of_eq _
          (selectedFrameOperator_posSemidef v (Fin.snoc s i)).isHermitian heq.symm
          (b₀ - (t : ℝ) * δ - δ) hiGap j
        have hbnew : b₀ - ((t + 1 : ℕ) : ℝ) * δ = b₀ - (t : ℝ) * δ - δ := by
          push_cast
          ring
        simpa only [hbnew] using hh
      · rw [selectedFrameOperator_snoc]
        have hbnew : b₀ - ((t + 1 : ℕ) : ℝ) * δ = b₀ - (t : ℝ) * δ - δ := by
          push_cast
          ring
        rw [hbnew]
        exact hiPot.trans hsPot
  exact hind k le_rfl

end NLAlib.RestrictedInvertibility
