import NLAlib.Matrix.Spectral.EigenvalueOrder
/-!
# Interlacing under low-rank and signed updates

The numbers of positive and negative eigenvalues give the exact index
shifts for symmetric updates. Rank bounds give the two symmetric shifts,
and a rank-one PSD update gives ordinary one-step interlacing.
Source: Horn--Johnson (2013), Corollaries 4.3.3, 4.3.5, 4.3.7, 4.3.9.
Atlas: `low-rank-update-interlacing`.
-/

noncomputable section
open Matrix Module

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Once the index is at least the number of positive eigenvalues, the
sorted eigenvalue is nonpositive. Horn--Johnson (2013), Corollary 4.3.3;
helper for `low-rank-update-interlacing`. -/
theorem eigenvalues₀_le_zero_of_card_pos_le {B : Matrix n n ℝ} (hB : B.IsHermitian)
    (j : Fin (Fintype.card n))
    (hj : (Finset.univ.filter fun i => 0 < hB.eigenvalues₀ i).card ≤ j) :
    hB.eigenvalues₀ j ≤ 0 := by
  classical
  by_contra h
  have hpos : 0 < hB.eigenvalues₀ j := lt_of_not_ge h
  let f : Fin (j.val + 1) → {i : Fin (Fintype.card n) // 0 < hB.eigenvalues₀ i} := fun i =>
    ⟨⟨i, by omega⟩, hpos.trans_le (hB.eigenvalues₀_antitone (by
      change i.val ≤ j.val
      omega))⟩
  have hf : Function.Injective f := by
    intro i k h
    apply Fin.ext
    exact congrArg (fun t => t.val.val) h
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_subtype] at hc
  omega

/-- Positive eigenvalues of a negated symmetric matrix are counted by
negative eigenvalues of the original matrix. Horn--Johnson (2013),
Observation 4.2.5; helper for `low-rank-update-interlacing`. -/
theorem card_eigenvalues₀_pos_neg {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    (Finset.univ.filter fun i => 0 < hB.neg.eigenvalues₀ i).card =
      (Finset.univ.filter fun i => hB.eigenvalues₀ i < 0).card := by
  classical
  let e : {i : Fin (Fintype.card n) // 0 < hB.neg.eigenvalues₀ i} ≃
      {i : Fin (Fintype.card n) // hB.eigenvalues₀ i < 0} :=
    { toFun := fun i => ⟨i.val.rev, by
        simpa only [eigenvalues₀_neg hB, neg_pos] using i.property⟩
      invFun := fun i => ⟨i.val.rev, by
        simpa only [eigenvalues₀_neg hB, Fin.rev_rev, neg_pos] using i.property⟩
      left_inv := fun _ => Subtype.ext (Fin.rev_rev _)
      right_inv := fun _ => Subtype.ext (Fin.rev_rev _) }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e

/-- An update with `π` positive eigenvalues shifts the upper bound by
exactly `π` places in decreasing order. Horn--Johnson (2013), Corollary 4.3.3.
atlas: low-rank-update-interlacing (partial) -/
theorem eigenvalues₀_add_le_of_card_pos {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n))
    (hi : i.val + (Finset.univ.filter fun j => 0 < hB.eigenvalues₀ j).card < Fintype.card n) :
    (hA.add hB).eigenvalues₀
      ⟨i.val + (Finset.univ.filter fun j => 0 < hB.eigenvalues₀ j).card, hi⟩ ≤
        hA.eigenvalues₀ i := by
  let p := (Finset.univ.filter fun j => 0 < hB.eigenvalues₀ j).card
  have hp : p < Fintype.card n := by dsimp [p]; omega
  have hb := eigenvalues₀_le_zero_of_card_pos_le hB ⟨p, hp⟩ (by rfl)
  have h := eigenvalues₀_add_le hA hB (hA.add hB) i ⟨p, hp⟩ hi
  exact h.trans (by linarith)

/-- An update with `ν` negative eigenvalues gives the matching lower
bound, shifted by `ν` places in decreasing order.
Horn--Johnson (2013), Corollary 4.3.3.
atlas: low-rank-update-interlacing (partial) -/
theorem eigenvalues₀_le_add_of_card_neg {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n))
    (hi : i.val + (Finset.univ.filter fun j => hB.eigenvalues₀ j < 0).card < Fintype.card n) :
    hA.eigenvalues₀
      ⟨i.val + (Finset.univ.filter fun j => hB.eigenvalues₀ j < 0).card, hi⟩ ≤
        (hA.add hB).eigenvalues₀ i := by
  have hi' : i.val + (Finset.univ.filter fun j => 0 < hB.neg.eigenvalues₀ j).card <
      Fintype.card n := by rwa [card_eigenvalues₀_pos_neg hB]
  have h := eigenvalues₀_add_le_of_card_pos (hA.add hB) hB.neg i hi'
  simpa only [add_neg_cancel_right, card_eigenvalues₀_pos_neg hB] using h

/-- A symmetric update of rank at most `r` shifts the upper eigenvalue
bound by at most `r` indices. Horn--Johnson (2013), Corollary 4.3.5.
atlas: low-rank-update-interlacing (partial) -/
theorem eigenvalues₀_add_le_of_rank_le {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {r : ℕ} (hBr : B.rank ≤ r)
    (i : Fin (Fintype.card n)) (hi : i.val + r < Fintype.card n) :
    (hA.add hB).eigenvalues₀ ⟨i.val + r, hi⟩ ≤ hA.eigenvalues₀ i := by
  obtain ⟨W, hW, hAW⟩ := exists_submodule_le_eigenvalues₀_mul hA i
  have hker : Fintype.card n ≤ finrank ℝ (LinearMap.ker B.mulVecLin) + r := by
    have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h
    change finrank ℝ (LinearMap.range B.mulVecLin) ≤ r at hBr
    omega
  apply eigenvalues₀_le_of_forall_mem (hA.add hB) _ (W ⊓ LinearMap.ker B.mulVecLin)
    (card_le_finrank_inf_add hW hker)
  intro x hx
  have hxB : B *ᵥ x = 0 := hx.2
  simpa only [Matrix.add_mulVec, hxB, add_zero] using hAW x hx.1

/-- A rank-`r` symmetric update has the matching lower eigenvalue bound.
Horn--Johnson (2013), Corollary 4.3.5.
atlas: low-rank-update-interlacing (partial) -/
theorem eigenvalues₀_le_add_of_rank_le {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {r : ℕ} (hBr : B.rank ≤ r)
    (i : Fin (Fintype.card n)) (hi : i.val + r < Fintype.card n) :
    hA.eigenvalues₀ ⟨i.val + r, hi⟩ ≤ (hA.add hB).eigenvalues₀ i := by
  have h := eigenvalues₀_add_le_of_rank_le (hA.add hB) hB.neg
    (r := r) (by
      have hrank : (-B).rank = B.rank := by
        rw [show -B = (-1 : ℝ) • B by simp]
        exact Matrix.rank_smul_of_mem_nonZeroDivisors B
          (mem_nonZeroDivisors_of_ne_zero (by norm_num))
      simpa only [hrank] using hBr) i hi
  simpa only [add_neg_cancel_right] using h

/-- A PSD rank-one update has one-step decreasing-order interlacing.
Horn--Johnson (2013), Corollary 4.3.7.
atlas: low-rank-update-interlacing (partial) -/
theorem eigenvalues₀_rank_one_add_interlacing {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (z : n → ℝ) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i ≤
      (hA.add (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀ i ∧
    (∀ hi : i.val + 1 < Fintype.card n,
      (hA.add (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀
        ⟨i.val + 1, hi⟩ ≤ hA.eigenvalues₀ i) := by
  refine ⟨eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub hA
    (hA.add (posSemidef_vecMulVec_self_star z).isHermitian) ?_ i, ?_⟩
  · simpa only [add_sub_cancel_left] using posSemidef_vecMulVec_self_star z
  · intro hi
    exact eigenvalues₀_add_le_of_rank_le hA (posSemidef_vecMulVec_self_star z).isHermitian
      (r := 1) (Matrix.rank_vecMulVec_le _ _) i hi

/-- A PSD rank-one downdate has the corresponding reversed one-step
interlacing. Horn--Johnson (2013), Corollary 4.3.9.
atlas: low-rank-update-interlacing (partial) -/
theorem eigenvalues₀_rank_one_sub_interlacing {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (z : n → ℝ) (i : Fin (Fintype.card n)) :
    (hA.sub (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀ i ≤ hA.eigenvalues₀ i ∧
    (∀ hi : i.val + 1 < Fintype.card n,
      hA.eigenvalues₀ ⟨i.val + 1, hi⟩ ≤
        (hA.sub (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀ i) := by
  have h := eigenvalues₀_rank_one_add_interlacing
    (hA.sub (posSemidef_vecMulVec_self_star z).isHermitian) z i
  simpa only [sub_add_cancel] using h

/-- Symmetric updates obey both inertia-count shifts, both rank shifts,
and both PSD rank-one interlacing forms, with decreasing zero-based indices.
Horn--Johnson (2013), Corollaries 4.3.3, 4.3.5, 4.3.7, 4.3.9.
atlas: low-rank-update-interlacing -/
theorem eigenvalue_low_rank_interlacing {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∀ (i : Fin (Fintype.card n))
      (hi : i.val + (Finset.univ.filter fun j => 0 < hB.eigenvalues₀ j).card < Fintype.card n),
      (hA.add hB).eigenvalues₀
        ⟨i.val + (Finset.univ.filter fun j => 0 < hB.eigenvalues₀ j).card, hi⟩ ≤ hA.eigenvalues₀ i) ∧
    (∀ (i : Fin (Fintype.card n))
      (hi : i.val + (Finset.univ.filter fun j => hB.eigenvalues₀ j < 0).card < Fintype.card n),
      hA.eigenvalues₀
        ⟨i.val + (Finset.univ.filter fun j => hB.eigenvalues₀ j < 0).card, hi⟩ ≤
          (hA.add hB).eigenvalues₀ i) ∧
    (∀ r, B.rank ≤ r → ∀ (i : Fin (Fintype.card n)) (hi : i.val + r < Fintype.card n),
      (hA.add hB).eigenvalues₀ ⟨i.val + r, hi⟩ ≤ hA.eigenvalues₀ i ∧
      hA.eigenvalues₀ ⟨i.val + r, hi⟩ ≤ (hA.add hB).eigenvalues₀ i) ∧
    (∀ z i, hA.eigenvalues₀ i ≤
      (hA.add (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀ i ∧
      (∀ hi : i.val + 1 < Fintype.card n,
        (hA.add (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀
          ⟨i.val + 1, hi⟩ ≤ hA.eigenvalues₀ i)) ∧
    (∀ z i, (hA.sub (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀ i ≤
      hA.eigenvalues₀ i ∧ (∀ hi : i.val + 1 < Fintype.card n,
        hA.eigenvalues₀ ⟨i.val + 1, hi⟩ ≤
          (hA.sub (posSemidef_vecMulVec_self_star z).isHermitian).eigenvalues₀ i)) :=
  ⟨eigenvalues₀_add_le_of_card_pos hA hB, eigenvalues₀_le_add_of_card_neg hA hB,
    fun r hBr i hi => ⟨eigenvalues₀_add_le_of_rank_le hA hB (r := r) hBr i hi,
      eigenvalues₀_le_add_of_rank_le hA hB (r := r) hBr i hi⟩,
    eigenvalues₀_rank_one_add_interlacing hA, eigenvalues₀_rank_one_sub_interlacing hA⟩

end NLAlib
