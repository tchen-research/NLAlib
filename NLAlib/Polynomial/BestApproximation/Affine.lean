import NLAlib.Polynomial.BestApproximation.MinimaxError

/-!
# Affine invariance of minimax error

Pullback by an affine bijection preserves degree-bounded best uniform approximation.
Source: Trefethen, ATAP, Chapter 10; the supplied operator rederivations, `polybest:minimax`.
Atlas: `minimax-error-def`.
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- Pullback by an affine map cannot increase the minimax error.
Source: ATAP, Chapter 10. -/
theorem minimaxError_comp_le_of_affine {s t : Set ℝ} [CompactSpace s] [CompactSpace t]
    (n : ℕ) (f : C(t, ℝ)) (h : C(s, t)) (α β : ℝ)
    (haff : ∀ x : s, (h x : ℝ) = α * (x : ℝ) + β) :
    minimaxError n (f.comp h) ≤ minimaxError n f := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_norm_sub_eq_minimaxError n f
  let q : ℝ[X] := p.comp (C α * X + C β)
  have hlin : (C α * X + C β : ℝ[X]).natDegree ≤ 1 := by
    exact natDegree_add_le_of_degree_le
      ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp)
  have hpn : p.natDegree ≤ n := natDegree_le_iff_degree_le.mpr hp
  have hq : q.degree ≤ n := by
    apply degree_le_natDegree.trans
    exact_mod_cast (natDegree_comp_le.trans
      (Nat.mul_le_mul hpn hlin)).trans (by simp : n * 1 ≤ n)
  have herr : ‖f.comp h - q.toContinuousMapOn s‖ ≤ ‖f - p.toContinuousMapOn t‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    convert (f - p.toContinuousMapOn t).norm_coe_le_norm (h x) using 1
    simp [q, haff]
  exact (minimaxError_le_norm_sub (f.comp h)
    (mem_polynomialApproximationSpace_iff.mpr ⟨q, hq, rfl⟩)).trans (herr.trans_eq hfp)

/-- An affine homeomorphism preserves the best uniform polynomial approximation error.
Source: ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_comp_homeomorph_of_affine {s t : Set ℝ}
    [CompactSpace s] [CompactSpace t] (n : ℕ) (f : C(t, ℝ)) (h : s ≃ₜ t)
    (α β : ℝ) (hα : α ≠ 0) (haff : ∀ x : s, (h x : ℝ) = α * (x : ℝ) + β) :
    minimaxError n (f.comp ⟨h, h.continuous⟩) = minimaxError n f := by
  apply le_antisymm (minimaxError_comp_le_of_affine n f ⟨h, h.continuous⟩ α β haff)
  have hinv : ∀ y : t, (h.symm y : ℝ) = α⁻¹ * (y : ℝ) + (-β / α) := by
    intro y
    have heq := haff (h.symm y)
    simp only [h.apply_symm_apply] at heq
    field_simp
    nlinarith
  have hle := minimaxError_comp_le_of_affine n (f.comp ⟨h, h.continuous⟩)
    ⟨h.symm, h.symm.continuous⟩ α⁻¹ (-β / α) hinv
  have heq : (f.comp ⟨h, h.continuous⟩).comp ⟨h.symm, h.symm.continuous⟩ = f := by ext y; simp
  rwa [heq] at hle

/-- Rescaling `[-1,1]` affinely onto `[a,b]` preserves the degree-`n` best uniform error.
The map is `x ↦ ((b-a)x+a+b)/2`. Source: Trefethen, ATAP, Chapter 10.
Together with the other minimax-error declarations this supplies the complete defining API.
atlas: minimax-error-def -/
theorem minimaxError_comp_affine_interval (n : ℕ) {a b : ℝ} (hab : a < b)
    (f : C(Set.Icc a b, ℝ)) :
    minimaxError n
      (f.comp ⟨((iccHomeoI (-1 : ℝ) 1 (by norm_num)).trans
        (iccHomeoI a b hab).symm), Homeomorph.continuous _⟩) = minimaxError n f := by
  apply minimaxError_comp_homeomorph_of_affine n f _ ((b - a) / 2) ((a + b) / 2)
  · exact div_ne_zero (sub_ne_zero.mpr hab.ne') (by norm_num)
  · intro x
    simp only [Homeomorph.trans_apply, iccHomeoI_symm_apply_coe, iccHomeoI_apply_coe]
    ring

end NLAlib
