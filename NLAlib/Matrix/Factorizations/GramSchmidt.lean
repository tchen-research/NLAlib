import NLAlib.Matrix.Factorizations.GramSchmidtClassical
/-!
# Modified Gram–Schmidt and its equality with the classical process

The total working-column recursion includes zero residuals. In exact arithmetic,
its output agrees with classical Gram–Schmidt for every input matrix; successful
processes therefore produce the same thin QR factorization. Importing this module
also exposes the classical process and its Mathlib correspondence.

Sources: Trefethen–Bau 1997, Lectures 7–8, Algorithms 7.1 and 8.1;
Golub–Van Loan 2013, §5.2.7–5.2.8. Realises `gram-schmidt`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {m : Type*} [Fintype m] {n : ℕ}

/-! ### Modified Gram–Schmidt -/

/-- The working columns of **modified Gram–Schmidt** after `k` steps (Trefethen–Bau Alg. 8.1):
start from the columns of `A`; step `k` (for `k < n`) normalises column `k` to
`q_k = w_k / ‖w_k‖` and removes its component from every later column,
`w_j ← w_j − (q_kᵀ w_j) q_k` (`j > k`); columns `< k` are left alone. After `n` steps column `j`
holds `q_j`. Trefethen–Bau 1997, Alg. 8.1; Golub–Van Loan 2013, Alg. 5.2.6.
atlas: gram-schmidt -/
def modifiedGramSchmidtState (A : Matrix m (Fin n) ℝ) : ℕ → Fin n → m → ℝ
  | 0 => fun j => A.col j
  | k + 1 => fun j =>
    if h : k < n then
      let w := modifiedGramSchmidtState A k ⟨k, h⟩
      let q := (√(w ⬝ᵥ w))⁻¹ • w
      if (j : ℕ) < k then modifiedGramSchmidtState A k j
      else if (j : ℕ) = k then q
      else modifiedGramSchmidtState A k j - (q ⬝ᵥ modifiedGramSchmidtState A k j) • q
    else modifiedGramSchmidtState A k j

/-- The `Q` factor of modified Gram–Schmidt (the working columns after `n` steps).
Trefethen–Bau 1997, Alg. 8.1.
atlas: gram-schmidt -/
def modifiedGramSchmidtQ (A : Matrix m (Fin n) ℝ) : Matrix m (Fin n) ℝ :=
  Matrix.of fun i j => modifiedGramSchmidtState A n j i

/-- The `R` factor of modified Gram–Schmidt: `r_ij = q_iᵀ w_j^{(i)}` for `i < j` (the working
column `j` before step `i`), `r_ii = ‖w_i^{(i)}‖`. Trefethen–Bau 1997, Alg. 8.1.
atlas: gram-schmidt -/
def modifiedGramSchmidtR (A : Matrix m (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i < j then modifiedGramSchmidtState A ((i : ℕ) + 1) i ⬝ᵥ modifiedGramSchmidtState A i j
    else if i = j then
      √(modifiedGramSchmidtState A i i ⬝ᵥ modifiedGramSchmidtState A i i)
    else 0

/-- The MGS invariant: after `k ≤ n` steps, working column `j` is `q_j` for `j < k` and
`a_j − ∑_{i<k} (q_iᵀ a_j) q_i` otherwise. Trefethen–Bau 1997, Lect. 8. -/
theorem modifiedGramSchmidtState_eq (A : Matrix m (Fin n) ℝ) :
    ∀ k ≤ n, ∀ j : Fin n, modifiedGramSchmidtState A k j =
      if (j : ℕ) < k then gramSchmidtCol A j
      else A.col j - ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < k),
        (gramSchmidtCol A l ⬝ᵥ A.col j) • gramSchmidtCol A l := by
  intro k
  induction k with
  | zero => intro _ j; simp [modifiedGramSchmidtState]
  | succ k ih =>
    intro hkn j
    have hk : k < n := hkn
    set K : Fin n := ⟨k, hk⟩ with hK
    have hfilt : Finset.univ.filter (fun l : Fin n => (l : ℕ) < k) = Finset.Iio K := by
      ext l; simp [Fin.lt_def, hK]
    have hw : modifiedGramSchmidtState A k K = gramSchmidtResidual A K := by
      rw [ih hk.le, if_neg (lt_irrefl _), hfilt, gramSchmidtResidual_eq_sum]
    have hq : (√(modifiedGramSchmidtState A k K ⬝ᵥ modifiedGramSchmidtState A k K))⁻¹ •
        modifiedGramSchmidtState A k K = gramSchmidtCol A K := by
      rw [hw, gramSchmidtCol_eq, norm_toLp_eq_sqrt_dotProduct_self]
    simp only [modifiedGramSchmidtState, dif_pos hk]
    rw [← hK, hq]
    rcases lt_trichotomy (j : ℕ) k with hjk | hjk | hjk
    · rw [if_pos hjk, ih hk.le, if_pos hjk, if_pos (by omega)]
    · rw [if_neg (by omega), if_pos hjk, if_pos (by omega)]
      rw [show j = K from Fin.ext hjk]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), ih hk.le, if_neg (by omega)]
      have hfilt' : Finset.univ.filter (fun l : Fin n => (l : ℕ) < k + 1) =
          insert K (Finset.univ.filter (fun l : Fin n => (l : ℕ) < k)) := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hK,
          Fin.ext_iff]; omega
      have hnot : K ∉ Finset.univ.filter (fun l : Fin n => (l : ℕ) < k) := by simp [hK]
      have hdot : gramSchmidtCol A K ⬝ᵥ (A.col j - ∑ l ∈ Finset.univ.filter
          (fun l : Fin n => (l : ℕ) < k), (gramSchmidtCol A l ⬝ᵥ A.col j) • gramSchmidtCol A l) =
          gramSchmidtCol A K ⬝ᵥ A.col j := by
        rw [dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero, sub_zero]
        intro l hl
        rw [dotProduct_smul, gramSchmidtCol_dotProduct_of_ne A, smul_zero]
        intro hKl; rw [← hKl] at hl; exact hnot hl
      rw [hdot, hfilt', Finset.sum_insert hnot]
      abel

/-- **MGS = CGS in exact arithmetic**: modified Gram–Schmidt computes the same `Q` and `R` as
classical Gram–Schmidt, for every `A` (breakdowns included). Trefethen–Bau 1997, Lect. 8
(MGS is a rearrangement of CGS); Golub–Van Loan 2013, §5.2.8. Proof: the invariant
`modifiedGramSchmidtState_eq`, with `q_kᵀ q_i = 0` for `i ≠ k`.
atlas: gram-schmidt -/
theorem modifiedGramSchmidt_eq (A : Matrix m (Fin n) ℝ) :
    modifiedGramSchmidtQ A = gramSchmidtQ A ∧ modifiedGramSchmidtR A = gramSchmidtR A := by
  have hres : ∀ i : Fin n, modifiedGramSchmidtState A i i = gramSchmidtResidual A i := by
    intro i
    rw [modifiedGramSchmidtState_eq A i i.isLt.le, if_neg (lt_irrefl _),
      gramSchmidtResidual_eq_sum]
    congr 2
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact Fin.lt_def.symm
  refine ⟨?_, ?_⟩
  · ext r j
    simp only [modifiedGramSchmidtQ, gramSchmidtQ, of_apply]
    rw [modifiedGramSchmidtState_eq A n le_rfl j, if_pos j.isLt]
  · ext i j
    simp only [modifiedGramSchmidtR, gramSchmidtR, of_apply]
    split_ifs with hij hij'
    · rw [modifiedGramSchmidtState_eq A _ i.isLt, if_pos (Nat.lt_succ_self _),
        modifiedGramSchmidtState_eq A i i.isLt.le, if_neg (by have := Fin.lt_def.1 hij; omega),
        dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero, sub_zero]
      intro l hl
      rw [dotProduct_smul, gramSchmidtCol_dotProduct_of_ne A, smul_zero]
      intro hil; rw [← hil] at hl; simp at hl
    · subst hij'; rw [hres]
    · rfl

/-- **Realisation of modified Gram–Schmidt**: when Gram–Schmidt succeeds (linearly independent
columns), MGS produces a thin QR of `A`. Trefethen–Bau 1997, Alg. 8.1, Thm 7.2;
Golub–Van Loan 2013, §5.2.8.
atlas: gram-schmidt -/
theorem isQR_modifiedGramSchmidt {A : Matrix m (Fin n) ℝ} (h : GramSchmidtSucceeds A) :
    IsQR A (modifiedGramSchmidtQ A) (modifiedGramSchmidtR A) := by
  rw [(modifiedGramSchmidt_eq A).1, (modifiedGramSchmidt_eq A).2]
  exact isQR_gramSchmidt h

end NLAlib
