import NLAlib.Matrix.EckartYoung

/-!
# SVD-derived right-space blocks with genuine optimal tail

The first `k` right singular vectors and their complement give the blocks used
by the HMT range-finder theorem. The head singular values are absorbed into
`U₁ = A V₁`, so its head factor is the identity. The tail is obtained from the
actual SVD and has squared Frobenius norm equal to the rank-constrained optimum.
HMT 2011, Theorems 9.1 and 10.5; atlas `rsvd-expected-error`, `gn-expected-error`.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

private theorem singularValueTailSq_eq_sum_width {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularValueTailSq A k =
      ∑ i : Fin n, if k ≤ (i : ℕ) then singularValues A i ^ 2 else 0 := by
  let f : ℕ → ℝ := fun i => if k ≤ i then singularValues A i ^ 2 else 0
  have hsum (d : ℕ) (hd : min m n ≤ d) :
      (∑ i ∈ Finset.range d, f i) = ∑ i ∈ Finset.range (min m n), f i := by
    symm
    apply Finset.sum_subset (Finset.range_mono hd)
    intro i _ hi
    have hz := singularValues_eq_zero_of_min_le A (k := i)
      (by simpa only [Finset.mem_range, not_lt] using hi)
    simp [f, hz]
  have hm := hsum m (min_le_left m n)
  have hn := hsum n (min_le_right m n)
  change (∑ i : Fin m, f i) = ∑ i : Fin n, f i
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  exact hm.trans hn.symm

/-- Every actual real matrix has an SVD-derived right-space block split whose
tail is the genuine optimal squared rank-`k` error. The head singular values
are absorbed into `U₁=A V₁`, as permitted by HMT's structural lemma.
Only `k≤n` is needed; `k>m` is handled by the padded zero singular values.
HMT 2011, Theorem 9.1; atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem exists_svd_right_blocks {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) (hkn : k ≤ n) :
    ∃ (r : ℕ) (U₁ : Matrix (Fin m) (Fin k) ℝ) (U₂ : Matrix (Fin m) (Fin m) ℝ)
      (V₁ : Matrix (Fin n) (Fin k) ℝ) (V₂ : Matrix (Fin n) (Fin r) ℝ)
      (S₂ : Matrix (Fin m) (Fin r) ℝ),
      A = U₁ * (1 : Matrix (Fin k) (Fin k) ℝ) * V₁ᵀ + U₂ * S₂ * V₂ᵀ ∧
      HasOrthonormalCols U₂ ∧ HasOrthonormalCols V₁ ∧ HasOrthonormalCols V₂ ∧
      V₁ᵀ * V₂ = 0 ∧ frobSq S₂ = bestRankFrobSq k A := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  obtain ⟨U, V, h⟩ := exists_isSVD A
  let V₁ : Matrix (Fin (k + r)) (Fin k) ℝ := V.submatrix id (Fin.castAdd r)
  let V₂ : Matrix (Fin (k + r)) (Fin r) ℝ := V.submatrix id (Fin.natAdd k)
  let D : Matrix (Fin m) (Fin (k + r)) ℝ := rectDiag (singularValues A)
  let S₂ : Matrix (Fin m) (Fin r) ℝ := D.submatrix id (Fin.natAdd k)
  have hV₁ : HasOrthonormalCols V₁ := by
    change V₁ᵀ * V₁ = 1
    have he : V₁ᵀ * V₁ = (Vᵀ * V).submatrix (Fin.castAdd r) (Fin.castAdd r) := rfl
    rw [he, h.transpose_mul_right]
    ext i j
    simp [Matrix.one_apply, Fin.castAdd_inj]
  have hV₂ : HasOrthonormalCols V₂ := by
    change V₂ᵀ * V₂ = 1
    have he : V₂ᵀ * V₂ = (Vᵀ * V).submatrix (Fin.natAdd k) (Fin.natAdd k) := rfl
    rw [he, h.transpose_mul_right]
    ext i j
    simp [Matrix.one_apply, Fin.natAdd_inj]
  have hcross : V₁ᵀ * V₂ = 0 := by
    have he : V₁ᵀ * V₂ = (Vᵀ * V).submatrix (Fin.castAdd r) (Fin.natAdd k) := rfl
    rw [he, h.transpose_mul_right]
    ext i j
    have hij : Fin.castAdd r i ≠ Fin.natAdd k j := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp [hij]
  have hcomplete : V₁ * V₁ᵀ + V₂ * V₂ᵀ = 1 := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin (k + r)) (Fin (k + r)) ℝ => M i j)
      h.mul_transpose_right
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_add,
      Matrix.add_apply, V₁, V₂, Matrix.submatrix_apply, id_eq] using he
  have hAV₂ : A * V₂ = U * S₂ := by
    have he : A * V₂ = (A * V).submatrix id (Fin.natAdd k) := rfl
    rw [h.mul_right] at he
    exact he
  have hA : A = (A * V₁) * (1 : Matrix (Fin k) (Fin k) ℝ) * V₁ᵀ + U * S₂ * V₂ᵀ := by
    calc
      A = A * (V₁ * V₁ᵀ + V₂ * V₂ᵀ) := by rw [hcomplete, Matrix.mul_one]
      _ = (A * V₁) * (1 : Matrix (Fin k) (Fin k) ℝ) * V₁ᵀ + U * S₂ * V₂ᵀ := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc A V₁, ← Matrix.mul_assoc A V₂,
          hAV₂, Matrix.mul_one]
  have hcolumn (j : Fin r) : (∑ i : Fin m, S₂ i j ^ 2) =
      singularValues A (k + (j : ℕ)) ^ 2 := by
    by_cases hjm : k + (j : ℕ) < m
    · rw [Finset.sum_eq_single (⟨k + j, hjm⟩ : Fin m)]
      · simp [S₂, D, rectDiag_apply]
      · intro i _ hi
        have hival : (i : ℕ) ≠ k + j := fun he => hi (Fin.ext he)
        simp [S₂, D, rectDiag_apply, hival]
      · simp
    · rw [singularValues_eq_zero_of_height_le A (not_lt.mp hjm)]
      simp only [zero_pow (by decide : 2 ≠ 0)]
      apply Finset.sum_eq_zero
      intro i _
      have hival : (i : ℕ) ≠ k + j := fun he => hjm (he ▸ i.isLt)
      simp [S₂, D, rectDiag_apply, hival]
  have hF : frobSq S₂ = ∑ j : Fin r, singularValues A (k + (j : ℕ)) ^ 2 := by
    rw [frobSq_eq_sum_sq, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hcolumn j)
  have htail : singularValueTailSq A k =
      ∑ j : Fin r, singularValues A (k + (j : ℕ)) ^ 2 := by
    rw [singularValueTailSq_eq_sum_width, Fin.sum_univ_add]
    have hhead : (∑ i : Fin k, if k ≤ ((Fin.castAdd r i : Fin (k + r)) : ℕ)
        then singularValues A (Fin.castAdd r i) ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [not_le.mpr i.isLt]
    rw [hhead, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    simp
  refine ⟨r, A * V₁, U, V₁, V₂, S₂, hA, h.transpose_mul_left, hV₁, hV₂, hcross, ?_⟩
  rw [hF, bestRankFrobSq_eq_singularValueTailSq, htail]

end NLAlib
