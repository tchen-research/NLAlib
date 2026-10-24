/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Spectral.EckartYoung
/-!
# SVD-derived right-space blocks with optimal tail

The first `k` right singular vectors and their complement give the blocks used
by the HMT range-finder theorem. The head singular values are absorbed into
`U₁ = A V₁`, so its head factor is the identity. The tail is obtained from the
SVD and has squared Frobenius norm equal to the rank-constrained optimum.
The block construction is generic over real or complex scalars.
HMT 2011, Theorems 9.1 and 10.5; atlas `rsvd-expected-error`, `gn-expected-error`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The padded squared singular-value tail has the same value when summed over
the input width as over its height. Source: HMT (2011), §2.1 and Theorem 10.5;
used by volume-sampling Frobenius error. Empty matrix dimensions are included. -/
theorem bestRankFrobSq_eq_sum_width {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    bestRankFrobSq A k =
      ∑ i : Fin n, if k ≤ (i : ℕ) then singularValues A i ^ 2 else 0 := by
  let f : ℕ → ℝ := fun i => if k ≤ i then singularValues A i ^ 2 else 0
  have hsum (d : ℕ) (hd : min m n ≤ d) :
      (∑ i ∈ Finset.range d, f i) = ∑ i ∈ Finset.range (min m n), f i := by
    symm
    apply Finset.sum_subset (Finset.range_mono hd)
    intro i _ hi
    have hz := singularValues_eq_zero_of_min_le A (k := i)
      (by simpa only [Finset.mem_range, not_lt, Fintype.card_fin] using hi)
    simp [f, hz]
  have hm := hsum m (min_le_left m n)
  have hn := hsum n (min_le_right m n)
  change (∑ i ∈ Finset.range (Fintype.card (Fin m)), f i) = ∑ i : Fin n, f i
  rw [Fintype.card_fin, Fin.sum_univ_eq_sum_range f]
  exact hm.trans hn.symm

/-- Every real or complex matrix has an SVD-derived right-space block split whose
tail has both the exact next singular value and the optimal squared rank-`k` error.
The spectral identification was previously duplicated in the real Gaussian range-finder
consumer; the shared construction now serves both scalar fields. The head singular values
are absorbed into `U₁=A V₁`, as permitted by HMT's structural lemma.
Only `k≤n` is needed; `k>m` is handled by the padded zero singular values.
HMT 2011, Theorem 9.1; atlas `rsvd-expected-error`, `gn-expected-error`. -/
theorem exists_svd_right_blocks_specNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    (k : ℕ) (hkn : k ≤ n) :
    ∃ (r : ℕ) (U₁ : Matrix (Fin m) (Fin k) 𝕜) (U₂ : Matrix (Fin m) (Fin m) 𝕜)
      (V₁ : Matrix (Fin n) (Fin k) 𝕜) (V₂ : Matrix (Fin n) (Fin r) 𝕜)
      (S₂ : Matrix (Fin m) (Fin r) 𝕜),
      A = U₁ * (1 : Matrix (Fin k) (Fin k) 𝕜) * V₁ᴴ + U₂ * S₂ * V₂ᴴ ∧
      HasOrthonormalCols U₂ ∧ HasOrthonormalCols V₁ ∧ HasOrthonormalCols V₂ ∧
      V₁ᴴ * V₂ = 0 ∧ specNorm S₂ = singularValues A k ∧
      frobSq S₂ = bestRankFrobSq A k := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  obtain ⟨U, V, h⟩ := exists_isSVD A
  let V₁ : Matrix (Fin (k + r)) (Fin k) 𝕜 := V.submatrix id (Fin.castAdd r)
  let V₂ : Matrix (Fin (k + r)) (Fin r) 𝕜 := V.submatrix id (Fin.natAdd k)
  let D : Matrix (Fin m) (Fin (k + r)) 𝕜 := rectDiag (singularValues A)
  let S₂ : Matrix (Fin m) (Fin r) 𝕜 := D.submatrix id (Fin.natAdd k)
  have hV₁ : HasOrthonormalCols V₁ := by
    change V₁ᴴ * V₁ = 1
    have he : V₁ᴴ * V₁ = (Vᴴ * V).submatrix (Fin.castAdd r) (Fin.castAdd r) := rfl
    rw [he, show Vᴴ * V = 1 from h.conjTranspose_mul_right]
    ext i j
    simp [Matrix.one_apply, Fin.castAdd_inj]
  have hV₂ : HasOrthonormalCols V₂ := by
    change V₂ᴴ * V₂ = 1
    have he : V₂ᴴ * V₂ = (Vᴴ * V).submatrix (Fin.natAdd k) (Fin.natAdd k) := rfl
    rw [he, show Vᴴ * V = 1 from h.conjTranspose_mul_right]
    ext i j
    simp [Matrix.one_apply, Fin.natAdd_inj]
  have hcross : V₁ᴴ * V₂ = 0 := by
    have he : V₁ᴴ * V₂ = (Vᴴ * V).submatrix (Fin.castAdd r) (Fin.natAdd k) := rfl
    rw [he, show Vᴴ * V = 1 from h.conjTranspose_mul_right]
    ext i j
    have hij : Fin.castAdd r i ≠ Fin.natAdd k j := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp [hij]
  have hcomplete : V₁ * V₁ᴴ + V₂ * V₂ᴴ = 1 := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin (k + r)) (Fin (k + r)) 𝕜 => M i j)
      (show V * Vᴴ = 1 from h.mul_conjTranspose_right)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_add,
      Matrix.add_apply, V₁, V₂, Matrix.submatrix_apply, id_eq] using he
  have hAV₂ : A * V₂ = U * S₂ := by
    have he : A * V₂ = (A * V).submatrix id (Fin.natAdd k) := rfl
    rw [h.mul_right] at he
    exact he
  have hA : A = (A * V₁) * (1 : Matrix (Fin k) (Fin k) 𝕜) * V₁ᴴ + U * S₂ * V₂ᴴ := by
    calc
      A = A * (V₁ * V₁ᴴ + V₂ * V₂ᴴ) := by rw [hcomplete, Matrix.mul_one]
      _ = (A * V₁) * (1 : Matrix (Fin k) (Fin k) 𝕜) * V₁ᴴ + U * S₂ * V₂ᴴ := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc A V₁, ← Matrix.mul_assoc A V₂,
          hAV₂, Matrix.mul_one]
  let T : Matrix (Fin m) (Fin (k + r)) 𝕜 :=
    rectDiag (fun i => if i < k then 0 else singularValues A i)
  have hST : S₂ * V₂ᴴ = T * Vᴴ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_add]
    have hhead : ∑ a : Fin k, T i (Fin.castAdd r a) * star (V j (Fin.castAdd r a)) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases hd : (i : ℕ) = a
      · simp [T, rectDiag_apply_ofReal, hd]
      · simp [T, rectDiag_apply_ofReal, hd]
    rw [hhead, zero_add]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hd : (i : ℕ) = k + b
    · simp [S₂, D, V₂, T, rectDiag_apply_ofReal, hd]
    · simp [S₂, D, V₂, T, rectDiag_apply_ofReal, hd]
  have htail : U * S₂ * V₂ᴴ = A - h.truncatedMatrix k := by
    have hsplit : A = h.truncatedMatrix k + U * T * Vᴴ := h.eq_head_add_tail k
    calc U * S₂ * V₂ᴴ = U * T * Vᴴ := by rw [Matrix.mul_assoc, hST, ← Matrix.mul_assoc]
      _ = (h.truncatedMatrix k + U * T * Vᴴ) - h.truncatedMatrix k := by abel
      _ = A - h.truncatedMatrix k := by rw [← hsplit]
  have hspec : specNorm S₂ = singularValues A k := by
    rw [← h.specNorm_sub_truncatedMatrix k, ← htail,
      specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV₂,
      specNorm_mul_left_of_hasOrthonormalCols h.conjTranspose_mul_left]
  have hfrob : frobSq S₂ = bestRankFrobSq A k := by
    rw [← h.frobSq_sub_truncatedMatrix k, ← htail,
      frobSq_mul_right_of_orthonormal hV₂.conjTranspose_mul_self,
      frobSq_mul_left_of_orthonormal h.conjTranspose_mul_left]
  exact ⟨r, A * V₁, U, V₁, V₂, S₂, hA, h.conjTranspose_mul_left, hV₁, hV₂, hcross, hspec, hfrob⟩

/-- The Frobenius-only interface to the same generic SVD block construction. The stronger
`exists_svd_right_blocks_specNorm` also identifies the first tail singular value.
Source: HMT (2011), Theorem 9.1; supports `rsvd-expected-error`, `gn-expected-error`. -/
theorem exists_svd_right_blocks {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    (k : ℕ) (hkn : k ≤ n) :
    ∃ (r : ℕ) (U₁ : Matrix (Fin m) (Fin k) 𝕜) (U₂ : Matrix (Fin m) (Fin m) 𝕜)
      (V₁ : Matrix (Fin n) (Fin k) 𝕜) (V₂ : Matrix (Fin n) (Fin r) 𝕜)
      (S₂ : Matrix (Fin m) (Fin r) 𝕜),
      A = U₁ * (1 : Matrix (Fin k) (Fin k) 𝕜) * V₁ᴴ + U₂ * S₂ * V₂ᴴ ∧
      HasOrthonormalCols U₂ ∧ HasOrthonormalCols V₁ ∧ HasOrthonormalCols V₂ ∧
      V₁ᴴ * V₂ = 0 ∧ frobSq S₂ = bestRankFrobSq A k := by
  obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, _, hF⟩ :=
    exists_svd_right_blocks_specNorm A k hkn
  exact ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, hF⟩

end NLAlib
