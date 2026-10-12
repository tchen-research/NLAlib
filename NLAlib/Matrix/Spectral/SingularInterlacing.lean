import NLAlib.Matrix.Spectral.LowRankInterlacing
import NLAlib.Matrix.Spectral.EigenvalueEquality
import NLAlib.Matrix.Spectral.SingularValueInvariance
/-!
# Singular-value interlacing under row and column deletion

Selecting rows splits the column Gram matrix into the selected and omitted
row Grams. Low-rank eigenvalue interlacing gives the lower shift and PSD
order gives the upper bound. Transposition treats columns, and combining
the two gives arbitrary submatrix interlacing on the actual padded singular
list. Source: Horn--Johnson (2013), Corollary 7.3.6.
Atlas: `singular-value-interlacing`.
-/

noncomputable section
open Matrix

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype n] [DecidableEq n] [DecidableEq p] in
/-- A row selection and its omitted rows split the column Gram matrix.
Horn--Johnson (2013), Corollary 7.3.6;
helper for `singular-value-interlacing`. -/
theorem transpose_mul_eq_selected_omitted_grams (A : Matrix m n ℝ)
    (f : p → m) (hf : Function.Injective f) :
    Aᵀ * A = (A.submatrix f id)ᵀ * A.submatrix f id +
      (A.submatrix (Subtype.val : {i : m // i ∉ Set.range f} → m) id)ᵀ *
        A.submatrix (Subtype.val : {i : m // i ∉ Set.range f} → m) id := by
  classical
  let : Fintype (Set.range f) := Subtype.fintype (fun i => i ∈ Set.range f)
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Function.id_def, Matrix.add_apply]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range f)
    (fun k => A k i * A k j)
  have hselected : (∑ k : Set.range f, A k i * A k j) =
      ∑ k : p, A (f k) i * A (f k) j := by
    exact ((Equiv.ofInjective f hf).sum_comp (fun k : Set.range f => A k i * A k j)).symm
  rw [hselected] at hsplit
  exact hsplit.symm

omit [DecidableEq p] in
/-- Row selection cannot increase any singular value, including padded
zeros. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem toEuclideanLin_singularValues_submatrix_rows_le (A : Matrix m n ℝ)
    (f : p → m) (hf : Function.Injective f) (k : ℕ) :
    (A.submatrix f id).toEuclideanLin.singularValues k ≤ A.toEuclideanLin.singularValues k := by
  classical
  by_cases hk : k < Fintype.card n
  · let D := A.submatrix (Subtype.val : {i : m // i ∉ Set.range f} → m) id
    have hd : (Aᵀ * A - (A.submatrix f id)ᵀ * A.submatrix f id).PosSemidef := by
      rw [transpose_mul_eq_selected_omitted_grams A f hf, add_sub_cancel_left]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self D
    have h := eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub
      (Matrix.isHermitian_conjTranspose_mul_self (A.submatrix f id))
      (Matrix.isHermitian_conjTranspose_mul_self A) hd ⟨k, hk⟩
    rw [← sq_toEuclideanLin_singularValues_eq_eigenvalues₀ (A.submatrix f id) ⟨k, hk⟩,
      ← sq_toEuclideanLin_singularValues_eq_eigenvalues₀ A ⟨k, hk⟩] at h
    nlinarith [(A.submatrix f id).toEuclideanLin.singularValues_nonneg k,
      A.toEuclideanLin.singularValues_nonneg k]
  · rw [LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le]
    all_goals simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk

omit [DecidableEq p] in
/-- Deleting rows shifts the lower singular-value bound by exactly the
number of omitted rows. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem toEuclideanLin_singularValues_le_submatrix_rows (A : Matrix m n ℝ)
    (f : p → m) (hf : Function.Injective f) (k : ℕ) :
    A.toEuclideanLin.singularValues (k + (Fintype.card m - Fintype.card p)) ≤
      (A.submatrix f id).toEuclideanLin.singularValues k := by
  classical
  let D := A.submatrix (Subtype.val : {i : m // i ∉ Set.range f} → m) id
  have hc : Fintype.card {i : m // i ∉ Set.range f} = Fintype.card m - Fintype.card p := by
    rw [Fintype.card_subtype_compl, Set.card_range_of_injective hf]
  by_cases hk : k + (Fintype.card m - Fintype.card p) < Fintype.card n
  · have hk₀ : k < Fintype.card n := by omega
    have hr : (Dᵀ * D).rank ≤ Fintype.card m - Fintype.card p := by
      rw [← hc]
      exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height D)
    have h := eigenvalues₀_add_le_of_rank_le
      (Matrix.isHermitian_conjTranspose_mul_self (A.submatrix f id))
      (Matrix.isHermitian_conjTranspose_mul_self D) hr ⟨k, hk₀⟩ hk
    have hGram := transpose_mul_eq_selected_omitted_grams A f hf
    change Aᵀ * A = (A.submatrix f id)ᵀ * A.submatrix f id + Dᵀ * D at hGram
    have heig := eigenvalues₀_eq_of_matrix_eq
      ((Matrix.isHermitian_conjTranspose_mul_self (A.submatrix f id)).add
        (Matrix.isHermitian_conjTranspose_mul_self D))
      (Matrix.isHermitian_conjTranspose_mul_self A)
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hGram.symm)
    rw [heig] at h
    rw [← sq_toEuclideanLin_singularValues_eq_eigenvalues₀ A
      ⟨k + (Fintype.card m - Fintype.card p), hk⟩,
      ← sq_toEuclideanLin_singularValues_eq_eigenvalues₀ (A.submatrix f id) ⟨k, hk₀⟩] at h
    nlinarith [A.toEuclideanLin.singularValues_nonneg (k + (Fintype.card m - Fintype.card p)),
      (A.submatrix f id).toEuclideanLin.singularValues_nonneg k]
  · rw [LinearMap.singularValues_of_finrank_le]
    · exact (A.submatrix f id).toEuclideanLin.singularValues_nonneg k
    · simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk

/-- Column selection cannot increase any singular value.
Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem toEuclideanLin_singularValues_submatrix_cols_le (A : Matrix m n ℝ)
    (f : p → n) (hf : Function.Injective f) (k : ℕ) :
    (A.submatrix id f).toEuclideanLin.singularValues k ≤ A.toEuclideanLin.singularValues k := by
  have h := toEuclideanLin_singularValues_submatrix_rows_le Aᵀ f hf k
  rw [← Matrix.transpose_submatrix, toEuclideanLin_singularValues_transpose,
    toEuclideanLin_singularValues_transpose] at h
  exact h

/-- Deleting columns shifts the lower singular-value bound by the number
of omitted columns. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem toEuclideanLin_singularValues_le_submatrix_cols (A : Matrix m n ℝ)
    (f : p → n) (hf : Function.Injective f) (k : ℕ) :
    A.toEuclideanLin.singularValues (k + (Fintype.card n - Fintype.card p)) ≤
      (A.submatrix id f).toEuclideanLin.singularValues k := by
  have h := toEuclideanLin_singularValues_le_submatrix_rows Aᵀ f hf k
  rw [← Matrix.transpose_submatrix, toEuclideanLin_singularValues_transpose,
    toEuclideanLin_singularValues_transpose] at h
  exact h

/-- Arbitrary row and column deletion gives the full singular-value
interlacing interval, with the total number of deleted coordinates as the
lower shift. Taking one omitted coordinate gives the one-step interlacing
chain; all statements use the actual padded singular values.
Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing -/
theorem toEuclideanLin_singularValues_submatrix_interlacing
    {q : Type*} [Fintype q] [DecidableEq q] (A : Matrix m n ℝ)
    (f : p → m) (g : q → n) (hf : Function.Injective f) (hg : Function.Injective g) (k : ℕ) :
    A.toEuclideanLin.singularValues
      (k + (Fintype.card m - Fintype.card p) + (Fintype.card n - Fintype.card q)) ≤
        (A.submatrix f g).toEuclideanLin.singularValues k ∧
    (A.submatrix f g).toEuclideanLin.singularValues k ≤ A.toEuclideanLin.singularValues k := by
  have hc := toEuclideanLin_singularValues_le_submatrix_cols (A.submatrix f id) g hg k
  have hr := toEuclideanLin_singularValues_le_submatrix_rows A f hf
    (k + (Fintype.card n - Fintype.card q))
  have hcu := toEuclideanLin_singularValues_submatrix_cols_le (A.submatrix f id) g hg k
  have hru := toEuclideanLin_singularValues_submatrix_rows_le A f hf k
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at hc hcu
  refine ⟨?_, hcu.trans hru⟩
  have hidx : k + (Fintype.card m - Fintype.card p) + (Fintype.card n - Fintype.card q) =
      k + (Fintype.card n - Fintype.card q) + (Fintype.card m - Fintype.card p) := by omega
  rw [hidx]
  exact hr.trans hc

end NLAlib
