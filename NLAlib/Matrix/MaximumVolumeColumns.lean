import NLAlib.Matrix.LeastSquares
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Finset.Max

/-!
# Existence of a maximum-volume independent column selection

When the requested size is at most the actual rank, a finite maximizer of the
column Gram determinant has positive volume and distinct selected indices.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A real finite matrix has a positive-volume selection of any number of
columns up to its actual rank, including the empty selection. This is basis
extraction from its own columns, with no generic-position hypothesis.
Supports `rank-revealing-qr`. -/
theorem exists_column_embedding_gram_det_pos {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, 0 < ((A.submatrix id e)ᵀ * A.submatrix id e).det := by
  classical
  have hEx : ∃ f : Fin A.rank → (m → ℝ), (∀ i, f i ∈ Set.range A.col) ∧
      LinearIndependent ℝ f := by
    obtain ⟨f, hf, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.col)
    have hdim := Matrix.rank_eq_finrank_span_cols A
    exact hdim.symm ▸ ⟨f, hf, hli⟩
  obtain ⟨f, hf, hli⟩ := hEx
  choose a ha using hf
  have hai : Function.Injective a := by
    intro i j hij
    apply hli.injective
    rw [← ha i, ← ha j, hij]
  let e : Fin k ↪ n := ⟨fun i => a (Fin.castLE hk i), hai.comp (Fin.castLE_injective hk)⟩
  have hCols : LinearIndependent ℝ (A.submatrix id e).col := by
    have heq : (A.submatrix id e).col = f ∘ Fin.castLE hk := by
      funext i
      exact ha (Fin.castLE hk i)
    rw [heq]
    exact hli.comp _ (Fin.castLE_injective hk)
  have hRank : (A.submatrix id e).rank = Fintype.card (Fin k) := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact finrank_span_eq_card hCols
  have hUnit := isUnit_transpose_mul_self_of_rank_eq hRank
  have hNonneg : 0 ≤ ((A.submatrix id e)ᵀ * A.submatrix id e).det := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (A.submatrix id e)).det_nonneg
  exact ⟨e, lt_of_le_of_ne hNonneg
    (Ne.symm ((Matrix.isUnit_iff_isUnit_det _).mp hUnit).ne_zero)⟩

/-- Among all ordered selections of `k` columns there is a positive Gram-volume
maximizer, and its indices are distinct. Maximizing over all functions also
covers column exchanges that create a repeated column, whose volume is zero.
Gu–Eisenstat 1996, maximum-volume existence proof; supports `rank-revealing-qr`. -/
theorem exists_maximum_volume_column_embedding {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n,
      0 < ((A.submatrix id e)ᵀ * A.submatrix id e).det ∧
      ∀ f : Fin k → n,
        ((A.submatrix id f)ᵀ * A.submatrix id f).det ≤
          ((A.submatrix id e)ᵀ * A.submatrix id e).det := by
  classical
  obtain ⟨e₀, he₀⟩ := exists_column_embedding_gram_det_pos A k hk
  let volume := fun f : Fin k → n => ((A.submatrix id f)ᵀ * A.submatrix id f).det
  obtain ⟨f, _, hf⟩ := Finset.exists_max_image Finset.univ volume
    ⟨(e₀ : Fin k → n), Finset.mem_univ _⟩
  have hpos : 0 < volume f := he₀.trans_le (hf e₀ (Finset.mem_univ _))
  have hfi : Function.Injective f := by
    intro i j hij
    by_contra hne
    apply hpos.ne'
    apply Matrix.det_zero_of_column_eq hne
    intro a
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
    rw [hij]
  exact ⟨⟨f, hfi⟩, hpos, fun g => hf g (Finset.mem_univ _)⟩

end NLAlib
