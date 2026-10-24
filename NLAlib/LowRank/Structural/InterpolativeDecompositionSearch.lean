import NLAlib.LowRank.Structural.InterpolativeDecomposition
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.VecNotation

/-!
# Finite exact-comparison search for interpolative decomposition

The selection algorithm enumerates finite column maps lexicographically, filters
the distinct selections, and scans their Gram determinants. Only a strictly larger
volume replaces the current choice, so ties retain the first enumerated embedding.
The returned coefficients are the actual Gram-inverse normal-equation formula.

This is an exhaustive finite algorithm in the exact-real arithmetic/comparison
model. It makes no efficiency or binary representation claim for arbitrary real data.
No finished existence theorem is used to choose its output.

Source: HMT 2011, §4.2; Gu–Eisenstat 1996, Theorem 3.2; the ID search route in
`sketching_lowrank_routes_2026_10_24/deterministic_lra.tex`.
Atlas: `interpolative-decomposition` (algorithm realization).
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Enumerate all length-`k` column maps in lexicographic order. The empty map
is enumerated once, even when the ambient column set is empty. -/
def columnSelectionList (n : ℕ) : (k : ℕ) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap (fun i =>
      (columnSelectionList n k).map (fun t => Fin.cons i t))

/-- Every finite column map occurs in the explicit recursive enumeration. -/
theorem mem_columnSelectionList {n k : ℕ} (f : Fin k → Fin n) : f ∈ columnSelectionList n k := by
  induction k with
  | zero =>
    have he : f = Fin.elim0 := Subsingleton.elim _ _
    simp only [columnSelectionList, List.mem_singleton]
    exact he
  | succ k ih =>
    rw [columnSelectionList, List.mem_flatMap]
    refine ⟨f 0, by simp, ?_⟩
    rw [List.mem_map]
    exact ⟨Fin.tail f, ih _, Fin.cons_self_tail f⟩

/-- Filter the lexicographic column maps to distinct-column embeddings, preserving
their enumeration order. Injectivity is a finite decidable comparison of indices. -/
def columnEmbeddingList (n k : ℕ) : List (Fin k ↪ Fin n) :=
  (columnSelectionList n k).filterMap (fun f =>
    if h : Function.Injective f then some ⟨f, h⟩ else none)

/-- Every column embedding occurs in the filtered finite enumeration. -/
theorem mem_columnEmbeddingList {n k : ℕ} (e : Fin k ↪ Fin n) : e ∈ columnEmbeddingList n k := by
  rw [columnEmbeddingList, List.mem_filterMap]
  refine ⟨e, mem_columnSelectionList e, ?_⟩
  rw [dif_pos e.injective]
  congr 1

/-- Scan the explicit embedding list for the maximum Gram determinant, which is
the squared selected-column volume. Exact real comparisons are the data-dependent
tests. A strict improvement replaces the candidate; equal scores keep the first.
Invalid sizes may return `none`. -/
def maximumVolumeColumnSearch {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Option (Fin k ↪ Fin n) :=
  (columnEmbeddingList n k).argmax (fun e => ((A.submatrix id e)ᵀ * A.submatrix id e).det)

/-- The selection is explicitly a finite comparison fold over the enumerated
embeddings, with no choice of a completed ID witness hidden in the definition.
atlas: interpolative-decomposition (partial) -/
theorem maximumVolumeColumnSearch_eq_foldl {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    maximumVolumeColumnSearch A k = (columnEmbeddingList n k).foldl
      (fun acc e => match acc with
        | none => some e
        | some c => if ((A.submatrix id c)ᵀ * A.submatrix id c).det <
            ((A.submatrix id e)ᵀ * A.submatrix id e).det then some e else some c) none := by
  unfold maximumVolumeColumnSearch List.argmax
  apply congrArg (fun step => (columnEmbeddingList n k).foldl step none)
  funext acc e
  cases acc <;> rfl

/-- The finite search returns a positive-volume maximal embedding whenever
`k ≤ rank A`. Maximality includes maps with repeated columns, whose Gram volume
is zero. The proof uses existence only to certify nonemptiness and positivity,
never to define the returned selection. -/
theorem maximumVolumeColumnSearch_spec {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ Fin n, maximumVolumeColumnSearch A k = some e ∧
      0 < ((A.submatrix id e)ᵀ * A.submatrix id e).det ∧
      ∀ f : Fin k → Fin n, ((A.submatrix id f)ᵀ * A.submatrix id f).det ≤
        ((A.submatrix id e)ᵀ * A.submatrix id e).det := by
  classical
  obtain ⟨e₀, hpos₀⟩ := exists_column_embedding_gram_det_pos A k hk
  have hlist : columnEmbeddingList n k ≠ [] := List.ne_nil_of_mem (mem_columnEmbeddingList e₀)
  have hsome : maximumVolumeColumnSearch A k ≠ none := by
    intro h
    apply hlist
    exact List.argmax_eq_none.mp h
  cases hs : maximumVolumeColumnSearch A k with
  | none => exact (hsome hs).elim
  | some e =>
    have he : e ∈ (columnEmbeddingList n k).argmax
        (fun e : Fin k ↪ Fin n => ((A.submatrix id e)ᵀ * A.submatrix id e).det) := hs
    have hmax (g : Fin k ↪ Fin n) : ((A.submatrix id g)ᵀ * A.submatrix id g).det ≤
        ((A.submatrix id e)ᵀ * A.submatrix id e).det :=
      List.le_of_mem_argmax (f := fun e : Fin k ↪ Fin n =>
        ((A.submatrix id e)ᵀ * A.submatrix id e).det) (mem_columnEmbeddingList g) he
    have hpos := hpos₀.trans_le (hmax e₀)
    refine ⟨e, rfl, hpos, ?_⟩
    intro f
    by_cases hf : Function.Injective f
    · exact hmax ⟨f, hf⟩
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
      have hzero : ((A.submatrix id f)ᵀ * A.submatrix id f).det = 0 := by
        apply Matrix.det_zero_of_column_eq hne
        intro a
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
        rw [hij]
      rw [hzero]
      exact hpos.le

/-- Equal-volume ties are resolved by the first occurrence in the fixed
lexicographic embedding list.
atlas: interpolative-decomposition (partial) -/
theorem maximumVolumeColumnSearch_tie_first {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {e : Fin k ↪ Fin n} (he : maximumVolumeColumnSearch A k = some e) (g : Fin k ↪ Fin n)
    (hvol : ((A.submatrix id e)ᵀ * A.submatrix id e).det ≤
      ((A.submatrix id g)ᵀ * A.submatrix id g).det) :
    (columnEmbeddingList n k).idxOf e ≤ (columnEmbeddingList n k).idxOf g :=
  List.index_of_argmax he (mem_columnEmbeddingList g) hvol

/-- The complete exhaustive ID algorithm: select the first maximum-volume
embedding and compute `T = (Cᵀ C)⁻¹ Cᵀ A`. The output is optional so no arbitrary
fallback or rank oracle is needed outside the admissible range. -/
def interpolativeDecompositionSearch {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Option ((Fin k ↪ Fin n) × Matrix (Fin k) (Fin n) ℝ) :=
  (maximumVolumeColumnSearch A k).map (fun e => (e, columnInterpolationCoefficients A e))

/-- The actual returned finite-search ID has independent selected columns,
identity interpolation, coefficients bounded by one (hence by two), and the exact
sharp spectral residual guarantee. This includes cutoff zero and empty dimensions.
Source: HMT 2011, §4.2; Gu–Eisenstat 1996, Theorem 3.2.
atlas: interpolative-decomposition (partial) -/
theorem interpolativeDecompositionSearch_spec {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ Fin n, ∃ T : Matrix (Fin k) (Fin n) ℝ,
      interpolativeDecompositionSearch A k = some (e, T) ∧
      T = columnInterpolationCoefficients A e ∧
      IsUnit ((A.submatrix id e)ᵀ * A.submatrix id e) ∧
      LinearIndependent ℝ (A.submatrix id e).col ∧
      T.submatrix id e = 1 ∧ (∀ i j, |T i j| ≤ 1) ∧ (∀ i j, |T i j| ≤ 2) ∧
      specNorm (A - A.submatrix id e * T) ≤
        Real.sqrt (1 + (k : ℝ) * ((n : ℝ) - k)) * singularValues A k := by
  obtain ⟨e, he, hpos, hmax⟩ := maximumVolumeColumnSearch_spec A hk
  obtain ⟨hId, hEntry, hErr⟩ := columnInterpolationCoefficients_spec_of_maximum_volume A k hk e hpos hmax
  have hunit : IsUnit ((A.submatrix id e)ᵀ * A.submatrix id e) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hpos.ne')
  have hcols : LinearIndependent ℝ (A.submatrix id e).col := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols]
    exact ((Matrix.rank_transpose_mul_self _).symm.trans (Matrix.rank_of_isUnit _ hunit)).symm
  refine ⟨e, columnInterpolationCoefficients A e, ?_, rfl, hunit, hcols, hId, hEntry,
    (fun i j => (hEntry i j).trans (by norm_num)), ?_⟩
  · simp only [interpolativeDecompositionSearch, he, Option.map_some]
  · simpa only [Fintype.card_fin] using hErr

/-- At the input rank, the actual finite-search result reconstructs the matrix
exactly, including the empty rank-zero case. Source: HMT 2011, §4.2.
atlas: interpolative-decomposition (partial) -/
theorem interpolativeDecompositionSearch_exact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ e : Fin A.rank ↪ Fin n, ∃ T : Matrix (Fin A.rank) (Fin n) ℝ,
      interpolativeDecompositionSearch A A.rank = some (e, T) ∧
      T.submatrix id e = 1 ∧ (∀ i j, |T i j| ≤ 1) ∧ A = A.submatrix id e * T := by
  obtain ⟨e, T, hret, _, _, _, hId, hEntry, _, hErr⟩ := interpolativeDecompositionSearch_spec A le_rfl
  rw [singularValues_eq_zero_of_rank_le A le_rfl, mul_zero] at hErr
  have hz : specNorm (A - A.submatrix id e * T) = 0 := le_antisymm hErr (specNorm_nonneg _)
  have heq : A - A.submatrix id e * T = 0 := by
    open scoped Matrix.Norms.L2Operator in
    exact norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hz)
  exact ⟨e, T, hret, hId, hEntry, sub_eq_zero.mp heq⟩

end NLAlib
