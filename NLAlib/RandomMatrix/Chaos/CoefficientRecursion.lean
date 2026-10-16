import NLAlib.RandomMatrix.Chaos.Flattenings
import NLAlib.Matrix.Structured.RectangularCoefficientBlocks
import NLAlib.ForMathlib.Combinatorics.CoordinatePartitions

/-!
# Moving the last chaos index into a matrix coordinate

The row, column, and vectorization branches are lower-degree coefficient arrays.
Every parameter comparison is an entrywise reindexing of an original flattening.
Source: the finite bookkeeping lemma in the matrix-chaos derivation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical Matrix
namespace NLAlib

variable {τ ι m n 𝕜 : Type*} [Fintype τ] [DecidableEq τ]

/-- Append one scalar index to a tuple of old chaos indices. -/
def chaosAppendTuple (z : τ → ι) (j : ι) : τ ⊕ Unit → ι := Sum.elim z (fun _ => j)

/-- Freeze the last chaos index and move it into the matrix column. -/
def chaosRowCoefficients (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜)
    (z : τ → ι) : Matrix m (ι × n) 𝕜 :=
  fun a jb => A (chaosAppendTuple z jb.1) a jb.2

/-- Freeze the last chaos index and move it into the matrix row. -/
def chaosColumnCoefficients (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜)
    (z : τ → ι) : Matrix (ι × m) n 𝕜 :=
  fun ia b => A (chaosAppendTuple z ia.1) ia.2 b

/-- Freeze the last chaos index as a row and vectorize both original matrix
coordinates on the column side. -/
def chaosEntryCoefficients (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜)
    (z : τ → ι) : Matrix ι (m × n) 𝕜 :=
  fun j ab => A (chaosAppendTuple z j) ab.1 ab.2

variable [Fintype ι] [Fintype m] [Fintype n] [DecidableEq ι]
  [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- A horizontal-branch variance flattening is exactly an original flattening
with the last chaos mode on its column side. -/
theorem specNorm_chaosFlattening_rowCoefficients
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosFlattening (chaosRowCoefficients A) S) =
      specNorm (chaosFlattening A (S.disjSum ∅)) := by
  let e := (Equiv.finsetSumEmptyCoordinates (β := Unit) (ι := ι) S).prodCongr
    (Equiv.refl m)
  let f := ((Equiv.finsetSumEmptyComplementCoordinates (ι := ι) S).prodCongr
    (Equiv.refl n)).trans (Equiv.prodAssoc _ _ _)
  have he : (chaosFlattening A (S.disjSum ∅)).reindex e f =
      chaosFlattening (chaosRowCoefficients A) S := by
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosFlattening,
      chaosRowCoefficients]
    change A (chaosAssemble (S.disjSum ∅) (e.symm a).1 (f.symm b).1) a.2 b.2.2 =
      A (chaosAppendTuple (chaosAssemble S a.1 b.1) b.2.1) a.2 b.2.2
    congr 2
    funext t
    rcases t with t | u
    · by_cases ht : t ∈ S
      · simp [e, f, Equiv.finsetSumEmptyCoordinates, Equiv.finsetSumCoordinates,
          Equiv.finsetSumEmptyComplementCoordinates, chaosAssemble, chaosAppendTuple, ht]
      · simp [e, f, Equiv.finsetSumEmptyCoordinates, Equiv.finsetSumCoordinates,
          Equiv.finsetSumEmptyComplementCoordinates, chaosAssemble, chaosAppendTuple, ht]
    · cases u
      simp [e, f, Equiv.finsetSumEmptyCoordinates, Equiv.finsetSumCoordinates,
        Equiv.finsetSumEmptyComplementCoordinates, chaosAssemble, chaosAppendTuple]
  rw [← he, specNorm_reindex]

/-- Reordering a frozen coefficient label among the vectorized matrix labels. -/
private def rowCovarianceShuffle {x : Type*} :
    ((x × ι) × (m × n)) ≃ x × (m × (ι × n)) where
  toFun y := (y.1.1, (y.2.1, (y.1.2, y.2.2)))
  invFun y := ((y.1, y.2.2.1), (y.2.1, y.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def columnCovarianceShuffle {x : Type*} :
    ((x × ι) × (m × n)) ≃ x × ((ι × m) × n) where
  toFun y := (y.1.1, ((y.1.2, y.2.1), y.2.2))
  invFun y := ((y.1, y.2.1.1), (y.2.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A horizontal-branch covariance flattening keeps the last chaos mode on its
column side along with both original matrix coordinates. -/
theorem specNorm_chaosCovarianceFlattening_rowCoefficients
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosCovarianceFlattening (chaosRowCoefficients A) S) =
      specNorm (chaosCovarianceFlattening A (S.disjSum ∅)) := by
  let e := Equiv.finsetSumEmptyCoordinates (β := Unit) (ι := ι) S
  let f := ((Equiv.finsetSumEmptyComplementCoordinates (ι := ι) S).prodCongr
    (Equiv.refl (m × n))).trans rowCovarianceShuffle
  have he : (chaosCovarianceFlattening A (S.disjSum ∅)).reindex e f =
      chaosCovarianceFlattening (chaosRowCoefficients A) S := by
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosCovarianceFlattening,
      chaosRowCoefficients]
    change A (chaosAssemble (S.disjSum ∅) (e.symm a) (f.symm b).1) b.2.1 b.2.2.2 =
      A (chaosAppendTuple (chaosAssemble S a b.1) b.2.2.1) b.2.1 b.2.2.2
    congr 2
    funext t
    rcases t with t | u
    · by_cases ht : t ∈ S
      · simp [e, f, rowCovarianceShuffle, Equiv.finsetSumEmptyCoordinates,
          Equiv.finsetSumCoordinates, Equiv.finsetSumEmptyComplementCoordinates,
          chaosAssemble, chaosAppendTuple, ht]
      · simp [e, f, rowCovarianceShuffle, Equiv.finsetSumEmptyCoordinates,
          Equiv.finsetSumCoordinates, Equiv.finsetSumEmptyComplementCoordinates,
          chaosAssemble, chaosAppendTuple, ht]
    · cases u
      simp [e, f, rowCovarianceShuffle, Equiv.finsetSumEmptyCoordinates,
        Equiv.finsetSumCoordinates, Equiv.finsetSumEmptyComplementCoordinates,
        chaosAssemble, chaosAppendTuple]
  rw [← he, specNorm_reindex]

/-- A vertical-branch covariance flattening also keeps the frozen last mode on
its column side, together with the new matrix row and column. -/
theorem specNorm_chaosCovarianceFlattening_columnCoefficients
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosCovarianceFlattening (chaosColumnCoefficients A) S) =
      specNorm (chaosCovarianceFlattening A (S.disjSum ∅)) := by
  let e := Equiv.finsetSumEmptyCoordinates (β := Unit) (ι := ι) S
  let f := ((Equiv.finsetSumEmptyComplementCoordinates (ι := ι) S).prodCongr
    (Equiv.refl (m × n))).trans columnCovarianceShuffle
  have he : (chaosCovarianceFlattening A (S.disjSum ∅)).reindex e f =
      chaosCovarianceFlattening (chaosColumnCoefficients A) S := by
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosCovarianceFlattening,
      chaosColumnCoefficients]
    change A (chaosAssemble (S.disjSum ∅) (e.symm a) (f.symm b).1) b.2.1.2 b.2.2 =
      A (chaosAppendTuple (chaosAssemble S a b.1) b.2.1.1) b.2.1.2 b.2.2
    congr 2
    funext t
    rcases t with t | u
    · by_cases ht : t ∈ S
      · simp [e, f, columnCovarianceShuffle, Equiv.finsetSumEmptyCoordinates,
          Equiv.finsetSumCoordinates, Equiv.finsetSumEmptyComplementCoordinates,
          chaosAssemble, chaosAppendTuple, ht]
      · simp [e, f, columnCovarianceShuffle, Equiv.finsetSumEmptyCoordinates,
          Equiv.finsetSumCoordinates, Equiv.finsetSumEmptyComplementCoordinates,
          chaosAssemble, chaosAppendTuple, ht]
    · cases u
      simp [e, f, columnCovarianceShuffle, Equiv.finsetSumEmptyCoordinates,
        Equiv.finsetSumCoordinates, Equiv.finsetSumEmptyComplementCoordinates,
        chaosAssemble, chaosAppendTuple]
  rw [← he, specNorm_reindex]

/-- A vertical-branch variance flattening is an original flattening with the
last chaos mode on its row side. -/
theorem specNorm_chaosFlattening_columnCoefficients
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosFlattening (chaosColumnCoefficients A) S) =
      specNorm (chaosFlattening A (S.disjSum Finset.univ)) := by
  let e := ((Equiv.finsetSumOneCoordinates (ι := ι) S).prodCongr
    (Equiv.refl m)).trans (Equiv.prodAssoc _ _ _)
  let f := (Equiv.finsetSumOneComplementCoordinates (ι := ι) S).prodCongr
    (Equiv.refl n)
  have he : (chaosFlattening A (S.disjSum Finset.univ)).reindex e f =
      chaosFlattening (chaosColumnCoefficients A) S := by
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosFlattening,
      chaosColumnCoefficients]
    change A (chaosAssemble (S.disjSum Finset.univ) (e.symm a).1 (f.symm b).1)
      a.2.2 b.2 = A (chaosAppendTuple (chaosAssemble S a.1 b.1) a.2.1) a.2.2 b.2
    congr 2
    funext t
    rcases t with t | u
    · by_cases ht : t ∈ S
      · simp [e, f, Equiv.finsetSumOneCoordinates, Equiv.finsetSumCoordinates,
          Equiv.finsetSumOneComplementCoordinates, chaosAssemble, chaosAppendTuple, ht]
      · simp [e, f, Equiv.finsetSumOneCoordinates, Equiv.finsetSumCoordinates,
          Equiv.finsetSumOneComplementCoordinates, chaosAssemble, chaosAppendTuple, ht]
    · cases u
      simp [e, f, Equiv.finsetSumOneCoordinates, Equiv.finsetSumCoordinates,
        Equiv.finsetSumOneComplementCoordinates, chaosAssemble, chaosAppendTuple]
  rw [← he, specNorm_reindex]

/-- Every variance flattening of the vectorization branch is an original
covariance flattening with a nonempty row subset containing the last mode. -/
theorem specNorm_chaosFlattening_entryCoefficients
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosFlattening (chaosEntryCoefficients A) S) =
      specNorm (chaosCovarianceFlattening A (S.disjSum Finset.univ)) := by
  let e := Equiv.finsetSumOneCoordinates (ι := ι) S
  let f := (Equiv.finsetSumOneComplementCoordinates (ι := ι) S).prodCongr
    (Equiv.refl (m × n))
  have he : (chaosCovarianceFlattening A (S.disjSum Finset.univ)).reindex e f =
      chaosFlattening (chaosEntryCoefficients A) S := by
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosFlattening,
      chaosCovarianceFlattening, chaosEntryCoefficients]
    congr 2
    funext t
    rcases t with t | u
    · by_cases ht : t ∈ S
      · simp [e, f, Equiv.finsetSumOneCoordinates, Equiv.finsetSumCoordinates,
          Equiv.finsetSumOneComplementCoordinates, chaosAssemble, chaosAppendTuple, ht]
      · simp [e, f, Equiv.finsetSumOneCoordinates, Equiv.finsetSumCoordinates,
          Equiv.finsetSumOneComplementCoordinates, chaosAssemble, chaosAppendTuple, ht]
    · cases u
      simp [e, f, Equiv.finsetSumOneCoordinates, Equiv.finsetSumCoordinates,
        Equiv.finsetSumOneComplementCoordinates, chaosAssemble, chaosAppendTuple]
  rw [← he, specNorm_reindex]

/-- Moving the last mode into a column cannot increase the variance parameter. -/
theorem chaosSigma_rowCoefficients_le (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) :
    chaosSigma (chaosRowCoefficients A) ≤ chaosSigma A := by
  apply chaosSigma_le
  intro S
  rw [specNorm_chaosFlattening_rowCoefficients]
  exact specNorm_chaosFlattening_le _ _

/-- Moving the last mode into a row cannot increase the variance parameter. -/
theorem chaosSigma_columnCoefficients_le (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) :
    chaosSigma (chaosColumnCoefficients A) ≤ chaosSigma A := by
  apply chaosSigma_le
  intro S
  rw [specNorm_chaosFlattening_columnCoefficients]
  exact specNorm_chaosFlattening_le _ _

/-- Moving the last mode into a row while vectorizing the original matrix turns
every variance flattening into a nonempty-row covariance flattening. -/
theorem chaosSigma_entryCoefficients_le (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) :
    chaosSigma (chaosEntryCoefficients A) ≤ chaosCovariance A := by
  apply chaosSigma_le
  intro S
  rw [specNorm_chaosFlattening_entryCoefficients]
  apply specNorm_chaosCovarianceFlattening_le
  exact ⟨Sum.inr (), by simp⟩

/-- The covariance parameter does not increase in the horizontal branch. -/
theorem chaosCovariance_rowCoefficients_le
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) :
    chaosCovariance (chaosRowCoefficients A) ≤ chaosCovariance A := by
  apply chaosCovariance_le _ (chaosCovariance_nonneg _)
  intro S hS
  rw [specNorm_chaosCovarianceFlattening_rowCoefficients]
  apply specNorm_chaosCovarianceFlattening_le
  obtain ⟨t, ht⟩ := hS
  exact ⟨Sum.inl t, by simpa using ht⟩

/-- The covariance parameter does not increase in the vertical branch. -/
theorem chaosCovariance_columnCoefficients_le
    (A : ((τ ⊕ Unit) → ι) → Matrix m n 𝕜) :
    chaosCovariance (chaosColumnCoefficients A) ≤ chaosCovariance A := by
  apply chaosCovariance_le _ (chaosCovariance_nonneg _)
  intro S hS
  rw [specNorm_chaosCovarianceFlattening_columnCoefficients]
  apply specNorm_chaosCovarianceFlattening_le
  obtain ⟨t, ht⟩ := hS
  exact ⟨Sum.inl t, by simpa using ht⟩

end NLAlib
