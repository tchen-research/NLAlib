/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.FiniteLaw.Uniform
import NLAlib.Sketching.Sparse.IIDComparison.ConditionalBarycenter
import Mathlib.Data.Set.PowersetCard
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic


/-!
# Uniform signed exact-s columns (OSNAP)

`uniformSparseMatrix X` has columns with exactly `s` nonzeros `± 1/√s` on a uniformly random
support (`UniformSparseSupport`, `UniformSparseColumn`, `UniformSparseSample`,
`uniformSparseColumnLaw`, `uniformSparseSampleLaw`). An outcome consists of a uniformly chosen support of cardinality `s` and a
uniform sign at every row.  Signs outside the support are harmless redundant
coordinates; every signed support vector therefore has the same number of
representatives and the induced column law is exactly uniform.
-/

open scoped InnerProductSpace

namespace NLAlib.SparseSketch.UniformSparse

noncomputable section

/-- Supports of cardinality exactly `s` in `Fin m`.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev _root_.NLAlib.UniformSparseSupport (m s : ℕ) := Set.powersetCard (Fin m) s

/-- A literal signed exact-`s` column.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev _root_.NLAlib.UniformSparseColumn (m s : ℕ) := UniformSparseSupport m s × (Fin m → Sign)

/-- Independent exact-`s` columns.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev _root_.NLAlib.UniformSparseSample (m s n : ℕ) := Fin n → UniformSparseColumn m s

/-- A canonical exact support, used only to witness nonemptiness.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def canonicalSupport {m s : ℕ} (hsm : s ≤ m) : UniformSparseSupport m s :=
  Set.powersetCard.ofFinEmb s (Fin m) (Fin.castLEEmb hsm)

/-- A support subset of the requested cardinality exists whenever sparsity does not exceed row count.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactSupportNonempty {m s : ℕ} (hsm : s ≤ m) :
    Nonempty (UniformSparseSupport m s) := ⟨canonicalSupport hsm⟩

/-- An exactly-s signed column exists whenever sparsity does not exceed row count.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exactColumnNonempty {m s : ℕ} (hsm : s ≤ m) :
    Nonempty (UniformSparseColumn m s) :=
  ⟨(canonicalSupport hsm, fun _ => .plus)⟩

/-- Uniform support and independent uniform signs.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def _root_.NLAlib.uniformSparseColumnLaw {m s : ℕ} (hsm : s ≤ m) : FiniteLaw
    (UniformSparseColumn m s) := by
  let : Nonempty (UniformSparseColumn m s) := exactColumnNonempty hsm
  exact FiniteLaw.uniform

/-- The actual independent-column law.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def _root_.NLAlib.uniformSparseSampleLaw {m s n : ℕ} (hsm : s ≤ m) :
    FiniteLaw (UniformSparseSample m s n) :=
  FiniteLaw.independentProduct (fun _ => uniformSparseColumnLaw hsm)

/-- Unnormalized entry of a signed sparse column.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def _root_.NLAlib.UniformSparseColumn.value {m s : ℕ} (x : UniformSparseColumn m s) (r : Fin m) :
    ℝ :=
  by
    classical
    exact if r ∈ x.1 then (x.2 r).val else 0

/-- A selected column coordinate equals its recorded sign value.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem columnValue_of_mem {m s : ℕ} (x : UniformSparseColumn m s)
    {r : Fin m} (hr : r ∈ x.1) : UniformSparseColumn.value x r = (x.2 r).val := by
  simp [UniformSparseColumn.value, hr]

/-- An unselected column coordinate is zero.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem columnValue_of_notMem {m s : ℕ} (x : UniformSparseColumn m s)
    {r : Fin m} (hr : r ∉ x.1) : UniformSparseColumn.value x r = 0 := by
  simp [UniformSparseColumn.value, hr]

/-- A signed column coordinate is nonzero precisely on its selected support.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem columnValue_ne_zero_iff {m s : ℕ} (x : UniformSparseColumn m s) (r : Fin m) :
    UniformSparseColumn.value x r ≠ 0 ↔ r ∈ x.1 := by
  by_cases hr : r ∈ x.1
  · simp [UniformSparseColumn.value, hr, Sign.val_ne_zero]
  · simp [UniformSparseColumn.value, hr]

/-- Real indicator of membership in the exact support.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def supportIndicator {m s : ℕ} (x : UniformSparseColumn m s) (r : Fin m) : ℝ := by
  classical
  exact if r ∈ x.1 then 1 else 0

/-- A signed column coordinate square is the indicator of selected support.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem columnValue_sq {m s : ℕ} (x : UniformSparseColumn m s) (r : Fin m) :
    UniformSparseColumn.value x r ^ 2 = supportIndicator x r := by
  classical
  by_cases hr : r ∈ x.1
  · simp [UniformSparseColumn.value, supportIndicator, hr, Sign.val_sq]
  · simp [UniformSparseColumn.value, supportIndicator, hr]

/-- An exactly-s signed column has squared coordinate energy equal to sparsity.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_columnValue_sq {m s : ℕ} (x : UniformSparseColumn m s) :
    ∑ r, UniformSparseColumn.value x r ^ 2 = (s : ℝ) := by
  classical
  simp_rw [columnValue_sq]
  have hfilter :
      (Finset.univ.filter fun r : Fin m => r ∈ (x.1 : Finset (Fin m))) =
        (x.1 : Finset (Fin m)) := by
    ext r
    simp
  calc
    (∑ r : Fin m, supportIndicator x r) =
        ((Finset.univ.filter fun r : Fin m =>
          r ∈ (x.1 : Finset (Fin m))).card : ℝ) := by
      simp [supportIndicator, Set.powersetCard.mem_coe_iff]
    _ = ((x.1 : Finset (Fin m)).card : ℝ) := by rw [hfilter]
    _ = (s : ℝ) := by rw [(x.1).prop]

/-- The normalized `m × n` exact-s sketch.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def _root_.NLAlib.uniformSparseMatrix {m s n : ℕ} (X : UniformSparseSample m s n) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun r i => invSqrt s * UniformSparseColumn.value (X i) r

/-- At positive sparsity, a normalized sketch entry is nonzero precisely on selected support.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem _root_.NLAlib.uniformSparseMatrix_ne_zero_iff {m s n : ℕ} (X : UniformSparseSample m s n)
    (hs : 0 < s) (r : Fin m) (i : Fin n) :
    uniformSparseMatrix X r i ≠ 0 ↔ r ∈ (X i).1 := by
  rw [uniformSparseMatrix, mul_ne_zero_iff, and_iff_right (invSqrt_ne_zero hs)]
  exact columnValue_ne_zero_iff (X i) r

/-- The exact nonzero support of a matrix column.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def matrixColumnSupportEquiv {m s n : ℕ} (X : UniformSparseSample m s n)
    (hs : 0 < s) (i : Fin n) :
    {r : Fin m // uniformSparseMatrix X r i ≠ 0} ≃ {r : Fin m // r ∈ (X i).1} where
  toFun r := ⟨r, (uniformSparseMatrix_ne_zero_iff X hs r i).mp r.2⟩
  invFun r := ⟨r, (uniformSparseMatrix_ne_zero_iff X hs r i).mpr r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each actual normalized sketch column has exactly the requested number of nonzero entries.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem _root_.NLAlib.card_filter_uniformSparseMatrix_ne_zero {m s n : ℕ}
    (X : UniformSparseSample m s n)
    (hs : 0 < s) (i : Fin n) :
    Fintype.card {r : Fin m // uniformSparseMatrix X r i ≠ 0} = s := by
  classical
  rw [Fintype.card_congr (matrixColumnSupportEquiv X hs i)]
  rw [Fintype.card_eq_nat_card]
  change Nat.card (↥(SetLike.coe (X i).1 : Set (Fin m))) = s
  rw [Nat.card_coe_set_eq]
  exact Set.powersetCard.ncard_eq (X i).1

/-- The exact-s sketch Gram entry is its reciprocal-sparsity weighted signed-support inner product.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sketchGram_apply {m s n : ℕ} (X : UniformSparseSample m s n)
    (hs : 0 < s) (i j : Fin n) :
    sketchGram (uniformSparseMatrix X) i j =
      (1 / (s : ℝ)) * ∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j)
          r := by
  rw [sketchGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, uniformSparseMatrix]
  calc
    (∑ r, invSqrt s * UniformSparseColumn.value (X i) r *
        (invSqrt s * UniformSparseColumn.value (X j) r)) =
        invSqrt s ^ 2 *
          ∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = (1 / (s : ℝ)) *
          ∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r := by
      rw [invSqrt_sq hs]

/-- Every exact-s sketch column has unit diagonal Gram entry at positive sparsity.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem sketchGram_diag {m s n : ℕ} (X : UniformSparseSample m s n)
    (hs : 0 < s) (i : Fin n) : sketchGram (uniformSparseMatrix X) i i = 1 := by
  rw [UniformSparse.sketchGram_apply X hs]
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  rw [show (∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X i) r) = (s : ℝ) by
    simpa [pow_two] using sum_columnValue_sq (X i)]
  field_simp

/-- The hollow expansion.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def hollowGram {m s n d : ℕ} (F : Frame n d) (X : UniformSparseSample m s n) :
    Matrix (Fin d) (Fin d) ℝ := fun a c =>
  (1 / (s : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    (∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) *
      F.u i a * F.u j c

/-- The embedded exact-s Gram entry is the literal frame-weighted sketch Gram sum.
Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem embeddedGram_apply {m s n d : ℕ} (F : Frame n d)
    (X : UniformSparseSample m s n) (hs : 0 < s) (a c : Fin d) :
    embeddedGram F (uniformSparseMatrix X) a c =
      (1 / (s : ℝ)) * ∑ i, ∑ j,
        (∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) *
          F.u i a * F.u j c := by
  simp only [embeddedGram, Matrix.mul_apply, Matrix.transpose_apply, rowMatrix]
  simp_rw [UniformSparse.sketchGram_apply X hs]
  calc
    (∑ i, F.u i a * ∑ j,
        ((1 / (s : ℝ)) *
          ∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) * F.u j c) =
        ∑ i, ∑ j, (1 / (s : ℝ)) *
          ((∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) *
            F.u i a * F.u j c) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (1 / (s : ℝ)) * ∑ i, ∑ j,
        (∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) *
          F.u i a * F.u j c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

/-- Exact pointwise hollowness; no independence premise is used.

Source: ported from `SparseFockFormal.UniformExactSModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_eq_hollow {m s n d : ℕ} (F : Frame n d)
    (X : UniformSparseSample m s n) (hs : 0 < s) :
    gramError F (uniformSparseMatrix X) = UniformSparse.hollowGram F X := by
  classical
  ext a c
  rw [gramError, Matrix.sub_apply, embeddedGram_apply F X hs]
  have hparseval := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℝ => M a c) F.parseval
  have hparseval' : (∑ i, F.u i a * F.u i c) =
      (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hparseval
  let T : Fin n → Fin n → ℝ := fun i j =>
    (∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) *
      F.u i a * F.u j c
  have hsplit (i : Fin n) :
      (∑ j, T i j) = T i i + ∑ j ∈ Finset.univ.erase i, T i j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  have hdiag : (1 / (s : ℝ)) * ∑ i, T i i =
      (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
    have hTi (i : Fin n) : T i i = (s : ℝ) * F.u i a * F.u i c := by
      dsimp [T]
      rw [show (∑ r, UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X i) r) =
          (s : ℝ) by
        simpa [pow_two] using sum_columnValue_sq (X i)]
    simp_rw [hTi, mul_assoc]
    rw [← Finset.mul_sum]
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    rw [show (1 / (s : ℝ)) * ((s : ℝ) * ∑ i, F.u i a * F.u i c) =
        ∑ i, F.u i a * F.u i c by field_simp]
    exact hparseval'
  simp only [UniformSparse.hollowGram]
  change (1 / (s : ℝ)) * (∑ i, ∑ j, T i j) -
      (1 : Matrix (Fin d) (Fin d) ℝ) a c =
    (1 / (s : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, T i j
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, mul_add, hdiag]
  ring

end

end NLAlib.SparseSketch.UniformSparse
