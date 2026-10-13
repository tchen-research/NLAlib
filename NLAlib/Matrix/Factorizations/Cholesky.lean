import NLAlib.Matrix.Factorizations.LU
import NLAlib.ForMathlib.LinearAlgebra.Matrix.TriangularRank
/-!
# Cholesky factorization and the Cholesky recursion

* `IsCholesky A L`: `A = L Lᵀ` with `L` lower triangular with positive diagonal (any linearly
  ordered index); `IsCholesky.posDef`, `IsCholesky.unique` (the determinant formula is
  `det_eq_prod_sq_diag_of_cholesky` in `CholeskyDefinite`).
* The recursion `cholesky A` on the leading pivot (`a ↦ √a`, `c ↦ c/√a`, continue on
  `pivotSchur A`), the success predicate `CholeskySucceeds A` (every pivot positive), the
  realisation `isCholesky_cholesky` (symmetric `A`) and the breakdown theorem
  `choleskySucceeds_iff_posDef`: Cholesky is the test for positive definiteness.
  Existence on any linearly ordered finite index: `exists_isCholesky_iff_posDef`.
* Semidefinite matrices: the same recursion gives `A = L Lᵀ` with nonnegative diagonal
  (`eq_cholesky_mul_transpose_of_posSemidef`), since a zero pivot of a PSD matrix has a zero
  column and `0⁻¹ · 0 = 0`; `exists_eq_mul_transpose_of_posSemidef` on any linearly ordered
  finite index.
* Pivoted (diagonal pivoting) Cholesky for PSD matrices: `choleskyPivoted`, `IsPivotedCholesky`
  (`PAPᵀ = LLᵀ`), never fails (`isPivotedCholesky_choleskyPivoted`), and stops at the rank
  (`choleskyPivoted_apply_self_pos_iff_lt_rank`, `choleskyPivoted_apply_eq_zero_of_rank_le`).

Sources: Trefethen–Bau 1997, Lect. 23 (Thm 23.1, Alg. 23.1); Golub–Van Loan 2013, §4.2.5–4.2.9;
Higham 2002, Thm 10.1 and §10.3; Horn–Johnson 2013, Cor. 7.2.9.
Atlas: `cholesky-decomposition`, `cholesky-algorithm`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-! ### The factorization predicate -/

section Predicate

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Cholesky factorization**: `A = L Lᵀ` with `L` lower triangular with positive diagonal.
Trefethen–Bau 1997, Lect. 23; Golub–Van Loan 2013, Thm 4.2.7; Higham 2002, Thm 10.1.
atlas: cholesky-decomposition (partial) -/
structure IsCholesky (A L : Matrix n n ℝ) : Prop where
  /-- `L` is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- `L` has positive diagonal. -/
  apply_self_pos : ∀ i, 0 < L i i
  /-- `A = L Lᵀ`. -/
  eq_mul_transpose : A = L * Lᵀ

/-- A Cholesky factor is invertible. -/
theorem IsCholesky.isUnit_det {A L : Matrix n n ℝ} (h : IsCholesky A L) : IsUnit L.det :=
  (isUnit_det_iff_of_isLowerTriangular h.isLowerTriangular).2 fun i => (h.apply_self_pos i).ne'

/-- A matrix with a Cholesky factorization is positive definite (`L` invertible, so
`xᵀ A x = ‖Lᵀ x‖² > 0` for `x ≠ 0`). Trefethen–Bau 1997, Thm 23.1 (converse direction).
atlas: cholesky-decomposition (partial) -/
theorem IsCholesky.posDef {A L : Matrix n n ℝ} (h : IsCholesky A L) : A.PosDef := by
  have hL : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).2 h.isUnit_det
  have := PosDef.mul_conjTranspose_self L (vecMul_injective_iff_isUnit.2 hL)
  rwa [conjTranspose_eq_transpose_of_trivial, ← h.eq_mul_transpose] at this

/-- **Uniqueness of the Cholesky factor**. Proof: `D = L'⁻¹ L = L'ᵀ L⁻ᵀ` is lower and upper
triangular, hence diagonal with positive diagonal, and `D Dᵀ = 1`, so `D = 1`.
Trefethen–Bau 1997, Thm 23.1; Golub–Van Loan 2013, Thm 4.2.7; Higham 2002, Thm 10.1.
atlas: cholesky-decomposition (partial) -/
theorem IsCholesky.unique {A L L' : Matrix n n ℝ} (h : IsCholesky A L) (h' : IsCholesky A L') :
    L = L' := by
  have hL := h.isUnit_det
  have hL' := h'.isUnit_det
  have hLt : IsUnit Lᵀ.det := by rwa [det_transpose]
  have hLL : L * Lᵀ = L' * L'ᵀ := h.eq_mul_transpose.symm.trans h'.eq_mul_transpose
  set D := L'⁻¹ * L with hD
  have hDlow : D.IsLowerTriangular :=
    BlockTriangular.mul (isLowerTriangular_inv h'.isLowerTriangular) h.isLowerTriangular
  have hD2 : D = L'ᵀ * (Lᵀ)⁻¹ := by
    calc D = L'⁻¹ * L * (Lᵀ * (Lᵀ)⁻¹) := by rw [mul_nonsing_inv _ hLt, Matrix.mul_one]
      _ = L'⁻¹ * (L * Lᵀ) * (Lᵀ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L'⁻¹ * (L' * L'ᵀ) * (Lᵀ)⁻¹ := by rw [hLL]
      _ = L'ᵀ * (Lᵀ)⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hL', Matrix.one_mul]
  have hDup : D.IsUpperTriangular := by
    rw [hD2]
    exact BlockTriangular.mul (isUpperTriangular_transpose_iff.2 h'.isLowerTriangular)
      (isUpperTriangular_inv (isUpperTriangular_transpose_iff.2 h.isLowerTriangular))
  have hdiag : ∀ i, D i i = (L' i i)⁻¹ * L i i := fun i => by
    rw [hD, mul_apply_self_of_isLowerTriangular (isLowerTriangular_inv h'.isLowerTriangular)
      h.isLowerTriangular, inv_apply_self_of_isLowerTriangular h'.isLowerTriangular
      (fun j => (h'.apply_self_pos j).ne')]
  have hpos : ∀ i, 0 < D i i := fun i => by
    rw [hdiag]; exact mul_pos (inv_pos.2 (h'.apply_self_pos i)) (h.apply_self_pos i)
  have hL't : IsUnit L'ᵀ.det := by rwa [det_transpose]
  have hDD : D * Dᵀ = 1 := by
    calc D * Dᵀ = L'⁻¹ * (L * Lᵀ) * (L'⁻¹)ᵀ := by
          rw [hD, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = L'⁻¹ * (L' * L'ᵀ) * (L'ᵀ)⁻¹ := by rw [hLL, transpose_nonsing_inv]
      _ = 1 := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hL', Matrix.one_mul, mul_nonsing_inv _ hL't]
  have hone : ∀ i, D i i = 1 := fun i => by
    have h1 := congrFun (congrFun hDD i) i
    rw [mul_apply_self_of_isLowerTriangular hDlow (isLowerTriangular_transpose_iff.2 hDup),
      transpose_apply, one_apply_eq] at h1
    have hp := hpos i
    nlinarith
  have hD1 : D = 1 := by
    rw [eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hDlow hDup]
    simp [hone]
  calc L = L' * (L'⁻¹ * L) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hL', Matrix.one_mul]
    _ = L' := by rw [← hD, hD1, Matrix.mul_one]

end Predicate

/-! ### The Cholesky recursion -/

section Algorithm

/-- **The Cholesky recursion** on the leading pivot: for `A = [[a, cᵀ], [c, C]]`,
`L = [[√a, 0], [c/√a, L']]` with `L' = cholesky (C − c cᵀ/a)` (`pivotSchur`; for a symmetric
`A` the first row and column agree). Total: a nonpositive pivot gives `√a = 0` and junk, never
an error. Trefethen–Bau 1997, Alg. 23.1; Golub–Van Loan 2013, §4.2.5 (outer-product form).
atlas: cholesky-algorithm -/
def cholesky : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
  | 0, A => A
  | _ + 1, A =>
    borderedMatrix (Real.sqrt (A 0 0)) 0 ((Real.sqrt (A 0 0))⁻¹ • fun i => A i.succ 0)
      (cholesky (pivotSchur A))

/-- **Success of the Cholesky recursion**: every pivot (the `(1,1)` entry of `A` and of each
successive Schur complement) is positive. Trefethen–Bau 1997, Lect. 23;
Golub–Van Loan 2013, §4.2.5.
atlas: cholesky-algorithm -/
def CholeskySucceeds : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → Prop
  | 0, _ => True
  | _ + 1, A => 0 < A 0 0 ∧ CholeskySucceeds (pivotSchur A)

/-- The Cholesky recursion always returns a lower triangular matrix. -/
theorem isLowerTriangular_cholesky {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (cholesky A).IsLowerTriangular := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih => exact isLowerTriangular_borderedMatrix_iff.2 ⟨rfl, ih _⟩

/-- The diagonal of the Cholesky recursion is nonnegative (square roots). -/
theorem cholesky_apply_self_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    0 ≤ cholesky A i i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [cholesky]
    · simpa [cholesky] using ih _ i

/-- The pivots are the squares of the diagonal: the recursion succeeds iff the diagonal of
`cholesky A` is positive. -/
theorem choleskySucceeds_iff_forall_cholesky_apply_self_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : CholeskySucceeds A ↔ ∀ i, 0 < cholesky A i i := by
  induction n with
  | zero => simp [CholeskySucceeds]
  | succ n ih =>
    rw [CholeskySucceeds, ih, Fin.forall_fin_succ]
    simp [cholesky, Real.sqrt_pos]

/-- **One step of the Cholesky recursion**: for symmetric `A` with nonnegative pivot whose
column vanishes when the pivot does, if the Schur complement is reproduced by its Cholesky
recursion then so is `A`. Trefethen–Bau 1997, Lect. 23, eq. (23.2); Golub–Van Loan 2013,
§4.2.5. -/
theorem eq_cholesky_mul_transpose_of_pivotSchur {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) (ha : 0 ≤ A 0 0)
    (hc : A 0 0 = 0 → ∀ i : Fin n, A i.succ 0 = 0)
    (hS : pivotSchur A = cholesky (pivotSchur A) * (cholesky (pivotSchur A))ᵀ) :
    A = cholesky A * (cholesky A)ᵀ := by
  have hsym : ∀ j : Fin n, A 0 j.succ = A j.succ 0 := fun j => by
    simpa using hA.apply j.succ 0
  have hsq : Real.sqrt (A 0 0) * Real.sqrt (A 0 0) = A 0 0 := Real.mul_self_sqrt ha
  have hcol : ∀ i : Fin n,
      Real.sqrt (A 0 0) * ((Real.sqrt (A 0 0))⁻¹ * A i.succ 0) = A i.succ 0 := by
    intro i
    rcases ha.lt_or_eq with hpos | hzero
    · rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', one_mul]
    · rw [hc hzero.symm i, mul_zero, mul_zero]
  have hinv : (Real.sqrt (A 0 0))⁻¹ * (Real.sqrt (A 0 0))⁻¹ = (A 0 0)⁻¹ := by
    rw [← mul_inv, hsq]
  simp only [cholesky]
  rw [transpose_borderedMatrix, borderedMatrix_mul_borderedMatrix, ← hS]
  conv_lhs => rw [← borderedMatrix_eta A]
  congr 1
  · simp [hsq]
  · ext j; simp [hcol, hsym]
  · ext i; simp [hcol]
  · ext i j
    simp only [pivotSchur_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, submatrix_apply,
      Matrix.add_apply]
    rw [hsym j]
    linear_combination (A i.succ 0 * A j.succ 0) * hinv.symm

/-- **Realisation of the Cholesky recursion**: for symmetric `A` with all pivots positive,
`cholesky A` is the Cholesky factor. Proof: induction on `n` with
`eq_cholesky_mul_transpose_of_pivotSchur`; the Schur complement stays symmetric
(`isHermitian_pivotSchur`). Trefethen–Bau 1997, Alg. 23.1; Golub–Van Loan 2013, §4.2.5.
atlas: cholesky-algorithm -/
theorem isCholesky_cholesky {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (h : CholeskySucceeds A) : IsCholesky A (cholesky A) := by
  refine ⟨isLowerTriangular_cholesky A,
    (choleskySucceeds_iff_forall_cholesky_apply_self_pos A).1 h, ?_⟩
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    obtain ⟨ha, hS⟩ := h
    exact eq_cholesky_mul_transpose_of_pivotSchur hA ha.le (fun h0 => absurd h0 ha.ne')
      (ih (isHermitian_pivotSchur hA) hS)

/-- **Breakdown of the Cholesky recursion**: for symmetric `A`, the recursion succeeds iff `A`
is positive definite (Cholesky is the test for positive definiteness). Proof: induction on `n`
with `posDef_iff_pivotSchur`. Trefethen–Bau 1997, Thm 23.1; Golub–Van Loan 2013, §4.2.5;
Horn–Johnson 2013, Cor. 7.2.9.
atlas: cholesky-algorithm -/
theorem choleskySucceeds_iff_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    CholeskySucceeds A ↔ A.PosDef := by
  induction n with
  | zero =>
    simp only [CholeskySucceeds, true_iff]
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
    ext i; exact i.elim0
  | succ n ih =>
    rw [CholeskySucceeds, ih (isHermitian_pivotSchur hA), posDef_iff_pivotSchur hA]

/-- **Realisation on `Fin n`**: a positive definite matrix on `Fin n` has the Cholesky factor
`cholesky A`. Trefethen–Bau 1997, Thm 23.1; Golub–Van Loan 2013, Thm 4.2.7. -/
theorem isCholesky_cholesky_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    IsCholesky A (cholesky A) :=
  isCholesky_cholesky hA.isHermitian ((choleskySucceeds_iff_posDef hA.isHermitian).2 hA)

/-- **Semidefinite Cholesky**: for positive semidefinite `A` the (unpivoted) recursion gives
`A = L Lᵀ` with `L = cholesky A` lower triangular with nonnegative diagonal
(`isLowerTriangular_cholesky`, `cholesky_apply_self_nonneg`); not unique in general. A zero
pivot has a zero column, so `0⁻¹ · 0 = 0` is the right multiplier. Proof: induction with
`eq_cholesky_mul_transpose_of_pivotSchur` and `posSemidef_pivotSchur`.
Golub–Van Loan 2013, §4.2.8; Higham 2002, Thm 10.9 (the pivoted form; here the pivots are
taken in order).
atlas: cholesky-decomposition (partial) -/
theorem eq_cholesky_mul_transpose_of_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : A = cholesky A * (cholesky A)ᵀ := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    exact eq_cholesky_mul_transpose_of_pivotSchur hA.isHermitian (hA.diag_nonneg)
      (fun h0 i => apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA h0 i.succ)
      (ih (posSemidef_pivotSchur hA))

end Algorithm

/-! ### Existence over any linearly ordered index -/

section Existence

variable {m n : Type*} [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]

/-- A lower-triangular factorization `A = L Lᵀ` transports along an order isomorphism of the
index type (with any predicate `P` on the diagonal). -/
theorem exists_eq_mul_transpose_submatrix {A L : Matrix n n ℝ} (P : ℝ → Prop)
    (hL : L.IsLowerTriangular) (hP : ∀ i, P (L i i)) (hA : A = L * Lᵀ) (e : m ≃o n) :
    ∃ L' : Matrix m m ℝ, L'.IsLowerTriangular ∧ (∀ i, P (L' i i)) ∧
      A.submatrix e e = L' * L'ᵀ :=
  ⟨L.submatrix e e, isLowerTriangular_iff.2 fun _ _ hij =>
      isLowerTriangular_iff.1 hL _ _ (e.strictMono hij),
    fun i => hP (e i), by
      rw [hA, Matrix.transpose_submatrix]
      exact (Matrix.submatrix_mul_equiv L Lᵀ e e.toEquiv e).symm⟩

/-- The sorting isomorphism `Fin (card n) ≃o n` and its inverse undo each other on matrices. -/
theorem submatrix_monoEquivOfFin_symm (A : Matrix n n ℝ) :
    (A.submatrix (monoEquivOfFin n rfl) (monoEquivOfFin n rfl)).submatrix
      (monoEquivOfFin n rfl).symm (monoEquivOfFin n rfl).symm = A := by
  ext i j; simp

/-- **Existence of the Cholesky factorization**: a real matrix on a linearly ordered finite index
has a Cholesky factorization iff it is positive definite; on `Fin n` the factor is `cholesky A`
(`isCholesky_cholesky_of_posDef`), and it is unique (`IsCholesky.unique`). Trefethen–Bau 1997,
Thm 23.1; Golub–Van Loan 2013, Thm 4.2.7; Higham 2002, Thm 10.1.
atlas: cholesky-decomposition -/
theorem exists_isCholesky_iff_posDef (A : Matrix n n ℝ) : (∃ L, IsCholesky A L) ↔ A.PosDef := by
  refine ⟨fun ⟨_, h⟩ => h.posDef, fun hA => ?_⟩
  let e := monoEquivOfFin n rfl
  have hA' : (A.submatrix e e).PosDef := hA.submatrix e.injective
  obtain ⟨hlow, hpos, heq⟩ := isCholesky_cholesky_of_posDef hA'
  obtain ⟨L, hL, hP, hLL⟩ := exists_eq_mul_transpose_submatrix (fun x => 0 < x) hlow hpos heq e.symm
  rw [submatrix_monoEquivOfFin_symm] at hLL
  exact ⟨L, hL, hP, hLL⟩

/-- **Semidefinite Cholesky**: every positive semidefinite real matrix on a linearly ordered
finite index is `L Lᵀ` with `L` lower triangular with nonnegative diagonal (not unique in
general; on `Fin n` the witness is `cholesky A`, `eq_cholesky_mul_transpose_of_posSemidef`).
Golub–Van Loan 2013, §4.2.8; Higham 2002, Thm 10.9.
atlas: cholesky-decomposition -/
theorem exists_eq_mul_transpose_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∃ L : Matrix n n ℝ, L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ A = L * Lᵀ := by
  let e := monoEquivOfFin n rfl
  have hA' : (A.submatrix e e).PosSemidef := hA.submatrix e
  obtain ⟨L, hL, hP, hLL⟩ := exists_eq_mul_transpose_submatrix (fun x => 0 ≤ x)
    (isLowerTriangular_cholesky _) (cholesky_apply_self_nonneg _)
    (eq_cholesky_mul_transpose_of_posSemidef hA') e.symm
  rw [submatrix_monoEquivOfFin_symm] at hLL
  exact ⟨L, hL, hP, hLL⟩

end Existence

/-! ### Pivoted Cholesky for semidefinite matrices -/

section Pivoted

/-- **Pivoted Cholesky factorization** `P A Pᵀ = L Lᵀ` with `P = σ.permMatrix`, written as
`A.submatrix σ σ = L Lᵀ` (the pivots in order are `σ 0, σ 1, …`), `L` lower triangular with
nonnegative diagonal. Golub–Van Loan 2013, §4.2.9; Higham 2002, §10.3.
atlas: cholesky-algorithm -/
structure IsPivotedCholesky {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n ℝ)
    (σ : Equiv.Perm n) (L : Matrix n n ℝ) : Prop where
  /-- `L` is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- `L` has nonnegative diagonal. -/
  apply_self_nonneg : ∀ i, 0 ≤ L i i
  /-- `P A Pᵀ = L Lᵀ`. -/
  submatrix_eq : A.submatrix σ σ = L * Lᵀ

/-- The symmetric swap of diagonal pivoting: exchange index `0` with the index of the largest
diagonal entry (in modulus; the diagonal of a PSD matrix is nonnegative).
Golub–Van Loan 2013, Alg. 4.2.4 (pivot choice). -/
def diagPivotSwap {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  A.submatrix (Equiv.swap 0 (absArgmax fun i => A i i)) (Equiv.swap 0 (absArgmax fun i => A i i))

/-- **Cholesky with diagonal pivoting** as a total recursion: swap the largest diagonal entry
to the front (`diagPivotSwap`), take one Cholesky step, recurse on the Schur complement and
permute the computed column by the later pivots. Returns the pivot order `σ` and `L`.
Golub–Van Loan 2013, Alg. 4.2.4 (outer-product form with symmetric pivoting); Higham 2002,
§10.3. For PSD `A` a zero pivot means the remaining matrix is zero, and the recursion then
produces zero columns (`x / 0 = 0`), so it never fails.
atlas: cholesky-algorithm -/
def choleskyPivoted : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ →
    Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ
  | 0, A => (1, A)
  | _ + 1, A =>
    (Equiv.Perm.decomposeFin.symm
        (absArgmax (fun i => A i i), (choleskyPivoted (pivotSchur (diagPivotSwap A))).1),
      borderedMatrix (Real.sqrt (diagPivotSwap A 0 0)) 0
        (fun i => (Real.sqrt (diagPivotSwap A 0 0))⁻¹ *
          diagPivotSwap A ((choleskyPivoted (pivotSchur (diagPivotSwap A))).1 i).succ 0)
        (choleskyPivoted (pivotSchur (diagPivotSwap A))).2)

/-- Rows and columns of `A` permuted symmetrically by `decomposeFin⁻¹ (p, τ)`, as a bordered
matrix. -/
theorem submatrix_decomposeFin_symm_self {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    A.submatrix (Equiv.Perm.decomposeFin.symm (p, τ)) (Equiv.Perm.decomposeFin.symm (p, τ)) =
      borderedMatrix (A p p) (fun j => A p (Equiv.swap 0 p (τ j).succ))
        (fun i => A (Equiv.swap 0 p (τ i).succ) p)
        (fun i j => A (Equiv.swap 0 p (τ i).succ) (Equiv.swap 0 p (τ j).succ)) := by
  conv_lhs => rw [← borderedMatrix_eta (A.submatrix _ _)]
  congr 1
  · simp
  · ext j; simp
  · ext i; simp
  · ext i j; simp

/-- **Pivoted Cholesky never fails on a positive semidefinite matrix**: `choleskyPivoted A` is
a pivoted Cholesky factorization. Proof: induction on `n`; `diagPivotSwap A` and its Schur
complement stay PSD (`posSemidef_pivotSchur`), a zero pivot has a zero column
(`apply_eq_zero_of_posSemidef_of_apply_self_eq_zero`), and the step is the computation of
`eq_cholesky_mul_transpose_of_pivotSchur` conjugated by the trailing permutation.
Golub–Van Loan 2013, §4.2.9; Higham 2002, Thm 10.9.
atlas: cholesky-algorithm -/
theorem isPivotedCholesky_choleskyPivoted {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) :
    IsPivotedCholesky A (choleskyPivoted A).1 (choleskyPivoted A).2 := by
  induction n with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    have hB : (diagPivotSwap A).PosSemidef := hA.submatrix _
    obtain ⟨hL, hd, hLL⟩ := ih (posSemidef_pivotSchur hB)
    have hsym : ∀ i j, A i j = A j i := fun i j => by
      have := congrFun (congrFun hA.isHermitian j) i
      simpa using this
    refine ⟨isLowerTriangular_borderedMatrix_iff.2 ⟨rfl, hL⟩, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [choleskyPivoted]
      · simpa [choleskyPivoted] using hd i
    · set p := absArgmax fun i => A i i with hp
      have ha : 0 ≤ A p p := hA.diag_nonneg
      have hsq : Real.sqrt (A p p) * Real.sqrt (A p p) = A p p := Real.mul_self_sqrt ha
      have hinv : (Real.sqrt (A p p))⁻¹ * (Real.sqrt (A p p))⁻¹ = (A p p)⁻¹ := by
        rw [← mul_inv, hsq]
      have hcol : ∀ x, Real.sqrt (A p p) * ((Real.sqrt (A p p))⁻¹ * A x p) = A x p := by
        intro x
        rcases ha.lt_or_eq with hpos | hzero
        · rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', one_mul]
        · rw [apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA hzero.symm x, mul_zero,
            mul_zero]
      simp only [choleskyPivoted]
      rw [submatrix_decomposeFin_symm_self, transpose_borderedMatrix,
        borderedMatrix_mul_borderedMatrix, ← hLL]
      simp only [diagPivotSwap, ← hp]
      congr 1
      · simp [hsq]
      · ext j; simp [hcol, hsym p]
      · ext i; simp [hcol]
      · ext i j
        simp only [pivotSchur_apply, vecMulVec_apply, submatrix_apply, Matrix.add_apply,
          Equiv.swap_apply_left]
        rw [hsym p (Equiv.swap 0 p _)]
        linear_combination
          (A (Equiv.swap 0 p ((choleskyPivoted (pivotSchur (A.submatrix (Equiv.swap 0 p)
            (Equiv.swap 0 p)))).1 i).succ) p *
          A (Equiv.swap 0 p ((choleskyPivoted (pivotSchur (A.submatrix (Equiv.swap 0 p)
            (Equiv.swap 0 p)))).1 j).succ) p) * hinv.symm

/-- Pivoted Cholesky has a positive diagonal prefix and entirely zero trailing columns.
Source: matrix toolkit rederivations, `lem:prefix`, the rank-free recursion invariant.
atlas: cholesky-algorithm (partial) -/
theorem exists_choleskyPivoted_positive_prefix {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) :
    ∃ r ≤ n, (∀ i : Fin n, i.val < r → 0 < (choleskyPivoted A).2 i i) ∧
      (∀ i j : Fin n, r ≤ j.val → (choleskyPivoted A).2 i j = 0) := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    let B := diagPivotSwap A
    have hB : B.PosSemidef := hA.submatrix _
    by_cases hpos : 0 < B 0 0
    · obtain ⟨r, hr, hprefix, hzero⟩ := ih (posSemidef_pivotSchur hB)
      refine ⟨r + 1, by omega, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · intro hi
          simpa only [choleskyPivoted, borderedMatrix_zero_zero] using Real.sqrt_pos.mpr hpos
        · intro hi
          simpa only [choleskyPivoted, borderedMatrix_succ_succ] using hprefix i (by simpa using hi)
      · intro i j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hj
          simp only [Fin.val_zero] at hj
          omega
        · intro hj
          refine Fin.cases ?_ (fun i => ?_) i
          · simp only [choleskyPivoted, borderedMatrix_zero_succ, Pi.zero_apply]
          · simpa only [choleskyPivoted, borderedMatrix_succ_succ] using hzero i j (by simpa using hj)
    · let p := absArgmax (fun i => A i i)
      have hpivot : B 0 0 = A p p := by simp only [p, B, diagPivotSwap, submatrix_apply, Equiv.swap_apply_left]
      have hp : A p p = 0 := by have hnonneg := hA.diag_nonneg (i := p); linarith
      have hA0 : A = 0 := by
        ext i j
        have hmax := abs_le_abs_absArgmax (fun k => A k k) j
        change |A j j| ≤ |A p p| at hmax
        rw [hp, abs_zero] at hmax
        have hj : A j j = 0 := abs_eq_zero.mp (le_antisymm hmax (abs_nonneg _))
        exact apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA hj i
      have hfactor := isPivotedCholesky_choleskyPivoted hA
      have hgram : (choleskyPivoted A).2 * (choleskyPivoted A).2ᵀ = 0 := by
        rw [← hfactor.submatrix_eq, hA0]
        simp
      have hL0 : (choleskyPivoted A).2 = 0 := by
        ext i j
        have h := congrFun (congrFun hgram i) i
        have hrow : (fun k => (choleskyPivoted A).2 i k) ⬝ᵥ (fun k => (choleskyPivoted A).2 i k) = 0 := by
          simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, dotProduct] using h
        exact congrFun (dotProduct_self_eq_zero.mp hrow) j
      refine ⟨0, Nat.zero_le _, fun i hi => False.elim (Nat.not_lt_zero _ hi), ?_⟩
      intro i j hj
      rw [hL0]
      rfl

/-- The positive prefix length of the pivoted Cholesky recursion is the input matrix rank.
Source: its triangular-prefix rank certificate and exact permuted Gram factorization. -/
theorem rank_choleskyPivoted_eq_prefix {n r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hr : r ≤ n)
    (hpos : ∀ i : Fin n, i.val < r → 0 < (choleskyPivoted A).2 i i)
    (hzero : ∀ i j : Fin n, r ≤ j.val → (choleskyPivoted A).2 i j = 0) : A.rank = r := by
  have hfactor := isPivotedCholesky_choleskyPivoted hA
  calc
    A.rank = (A.submatrix (choleskyPivoted A).1 (choleskyPivoted A).1).rank :=
      (Matrix.rank_submatrix _ _ _).symm
    _ = ((choleskyPivoted A).2 * (choleskyPivoted A).2ᵀ).rank := by rw [hfactor.submatrix_eq]
    _ = (choleskyPivoted A).2.rank := Matrix.rank_self_mul_transpose _
    _ = r := Matrix.rank_eq_of_lowerTriangular_positive_prefix hr _ hfactor.isLowerTriangular hpos hzero
/-- **Pivoted Cholesky stops at the rank**: its diagonal is positive exactly in the first
`rank A` positions for every positive semidefinite input.
Source: Golub–Van Loan 2013, §4.2.9; Higham 2002, §10.3; matrix toolkit rederivations, `lem:prefix`.
atlas: cholesky-algorithm -/
theorem choleskyPivoted_apply_self_pos_iff_lt_rank {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i : Fin n) : 0 < (choleskyPivoted A).2 i i ↔ (i : ℕ) < A.rank := by
  obtain ⟨r, hr, hpos, hzero⟩ := exists_choleskyPivoted_positive_prefix hA
  rw [rank_choleskyPivoted_eq_prefix hA hr hpos hzero]
  constructor
  · intro hi
    by_contra hnot
    have hz := hzero i i (Nat.le_of_not_gt hnot)
    rw [hz] at hi
    exact lt_irrefl _ hi
  · exact hpos i

/-- **Pivoted Cholesky terminates at the rank**: all columns with index at least `rank A`
vanish for every positive semidefinite input.
Source: Golub–Van Loan 2013, §4.2.9; Higham 2002, §10.3; matrix toolkit rederivations, `lem:rankL`.
atlas: cholesky-algorithm -/
theorem choleskyPivoted_apply_eq_zero_of_rank_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i j : Fin n) (hj : A.rank ≤ (j : ℕ)) : (choleskyPivoted A).2 i j = 0 := by
  obtain ⟨r, hr, hpos, hzero⟩ := exists_choleskyPivoted_positive_prefix hA
  rw [rank_choleskyPivoted_eq_prefix hA hr hpos hzero] at hj
  exact hzero i j hj

end Pivoted

end NLAlib
