import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Basic.MoorePenrose
/-!
# The QR factorization

The factorization predicates of `docs/ALGORITHM_CONVENTIONS.md` §1 for `A = QR`:

* `IsQR A Q R` (**thin** QR): `A : m × n`, `Q : m × n` with orthonormal columns
  (`HasOrthonormalCols Q`), `R : n × n` upper triangular (Mathlib's `Matrix.IsUpperTriangular`,
  i.e. `R.BlockTriangular id`), `A = QR`. The row index `m` is any `Fintype`; the column index is
  `Fin n` because triangularity needs the order.
* `IsFullQR A Q R` (**full** QR): `A : Fin m × Fin n`, `Q : m × m` orthogonal, `R : m × n` upper
  trapezoidal (`IsUpperTrapezoidal R`: `R i j = 0` for `j < i`), `A = QR`; no relation between
  `m` and `n` is required.

Neither predicate fixes the signs of the diagonal of `R`: Householder QR produces the
Trefethen–Bau signs, Gram–Schmidt produces `R_ii ≥ 0`. Sign normalisation is the lemma
`IsQR.diagonal_mul`, and uniqueness (`IsQR.eq_of_diag_pos`) is stated for positive diagonals.

## Contents

* Identities: `Qᵀ A = R` (`IsQR.transpose_mul_eq`), `Aᵀ A = Rᵀ R` (`IsQR.transpose_mul_self_eq`,
  so `Rᵀ` is the Cholesky factor of `AᵀA` when `R_ii > 0`), full column rank iff `R_ii ≠ 0`
  (`IsQR.isUnit_transpose_mul_self_iff`), `A⁺ = R⁻¹ Qᵀ` (`pinvL_eq_of_isQR`,
  `moorePenroseInverse_eq_of_isQR`), `QQᵀ = AA⁺` (`IsQR.mul_transpose_eq`) and
  `range A = range Q` (`IsQR.range_mulVecLin_eq`).
* Transport: sign normalisation `IsQR.diagonal_mul`, row reindexing `IsQR.submatrix_rows`,
  thin from full `IsFullQR.isQR_castLE`.
* Existence: `exists_isFullQR` (induction with an orthogonal completion step,
  `isFullQR_mul_borderedUpper`; realised constructively by `householderQR` in
  `NLAlib.Matrix.Factorizations.Householder`), `exists_isQR` (thin, `R_ii ≥ 0`, for `n ≤ |m|`),
  `exists_isQR_of_isUnit` (`R_ii > 0` under full column rank).
* Uniqueness: `IsQR.eq_of_diag_pos` (positive diagonals).

Sources: Trefethen–Bau 1997 [`tb97`], Lect. 7 (Thm 7.1, 7.2); Golub–Van Loan 2013 [`gvl13`],
§5.2 (Thm 5.2.1, 5.2.3).
Atlas: `qr-decomposition`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-! ### Predicates -/

section Predicates

variable {m : Type*} [Fintype m] {n : ℕ}

/-- **Thin QR factorization**: `A = QR` with `Q : m × n` having orthonormal columns and
`R : n × n` upper triangular. The signs of `R_ii` are not fixed (see `IsQR.diagonal_mul`); the
alternative convention `R_ii ≥ 0` is a separate conjunct where it is needed (`exists_isQR`).
Trefethen–Bau 1997, Lect. 7 (reduced QR); Golub–Van Loan 2013, Thm 5.2.3 (thin QR).
atlas: qr-decomposition (partial) -/
structure IsQR (A Q : Matrix m (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The factorization `A = QR`. -/
  eq : A = Q * R
  /-- `Q` has orthonormal columns, `Qᵀ Q = I`. -/
  orth : HasOrthonormalCols Q
  /-- `R` is upper triangular. -/
  upper : R.IsUpperTriangular

end Predicates

section Trapezoidal

variable {m n : ℕ}

/-- A rectangular matrix is **upper trapezoidal** (upper triangular in the rectangular sense):
`R i j = 0` whenever `j < i`. For square matrices this is Mathlib's `IsUpperTriangular`
(`isUpperTrapezoidal_iff_isUpperTriangular`). Golub–Van Loan 2013, §5.2 (the `R` of a full QR).
atlas: qr-decomposition (partial) -/
def IsUpperTrapezoidal (R : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0

/-- On square matrices, upper trapezoidal is Mathlib's upper triangular (bridge lemma).
Golub–Van Loan 2013, §3.1. -/
theorem isUpperTrapezoidal_iff_isUpperTriangular (R : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperTrapezoidal R ↔ R.IsUpperTriangular :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h (Fin.lt_def.2 hij)⟩

/-- **Full QR factorization**: `A = QR` with `Q : m × m` orthogonal and `R : m × n` upper
trapezoidal. No relation between `m` and `n` is assumed. Trefethen–Bau 1997, Lect. 7 (full QR);
Golub–Van Loan 2013, Thm 5.2.1.
atlas: qr-decomposition (partial) -/
structure IsFullQR (A : Matrix (Fin m) (Fin n) ℝ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) : Prop where
  /-- The factorization `A = QR`. -/
  eq : A = Q * R
  /-- `Q` is orthogonal, `Qᵀ Q = I`. -/
  orth : HasOrthonormalCols Q
  /-- `R` is upper trapezoidal. -/
  upper : IsUpperTrapezoidal R

/-- The `Q` of a full QR is orthogonal on both sides: `Q Qᵀ = I`. Golub–Van Loan 2013, §2.1. -/
theorem IsFullQR.mul_transpose_self {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsFullQR A Q R) : Q * Qᵀ = 1 :=
  mul_eq_one_comm.mp h.orth

/-- The `R` of a full QR is `Qᵀ A`. Golub–Van Loan 2013, §5.2. -/
theorem IsFullQR.transpose_mul_eq {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsFullQR A Q R) : Qᵀ * A = R := by
  rw [h.eq, ← Matrix.mul_assoc, show Qᵀ * Q = 1 from h.orth, Matrix.one_mul]

/-- **Thin QR from full QR**: if `n ≤ m`, the first `n` columns of `Q` and the first `n` rows
of `R` form a thin QR. Trefethen–Bau 1997, Lect. 7 (reduced from full QR); Golub–Van Loan 2013,
Thm 5.2.3 (proof).
atlas: qr-decomposition (partial) -/
theorem IsFullQR.isQR_castLE {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsFullQR A Q R) (hnm : n ≤ m) :
    IsQR A (Q.submatrix id (Fin.castLE hnm)) (R.submatrix (Fin.castLE hnm) id) where
  eq := by
    obtain ⟨r, rfl⟩ : ∃ r, m = n + r := ⟨m - n, by omega⟩
    rw [h.eq]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    rw [Fin.sum_univ_add]
    have hz : ∑ k : Fin r, Q i (Fin.natAdd n k) * R (Fin.natAdd n k) j = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [h.upper _ _ (by simp only [Fin.val_natAdd]; omega), mul_zero]
    rw [hz, add_zero]
    rfl
  orth := by
    change (Q.submatrix id (Fin.castLE hnm))ᵀ * Q.submatrix id (Fin.castLE hnm) = 1
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      show Qᵀ * Q = 1 from h.orth, Matrix.submatrix_one _ (Fin.castLE_injective hnm)]
  upper := fun i j hij => h.upper (Fin.castLE hnm i) j hij

/-- The rectangular bordered matrix `[[r], [0, M]]`: first row `r`, zeros below the pivot, and
trailing block `M`. The `R` of one Householder step. (Rectangular analogue of
`borderedMatrix` in `NLAlib.Matrix.Factorizations.Triangular`; `borderedUpper (vecCons 1 0) M` is
`diag(1, M)`.) Golub–Van Loan 2013, §5.2.2. -/
def borderedUpper (r : Fin (n + 1) → ℝ) (M : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (vecCons r fun i => vecCons 0 (M i))

@[simp]
theorem borderedUpper_zero (r : Fin (n + 1) → ℝ) (M : Matrix (Fin m) (Fin n) ℝ) (j : Fin (n + 1)) :
    borderedUpper r M 0 j = r j := rfl

@[simp]
theorem borderedUpper_succ_zero (r : Fin (n + 1) → ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) : borderedUpper r M i.succ 0 = 0 := by
  simp [borderedUpper]

@[simp]
theorem borderedUpper_succ_succ (r : Fin (n + 1) → ℝ) (M : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : borderedUpper r M i.succ j.succ = M i j := by
  simp [borderedUpper]

/-- `[[r], [0, M]]` is upper trapezoidal when `M` is. Golub–Van Loan 2013, §5.2.2. -/
theorem isUpperTrapezoidal_borderedUpper (r : Fin (n + 1) → ℝ) {M : Matrix (Fin m) (Fin n) ℝ}
    (hM : IsUpperTrapezoidal M) : IsUpperTrapezoidal (borderedUpper r M) := by
  intro i j hij
  induction i using Fin.cases with
  | zero => simp at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp
    | succ j => simpa using hM i j (by simpa using hij)

/-- `diag(1, M) [[r], [0, N]] = [[r], [0, M N]]`. Golub–Van Loan 2013, §1.3 (block products). -/
theorem borderedUpper_one_mul_borderedUpper {k : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (r : Fin (k + 1) → ℝ) (N : Matrix (Fin m) (Fin k) ℝ) :
    borderedUpper (vecCons 1 0) M * borderedUpper r N = borderedUpper r (M * N) := by
  ext i j
  induction i using Fin.cases with
  | zero => simp [Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [Matrix.mul_apply, Fin.sum_univ_succ]
    | succ j => simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- `diag(1, I) = I`. -/
theorem borderedUpper_one_one : borderedUpper (vecCons 1 0) (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  ext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp
    | succ j => simp [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp
    | succ j => simp [Matrix.one_apply]

/-- `diag(1, M)ᵀ = diag(1, Mᵀ)`. -/
theorem transpose_borderedUpper_one (M : Matrix (Fin m) (Fin m) ℝ) :
    (borderedUpper (vecCons 1 0) M)ᵀ = borderedUpper (vecCons 1 0) Mᵀ := by
  ext i j
  induction i using Fin.cases with
  | zero => induction j using Fin.cases <;> simp
  | succ i => induction j using Fin.cases <;> simp

/-- **One step of a full QR**: if `W` is orthogonal, `B = WᵀA` has zeros below the pivot in its
first column, and `B(1:, 1:) = Q'R'` is a full QR, then
`A = (W · diag(1, Q')) · [[B(0, :)], [0, R']]` is a full QR. This is the inductive step of every
orthogonal triangularisation (Householder, Givens, orthogonal completion).
Trefethen–Bau 1997, Lect. 10, eq. (10.1)–(10.3); Golub–Van Loan 2013, §5.2.2. -/
theorem isFullQR_mul_borderedUpper {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ}
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hW : Wᵀ * W = 1)
    (hB : ∀ i : Fin m, (Wᵀ * A) i.succ 0 = 0) {Q' : Matrix (Fin m) (Fin m) ℝ}
    {R' : Matrix (Fin m) (Fin n) ℝ} (h' : IsFullQR ((Wᵀ * A).submatrix Fin.succ Fin.succ) Q' R') :
    IsFullQR A (W * borderedUpper (vecCons 1 0) Q') (borderedUpper ((Wᵀ * A) 0) R') where
  eq := by
    have hblock : borderedUpper (vecCons 1 0) Q' * borderedUpper ((Wᵀ * A) 0) R' = Wᵀ * A := by
      rw [borderedUpper_one_mul_borderedUpper, ← h'.eq]
      ext i j
      induction i using Fin.cases with
      | zero => rfl
      | succ i =>
        induction j using Fin.cases with
        | zero => rw [borderedUpper_succ_zero, hB]
        | succ j => rw [borderedUpper_succ_succ]; rfl
    rw [Matrix.mul_assoc, hblock, ← Matrix.mul_assoc, mul_eq_one_comm.mp hW, Matrix.one_mul]
  orth := by
    change (W * borderedUpper (vecCons 1 0) Q')ᵀ * (W * borderedUpper (vecCons 1 0) Q') = 1
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul,
      transpose_borderedUpper_one, borderedUpper_one_mul_borderedUpper,
      show Q'ᵀ * Q' = 1 from h'.orth, borderedUpper_one_one]
  upper := isUpperTrapezoidal_borderedUpper _ h'.upper

end Trapezoidal

/-! ### Identities -/

section Identities

variable {m : Type*} [Fintype m] {n : ℕ} {A Q : Matrix m (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}

namespace IsQR

/-- `Qᵀ A = R`. Trefethen–Bau 1997, Lect. 7; Golub–Van Loan 2013, §5.2.
atlas: qr-decomposition (partial) -/
theorem transpose_mul_eq (h : IsQR A Q R) : Qᵀ * A = R := by
  rw [h.eq, ← Matrix.mul_assoc, show Qᵀ * Q = 1 from h.orth, Matrix.one_mul]

/-- `Aᵀ A = Rᵀ R`: `Rᵀ` is a (Cholesky) triangular factor of the Gram matrix `AᵀA`.
Trefethen–Bau 1997, Lect. 11 (normal equations via QR); Golub–Van Loan 2013, §5.2.
atlas: qr-decomposition (partial) -/
theorem transpose_mul_self_eq (h : IsQR A Q R) : Aᵀ * A = Rᵀ * R := by
  rw [h.eq, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ,
    show Qᵀ * Q = 1 from h.orth, Matrix.one_mul]

/-- `det R = ∏ R_ii` (Mathlib's `det_of_isUpperTriangular`). Golub–Van Loan 2013, §3.1. -/
theorem det_eq (h : IsQR A Q R) : R.det = ∏ i, R i i :=
  det_of_isUpperTriangular h.upper

/-- `R` is invertible iff its diagonal has no zero. Golub–Van Loan 2013, §3.1. -/
theorem isUnit_det_iff (h : IsQR A Q R) : IsUnit R.det ↔ ∀ i, R i i ≠ 0 := by
  rw [h.det_eq, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp

/-- **Full column rank iff nonzero diagonal**: `AᵀA` is invertible iff every `R_ii ≠ 0`.
Trefethen–Bau 1997, Thm 7.2 (proof); Golub–Van Loan 2013, Thm 5.2.3.
atlas: qr-decomposition (partial) -/
theorem isUnit_transpose_mul_self_iff (h : IsQR A Q R) :
    IsUnit (Aᵀ * A) ↔ ∀ i, R i i ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, h.transpose_mul_self_eq, Matrix.det_mul, Matrix.det_transpose,
    IsUnit.mul_iff, and_self, h.isUnit_det_iff]

/-- `range A = range Q` when `R` is invertible. Trefethen–Bau 1997, Lect. 7 (the columns of `Q`
span the column flag); Golub–Van Loan 2013, Thm 5.2.3.
atlas: qr-decomposition (partial) -/
theorem range_mulVecLin_eq (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) :
    LinearMap.range A.mulVecLin = LinearMap.range Q.mulVecLin := by
  have hdet : IsUnit R.det := h.isUnit_det_iff.2 hR
  have hQ : Q = A * R⁻¹ := by rw [h.eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
    Matrix.mul_one]
  apply le_antisymm
  · rw [h.eq, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  · rw [hQ, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _

/-- **Sign normalisation**: multiplying `Q` on the right and `R` on the left by a diagonal sign
matrix `D` (`D² = I`) gives another thin QR. Trefethen–Bau 1997, Thm 7.1 (proof, sign choice);
Golub–Van Loan 2013, §5.2. -/
theorem diagonal_mul (h : IsQR A Q R) (d : Fin n → ℝ) (hd : ∀ i, d i * d i = 1) :
    IsQR A (Q * diagonal d) (diagonal d * R) where
  eq := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal d), diagonal_mul_diagonal,
      show (fun i => d i * d i) = fun _ => 1 from funext hd, diagonal_one, Matrix.one_mul, h.eq]
  orth := by
    change (Q * diagonal d)ᵀ * (Q * diagonal d) = 1
    rw [Matrix.transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ,
      show Qᵀ * Q = 1 from h.orth, Matrix.one_mul, diagonal_mul_diagonal,
      show (fun i => d i * d i) = fun _ => 1 from funext hd, diagonal_one]
  upper := (blockTriangular_diagonal d).mul h.upper

/-- **Row reindexing**: a thin QR of `A` transports along any bijection of the row index.
Bridge from `Fin` to general `Fintype` row indices. -/
theorem submatrix_rows (h : IsQR A Q R) {m' : Type*} [Fintype m'] (e : m' ≃ m) :
    IsQR (A.submatrix e id) (Q.submatrix e id) R where
  eq := by
    rw [h.eq, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  orth := by
    change (Q.submatrix e id)ᵀ * Q.submatrix e id = 1
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
      show Qᵀ * Q = 1 from h.orth, Matrix.submatrix_id_id]
  upper := h.upper

end IsQR

/-- **Pseudoinverse via QR**: under full column rank (`R_ii ≠ 0`), `(AᵀA)⁻¹Aᵀ = R⁻¹Qᵀ`.
Trefethen–Bau 1997, Lect. 11 (Alg. 11.2); Golub–Van Loan 2013, §5.3.3.
atlas: qr-decomposition (partial) -/
theorem pinvL_eq_of_isQR (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) : pinvL A = R⁻¹ * Qᵀ := by
  have hdet : IsUnit R.det := h.isUnit_det_iff.2 hR
  have hdetT : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
  unfold pinvL
  rw [h.transpose_mul_self_eq, Matrix.mul_inv_rev]
  conv_lhs => rw [h.eq, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ⁻¹, Matrix.nonsing_inv_mul _ hdetT, Matrix.one_mul]

/-- The Moore–Penrose inverse via QR: under full column rank, `A⁺ = R⁻¹ Qᵀ`.
Trefethen–Bau 1997, Lect. 11; Golub–Van Loan 2013, §5.3.3.
atlas: qr-decomposition (partial) -/
theorem moorePenroseInverse_eq_of_isQR (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) :
    moorePenroseInverse A = R⁻¹ * Qᵀ := by
  rw [moorePenroseInverse_eq_pinvL A (h.isUnit_transpose_mul_self_iff.2 hR),
    pinvL_eq_of_isQR h hR]

/-- **`QQᵀ` is the orthogonal projector onto `range A`**: `QQᵀ = AA⁺` under full column rank.
Trefethen–Bau 1997, Lect. 6–7; Golub–Van Loan 2013, §5.2.
atlas: qr-decomposition (partial) -/
theorem IsQR.mul_transpose_eq (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) :
    Q * Qᵀ = A * moorePenroseInverse A := by
  rw [moorePenroseInverse_eq_of_isQR h hR, h.eq, Matrix.mul_assoc, ← Matrix.mul_assoc R,
    Matrix.mul_nonsing_inv _ (h.isUnit_det_iff.2 hR), Matrix.one_mul]

end Identities

/-! ### Existence and uniqueness -/

/-- For every `A : (m+1) × (n+1)` there is an orthogonal `W` with `WᵀA` zero below the pivot in
its first column: `W` completes `a₀ / ‖a₀‖` to an orthonormal basis
(`exists_orthogonal_completion`), or `W = I` when `a₀ = 0`. The reflector-free form of one
Householder step. Golub–Van Loan 2013, §5.2.2. -/
theorem exists_transpose_mul_apply_succ_zero_eq_zero {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) :
    ∃ W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, Wᵀ * W = 1 ∧
      ∀ i : Fin m, (Wᵀ * A) i.succ 0 = 0 := by
  by_cases ha : A.col 0 ⬝ᵥ A.col 0 = 0
  · refine ⟨1, by simp, fun i => ?_⟩
    have h0 := congrFun (dotProduct_self_eq_zero.1 ha) i.succ
    simpa using h0
  · have hnn : 0 ≤ A.col 0 ⬝ᵥ A.col 0 := by
      unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    set c := √(A.col 0 ⬝ᵥ A.col 0) with hcdef
    have hc : c ≠ 0 := by
      rw [hcdef, Real.sqrt_ne_zero hnn]; exact ha
    have hc2 : c * c = A.col 0 ⬝ᵥ A.col 0 := Real.mul_self_sqrt hnn
    let V : Matrix (Fin (m + 1)) (Fin 1) ℝ := Matrix.of fun i _ => A i 0 / c
    have hV : Vᵀ * V = 1 := by
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0, Matrix.one_apply_eq]
      simp only [Matrix.mul_apply, transpose_apply, V, of_apply]
      rw [show ∑ k, A k 0 / c * (A k 0 / c) = (A.col 0 ⬝ᵥ A.col 0) / (c * c) by
        rw [dotProduct, Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by simp only [col_apply]; ring]
      rw [hc2, div_self ha]
    obtain ⟨W, hW, hWV⟩ := exists_orthogonal_completion V hV
      ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
    refine ⟨W, hW, fun i => ?_⟩
    have hA : ∀ k, A k 0 = c * W k 0 := fun k => by
      rw [show W k 0 = V k 0 from hWV k 0]
      simp only [V, of_apply]
      field_simp
    have hWW := congrFun (congrFun hW i.succ) 0
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero i), Matrix.mul_apply] at hWW
    rw [Matrix.mul_apply]
    simp_rw [hA]
    rw [show ∑ k, Wᵀ i.succ k * (c * W k 0) = c * ∑ k, Wᵀ i.succ k * W k 0 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hWW, mul_zero]

/-- **Existence of a full QR** for every real `m × n` matrix, with no rank or shape hypothesis.
Trefethen–Bau 1997, Thm 7.1 (existence); Golub–Van Loan 2013, Thm 5.2.1. Proof: induction on
`m`; one orthogonal step (`exists_transpose_mul_apply_succ_zero_eq_zero`) and
`isFullQR_mul_borderedUpper`. The constructive version with Householder reflectors is
`isFullQR_householderQR` (`NLAlib.Matrix.Factorizations.Householder`).
atlas: qr-decomposition (partial) -/
theorem exists_isFullQR : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ), ∃ Q R, IsFullQR A Q R
  | 0, _, A => ⟨1, A, ⟨by simp, by simp [HasOrthonormalCols], fun i => i.elim0⟩⟩
  | _ + 1, 0, A => ⟨1, A, ⟨by simp, by simp [HasOrthonormalCols], fun _ j => j.elim0⟩⟩
  | _ + 1, _ + 1, A => by
    obtain ⟨W, hW, hB⟩ := exists_transpose_mul_apply_succ_zero_eq_zero A
    obtain ⟨Q', R', h'⟩ := exists_isFullQR ((Wᵀ * A).submatrix Fin.succ Fin.succ)
    exact ⟨_, _, isFullQR_mul_borderedUpper hW hB h'⟩

/-- **Existence of a thin QR with nonnegative diagonal** for every real matrix with at least as
many rows as columns (`n ≤ |m|`); no rank hypothesis. Trefethen–Bau 1997, Thm 7.1;
Golub–Van Loan 2013, Thm 5.2.3. Proof: full QR (`exists_isFullQR`), its first `n` columns
(`IsFullQR.isQR_castLE`), then sign normalisation (`IsQR.diagonal_mul`), after reindexing the
rows by `Fin |m|`.
atlas: qr-decomposition (partial) -/
theorem exists_isQR {m : Type*} [Fintype m] {n : ℕ} (A : Matrix m (Fin n) ℝ)
    (hn : n ≤ Fintype.card m) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 ≤ R i i := by
  let e := Fintype.equivFin m
  obtain ⟨Q₀, R₀, h₀⟩ := exists_isFullQR (A.submatrix e.symm id)
  have h₁ := (h₀.isQR_castLE hn).submatrix_rows e
  rw [show (A.submatrix e.symm id).submatrix e id = A by ext; simp] at h₁
  set R₁ := R₀.submatrix (Fin.castLE hn) id
  let d : Fin n → ℝ := fun i => if 0 ≤ R₁ i i then 1 else -1
  have hd : ∀ i, d i * d i = 1 := fun i => by by_cases hi : 0 ≤ R₁ i i <;> simp [d, hi]
  refine ⟨_, _, h₁.diagonal_mul d hd, fun i => ?_⟩
  rw [Matrix.diagonal_mul]
  by_cases hi : 0 ≤ R₁ i i
  · simp [d, hi]
  · simp only [d, hi, if_false]; linarith

/-- **Existence with positive diagonal under full column rank**: if `AᵀA` is invertible
(`rank A = n`), `A` has a thin QR with `R_ii > 0`. Trefethen–Bau 1997, Thm 7.2;
Golub–Van Loan 2013, Thm 5.2.3. The row-count condition `n ≤ |m|` follows from the rank.
atlas: qr-decomposition (partial) -/
theorem exists_isQR_of_isUnit {m : Type*} [Fintype m] {n : ℕ} {A : Matrix m (Fin n) ℝ}
    (hA : IsUnit (Aᵀ * A)) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 < R i i := by
  have hn : n ≤ Fintype.card m := by
    have h1 := Matrix.rank_of_isUnit _ hA
    rw [Matrix.rank_transpose_mul_self, Fintype.card_fin] at h1
    exact h1 ▸ Matrix.rank_le_card_height A
  obtain ⟨Q, R, h, hpos⟩ := exists_isQR A hn
  exact ⟨Q, R, h, fun i => lt_of_le_of_ne (hpos i)
    (h.isUnit_transpose_mul_self_iff.1 hA i).symm⟩

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals
(helper; also `mul_apply_self_of_isUpperTriangular` in `Factorizations.Triangular`). -/
private lemma mul_apply_self_of_upper {n : ℕ} {S T : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (i : Fin n) :
    (S * T) i i = S i i * T i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hS h, zero_mul]
    · rw [hT h, mul_zero]
  · simp

/-- **Uniqueness of the thin QR with positive diagonal**: two thin QR factorizations of the same
`A` whose `R` factors have positive diagonals coincide. (Positivity of the diagonal forces full
column rank, so no separate rank hypothesis is needed.) Trefethen–Bau 1997, Thm 7.2;
Golub–Van Loan 2013, Thm 5.2.3. Proof: `T := Q₂ᵀQ₁` satisfies `T R₁ = R₂` and
`Tᵀ R₂ = R₁` (`IsQR.transpose_mul_eq`), so `T = R₂R₁⁻¹` and `Tᵀ = R₁R₂⁻¹` are both upper
triangular, hence `T` is diagonal, with `T_ii R₁ii = R₂ii`, `T_ii R₂ii = R₁ii`, so `T_ii² = 1`,
`T_ii > 0`; thus `T = I`, `R₂ = R₁` and `Q₂ = A R₂⁻¹ = Q₁`.
atlas: qr-decomposition (partial) -/
theorem IsQR.eq_of_diag_pos {m : Type*} [Fintype m] {n : ℕ} {A Q₁ Q₂ : Matrix m (Fin n) ℝ}
    {R₁ R₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : IsQR A Q₁ R₁) (h₂ : IsQR A Q₂ R₂)
    (hR₁ : ∀ i, 0 < R₁ i i) (hR₂ : ∀ i, 0 < R₂ i i) : Q₁ = Q₂ ∧ R₁ = R₂ := by
  have hd₁ : IsUnit R₁.det := h₁.isUnit_det_iff.2 fun i => (hR₁ i).ne'
  have hd₂ : IsUnit R₂.det := h₂.isUnit_det_iff.2 fun i => (hR₂ i).ne'
  set T := Q₂ᵀ * Q₁ with hTdef
  have hT : T * R₁ = R₂ := by rw [Matrix.mul_assoc, ← h₁.eq, h₂.transpose_mul_eq]
  have hT' : Tᵀ * R₂ = R₁ := by
    rw [hTdef, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← h₂.eq,
      h₁.transpose_mul_eq]
  have hinv₁ : R₁⁻¹.IsUpperTriangular := by
    have := R₁.invertibleOfIsUnitDet hd₁; exact blockTriangular_inv_of_blockTriangular h₁.upper
  have hinv₂ : R₂⁻¹.IsUpperTriangular := by
    have := R₂.invertibleOfIsUnitDet hd₂; exact blockTriangular_inv_of_blockTriangular h₂.upper
  have hTu : T.IsUpperTriangular := by
    have : T = R₂ * R₁⁻¹ := by
      rw [← hT, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd₁, Matrix.mul_one]
    rw [this]; exact h₂.upper.mul hinv₁
  have hTl : Tᵀ.IsUpperTriangular := by
    have : Tᵀ = R₁ * R₂⁻¹ := by
      rw [← hT', Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd₂, Matrix.mul_one]
    rw [this]; exact h₁.upper.mul hinv₂
  have hdiag : ∀ i, T i i = 1 := by
    intro i
    have e1 := mul_apply_self_of_upper hTu h₁.upper i
    have e2 := mul_apply_self_of_upper hTl h₂.upper i
    rw [hT] at e1; rw [hT', Matrix.transpose_apply] at e2
    have hpos : 0 < T i i := by
      have := hR₂ i; rw [e1] at this; exact pos_of_mul_pos_left this (hR₁ i).le
    have hsq : T i i * T i i = 1 := by
      have : T i i * T i i * R₁ i i = 1 * R₁ i i := by
        rw [one_mul, mul_assoc, ← e1, ← e2]
      exact mul_right_cancel₀ (hR₁ i).ne' this
    nlinarith
  have hT1 : T = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.one_apply_ne h.ne]
      exact hTl h
    · rw [hdiag, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h.ne', hTu h]
  have hR : R₁ = R₂ := by rw [← hT, hT1, Matrix.one_mul]
  refine ⟨?_, hR⟩
  have hQ : ∀ {Q R}, IsQR A Q R → IsUnit R.det → Q = A * R⁻¹ := fun h hd => by
    rw [h.eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  rw [hQ h₁ hd₁, hQ h₂ hd₂, hR]

end NLAlib
