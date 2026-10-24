import NLAlib.Matrix.Factorizations.Givens
import NLAlib.Matrix.Factorizations.GramSchmidtClassical
import NLAlib.Matrix.Structured.Hessenberg
import NLAlib.Krylov.Spaces.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
/-!
# The QR algorithm is simultaneous iteration

The (shifted) QR algorithm, driven by any QR routine `qr` and any shift sequence `μ`:
`A₀ = A`, `A_j − μ_j I = Q_{j+1} R_{j+1}` (with `(Q_{j+1}, R_{j+1}) = qr (A_j − μ_j I)`),
`A_{j+1} = R_{j+1} Q_{j+1} + μ_j I`; the accumulated factors are
`Q^{(k)} = Q_1 ⋯ Q_k` and `R^{(k)} = R_k ⋯ R_1`.

* The recursion: `NLAlib.qrAlgorithm qr μ A k` (`A_k`), `qrAlgorithmFactors` (the `k`-th
  factor pair), `qrAlgorithmQ`, `qrAlgorithmR`. Total for every `qr`.
* The success predicate `QRAlgorithmSucceeds qr μ A k`: each of the first `k` factor pairs is a
  QR factorization (`IsQR`) of the matrix it was computed from. It holds for every `k` when `qr`
  is a QR routine on all matrices (`qrAlgorithmSucceeds_of_forall_isQR`), and for the Givens
  routine `givensQR` on an upper Hessenberg `A` (`qrAlgorithmSucceeds_givensQR`).
* Realisation (T&B Thm 28.3, shifted form): `A_k = Q^{(k)ᵀ} A Q^{(k)}`
  (`qrAlgorithm_eq_transpose_mul_mul`), `Q^{(k)}` orthogonal, `R^{(k)}` upper triangular, and
  `∏_{j<k} (A − μ_j I) = Q^{(k)} R^{(k)}` (`aeval_prod_eq_qrAlgorithmQ_mul_qrAlgorithmR`);
  unshifted, `A^k = Q^{(k)} R^{(k)}` is a QR factorization of `A^k` (`isQR_pow_qrAlgorithm`),
  and the leading columns of `Q^{(k)}` span the subspace iterates of the leading columns of `I`
  (`range_qrAlgorithmQ_castLE_eq_subspaceIterate`).
* One shifted step is an orthogonal similarity (`add_smul_one_eq_transpose_mul_mul_of_isQR`).
* Structure: symmetry is preserved (`isHermitian_qrAlgorithm`); upper Hessenberg form is preserved
  when every `R_j` is invertible (`isUpperHessenberg_qrAlgorithm`, e.g. when no shift is an
  eigenvalue, `qrAlgorithmFactors_snd_apply_self_ne_zero`), hence symmetric tridiagonal form
  too (`isTridiagonal_qrAlgorithm`); with the Givens routine no invertibility is needed
  (`isUpperHessenberg_qrAlgorithm_givensQR`, `isTridiagonal_qrAlgorithm_givensQR`).

The convergence theorem (T&B Thm 28.4) is a separate future entry consuming
`subspace-iteration-convergence`.

Uses the shape predicates `IsUpperHessenberg`, `IsTridiagonal` and their closure lemmas
(`IsUpperHessenberg.sub_smul_one`, `IsUpperHessenberg.add_smul_one`,
`IsUpperHessenberg.isTridiagonal_of_isSymm`) from `NLAlib.Matrix.Structured.Hessenberg`, and
`isUpperHessenberg_mul_of_isQR`, `isUpperHessenberg_givensQR_snd_mul_fst`, `isQR_givensQR` from
`NLAlib.Matrix.Factorizations.Givens`.

Source: Trefethen–Bau (1997) [`tb97`], Lect. 28 (Thm 28.3), Lect. 29; Golub–Van Loan (2013)
[`gvl13`], §7.3.1, §7.4.2, §8.3.
Atlas: `qr-algorithm-simultaneous-iteration`.
-/

noncomputable section

open scoped Matrix
open Matrix Polynomial

namespace NLAlib

variable {n : ℕ}

/-! ### One step -/

/-- **A shifted QR step is an orthogonal similarity.** If `H − μI = QR` is a (square) QR
factorization then `RQ + μI = QᵀHQ`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 29 (Alg.
29.1); Golub–Van Loan (2013) [`gvl13`], §7.5.1.
atlas: qr-algorithm-simultaneous-iteration -/
theorem add_smul_one_eq_transpose_mul_mul_of_isQR {H Q R : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (h : IsQR (H - μ • (1 : Matrix (Fin n) (Fin n) ℝ)) Q R) :
    R * Q + μ • (1 : Matrix (Fin n) (Fin n) ℝ) = Qᵀ * H * Q := by
  have hQQ : Qᵀ * Q = 1 := h.orth
  have hR : Qᵀ * (H - μ • (1 : Matrix (Fin n) (Fin n) ℝ)) = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial Q] using h.conjTranspose_mul_eq
  rw [← hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hQQ, sub_add_cancel]

/-! ### The recursion -/

/-- The **shifted QR algorithm** driven by a QR routine `qr` and shifts `μ`: `A₀ = A`,
`A_{k+1} = R Q + μ_k I` where `(Q, R) = qr (A_k − μ_k I)`. Total for every `qr`; it computes the
QR algorithm when `QRAlgorithmSucceeds` holds. The unshifted algorithm is `μ = fun _ => 0`.
Source: Trefethen–Bau (1997) [`tb97`], Alg. 28.1 (unshifted), Alg. 29.1 (shifted);
Golub–Van Loan (2013) [`gvl13`], §7.3.1, §7.5. Alternative: hypotheses on arbitrary sequences
`Q_j, R_j`; a routine argument keeps the recursion total and lets `qr` be `givensQR` or any
choice of QR.
atlas: qr-algorithm-simultaneous-iteration -/
def qrAlgorithm
    (qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (μ : ℕ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | k + 1 =>
    let F := qr (qrAlgorithm qr μ A k - μ k • (1 : Matrix (Fin n) (Fin n) ℝ))
    F.2 * F.1 + μ k • (1 : Matrix (Fin n) (Fin n) ℝ)

variable (qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
  (μ : ℕ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)

/-- The factor pair `(Q_{k+1}, R_{k+1}) = qr (A_k − μ_k I)` of step `k`. Source: Trefethen–Bau
(1997) [`tb97`], Alg. 28.1. Helper for `qr-algorithm-simultaneous-iteration`. -/
def qrAlgorithmFactors (k : ℕ) : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  qr (qrAlgorithm qr μ A k - μ k • (1 : Matrix (Fin n) (Fin n) ℝ))

/-- The accumulated orthogonal factor `Q^{(k)} = Q_1 ⋯ Q_k`. Source: Trefethen–Bau (1997)
[`tb97`], Lect. 28 (eq. 28.8). Helper for `qr-algorithm-simultaneous-iteration`. -/
def qrAlgorithmQ : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => qrAlgorithmQ k * (qrAlgorithmFactors qr μ A k).1

/-- The accumulated triangular factor `R^{(k)} = R_k ⋯ R_1`. Source: Trefethen–Bau (1997)
[`tb97`], Lect. 28 (eq. 28.8). Helper for `qr-algorithm-simultaneous-iteration`. -/
def qrAlgorithmR : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => (qrAlgorithmFactors qr μ A k).2 * qrAlgorithmR k

/-- **Success predicate**: each of the first `k` factor pairs is a QR factorization of the
matrix it was computed from, `A_j − μ_j I = Q_{j+1} R_{j+1}` with `Q_{j+1}` orthogonal and
`R_{j+1}` upper triangular. The QR algorithm itself never breaks down; this records that `qr`
did its job along the run. Source: Trefethen–Bau (1997) [`tb97`], Alg. 28.1.
atlas: qr-algorithm-simultaneous-iteration -/
def QRAlgorithmSucceeds (k : ℕ) : Prop :=
  ∀ j < k, IsQR (qrAlgorithm qr μ A j - μ j • (1 : Matrix (Fin n) (Fin n) ℝ))
    (qrAlgorithmFactors qr μ A j).1 (qrAlgorithmFactors qr μ A j).2

/-- `A₀ = A`. Helper for `qr-algorithm-simultaneous-iteration`. -/
@[simp]
theorem qrAlgorithm_zero : qrAlgorithm qr μ A 0 = A := rfl

/-- `A_{k+1} = R_{k+1} Q_{k+1} + μ_k I`. Helper for `qr-algorithm-simultaneous-iteration`. -/
theorem qrAlgorithm_succ (k : ℕ) :
    qrAlgorithm qr μ A (k + 1) =
      (qrAlgorithmFactors qr μ A k).2 * (qrAlgorithmFactors qr μ A k).1 +
        μ k • (1 : Matrix (Fin n) (Fin n) ℝ) := rfl

variable {qr μ A}

/-- The success predicate is monotone in `k`. Helper for
`qr-algorithm-simultaneous-iteration`. -/
theorem QRAlgorithmSucceeds.mono {k k' : ℕ} (h : QRAlgorithmSucceeds qr μ A k) (hk : k' ≤ k) :
    QRAlgorithmSucceeds qr μ A k' := fun j hj => h j (lt_of_lt_of_le hj hk)

/-- A routine that returns a QR factorization of every matrix makes the algorithm succeed for
every `k` (such routines exist: `exists_isFullQR`, Householder). Source: Trefethen–Bau (1997)
[`tb97`], Alg. 28.1.
atlas: qr-algorithm-simultaneous-iteration -/
theorem qrAlgorithmSucceeds_of_forall_isQR
    (hqr : ∀ M, IsQR M (qr M).1 (qr M).2) (k : ℕ) : QRAlgorithmSucceeds qr μ A k :=
  fun _ _ => hqr _

/-! ### Realisation: simultaneous iteration -/

/-- `Q^{(k)}` is orthogonal. Source: Trefethen–Bau (1997) [`tb97`], Lect. 28.
atlas: qr-algorithm-simultaneous-iteration -/
theorem transpose_mul_self_qrAlgorithmQ {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k) :
    (qrAlgorithmQ qr μ A k)ᵀ * qrAlgorithmQ qr μ A k = 1 := by
  induction k with
  | zero => simp [qrAlgorithmQ]
  | succ k ih =>
    have hQ : (qrAlgorithmFactors qr μ A k).1ᵀ * (qrAlgorithmFactors qr μ A k).1 = 1 :=
      (h k (Nat.lt_succ_self k)).orth
    rw [qrAlgorithmQ, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (qrAlgorithmQ qr μ A k)ᵀ, ih (h.mono (Nat.le_succ k)), Matrix.one_mul, hQ]

/-- `R^{(k)}` is upper triangular. Source: Trefethen–Bau (1997) [`tb97`], Lect. 28.
atlas: qr-algorithm-simultaneous-iteration -/
theorem isUpperTriangular_qrAlgorithmR {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k) :
    (qrAlgorithmR qr μ A k).IsUpperTriangular := by
  induction k with
  | zero => exact Matrix.blockTriangular_one
  | succ k ih =>
    exact (h k (Nat.lt_succ_self k)).upper.mul (ih (h.mono (Nat.le_succ k)))

/-- **The QR iterates are orthogonally similar to `A`**: `A_k = Q^{(k)ᵀ} A Q^{(k)}`, for any
shifts. Source: Trefethen–Bau (1997) [`tb97`], Thm 28.3 (eq. 28.10); Golub–Van Loan (2013)
[`gvl13`], §7.3.1.
atlas: qr-algorithm-simultaneous-iteration -/
theorem qrAlgorithm_eq_transpose_mul_mul {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k) :
    qrAlgorithm qr μ A k = (qrAlgorithmQ qr μ A k)ᵀ * A * qrAlgorithmQ qr μ A k := by
  induction k with
  | zero => simp [qrAlgorithmQ]
  | succ k ih =>
    rw [qrAlgorithm_succ, add_smul_one_eq_transpose_mul_mul_of_isQR (h k (Nat.lt_succ_self k)),
      ih (h.mono (Nat.le_succ k)), qrAlgorithmQ, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

/-- `A Q^{(k)} = Q^{(k)} A_k`. Helper for `qr-algorithm-simultaneous-iteration`. -/
theorem mul_qrAlgorithmQ_eq {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k) :
    A * qrAlgorithmQ qr μ A k = qrAlgorithmQ qr μ A k * qrAlgorithm qr μ A k := by
  have hQ := transpose_mul_self_qrAlgorithmQ h
  have hQ' : qrAlgorithmQ qr μ A k * (qrAlgorithmQ qr μ A k)ᵀ = 1 := mul_eq_one_comm.mp hQ
  rw [qrAlgorithm_eq_transpose_mul_mul h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ',
    Matrix.one_mul]

/-- **Shifted simultaneous iteration**: `∏_{j<k} (A − μ_j I) = Q^{(k)} R^{(k)}` (the product of
the shifted matrices, written as the polynomial `∏_{j<k} (X − μ_j)` evaluated at `A`).
Source: Trefethen–Bau (1997) [`tb97`], Thm 28.3 and Lect. 29 (shifted form); Golub–Van Loan
(2013) [`gvl13`], §7.5.
atlas: qr-algorithm-simultaneous-iteration -/
theorem aeval_prod_eq_qrAlgorithmQ_mul_qrAlgorithmR {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k) :
    aeval A (∏ j ∈ Finset.range k, (X - C (μ j))) =
      qrAlgorithmQ qr μ A k * qrAlgorithmR qr μ A k := by
  induction k with
  | zero => simp [qrAlgorithmQ, qrAlgorithmR]
  | succ k ih =>
    have hk := h k (Nat.lt_succ_self k)
    have hk' := h.mono (Nat.le_succ k)
    rw [Finset.prod_range_succ_comm, map_mul, ih hk', map_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, ← Matrix.mul_assoc, Matrix.sub_mul,
      mul_qrAlgorithmQ_eq hk', Matrix.smul_mul, Matrix.one_mul,
      show qrAlgorithmQ qr μ A k * qrAlgorithm qr μ A k - μ k • qrAlgorithmQ qr μ A k =
        qrAlgorithmQ qr μ A k * (qrAlgorithm qr μ A k - μ k • (1 : Matrix (Fin n) (Fin n) ℝ)) by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one],
      hk.eq, qrAlgorithmQ, qrAlgorithmR]
    simp only [qrAlgorithmFactors, Matrix.mul_assoc]

/-- **The unshifted QR algorithm is simultaneous iteration**: `A^k = Q^{(k)} R^{(k)}`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 28.3 (eq. 28.9); Golub–Van Loan (2013) [`gvl13`],
§7.3.1.
atlas: qr-algorithm-simultaneous-iteration -/
theorem pow_eq_qrAlgorithmQ_mul_qrAlgorithmR {k : ℕ}
    (h : QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    A ^ k = qrAlgorithmQ qr (fun _ => 0) A k * qrAlgorithmR qr (fun _ => 0) A k := by
  rw [← aeval_prod_eq_qrAlgorithmQ_mul_qrAlgorithmR h]
  simp

/-- **`A^k = Q^{(k)} R^{(k)}` is a QR factorization of `A^k`**: the unshifted QR algorithm
computes the QR factorization of the powers of `A` (simultaneous iteration from `I`).
Source: Trefethen–Bau (1997) [`tb97`], Thm 28.3.
atlas: qr-algorithm-simultaneous-iteration -/
theorem isQR_pow_qrAlgorithm {k : ℕ} (h : QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    IsQR (A ^ k) (qrAlgorithmQ qr (fun _ => 0) A k) (qrAlgorithmR qr (fun _ => 0) A k) where
  eq := pow_eq_qrAlgorithmQ_mul_qrAlgorithmR h
  orth := transpose_mul_self_qrAlgorithmQ h
  upper := isUpperTriangular_qrAlgorithmR h

/-- **The leading columns of `Q^{(k)}` span the subspace iterates of the leading columns of `I`.**
For invertible `A` and `j ≤ n`, the first `j` columns of `Q^{(k)}` span
`S_k(A, I_{:, 1:j}) = range (A^k I_{:, 1:j})`: unshifted QR is simultaneous iteration on all
leading blocks at once. Source: Trefethen–Bau (1997) [`tb97`], Thm 28.3 and Lect. 28 (the
"simultaneous iteration" interpretation); Golub–Van Loan (2013) [`gvl13`], §7.3.1.
Proof sketch: `A^k E_j = Q^{(k)} R^{(k)} E_j = Q^{(k)}_{:, 1:j} R^{(k)}_{1:j, 1:j}`
(`pow_eq_qrAlgorithmQ_mul_qrAlgorithmR`, `R^{(k)}` upper triangular), and `R^{(k)}_{1:j, 1:j}`
is invertible because `R^{(k)}` is (`det A^k = det Q^{(k)} det R^{(k)} ≠ 0` and the leading
block of an invertible upper triangular matrix is invertible); then
`subspaceIterate_mul_of_isUnit`. Without invertibility only `⊇` holds. Difficulty 2.
atlas: qr-algorithm-simultaneous-iteration -/
theorem range_qrAlgorithmQ_castLE_eq_subspaceIterate (hA : IsUnit A.det) {k : ℕ}
    (h : QRAlgorithmSucceeds qr (fun _ => 0) A k) {j : ℕ} (hj : j ≤ n) :
    LinearMap.range ((qrAlgorithmQ qr (fun _ => 0) A k).submatrix id (Fin.castLE hj)).mulVecLin =
      subspaceIterate A ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hj)) k := by
  have hQR := isQR_pow_qrAlgorithm h
  have hdet : IsUnit (qrAlgorithmR qr (fun _ => 0) A k).det := by
    have hprod : IsUnit ((qrAlgorithmQ qr (fun _ => 0) A k).det *
        (qrAlgorithmR qr (fun _ => 0) A k).det) := by
      rw [← Matrix.det_mul, ← hQR.eq, Matrix.det_pow]
      exact hA.pow k
    exact (IsUnit.mul_iff.mp hprod).2
  have hR := hQR.isUnit_det_iff.mp hdet
  have hselect : A ^ k * (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hj) =
      (A ^ k).submatrix id (Fin.castLE hj) := by
    simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] using
      Matrix.mul_submatrix_one (Equiv.refl (Fin n)) (Fin.castLE hj) (A ^ k)
  rw [subspaceIterate, hselect]
  by_cases hj0 : j = 0
  · subst j
    simp [Matrix.range_mulVecLin]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  exact (hQR.isGradedColumnBasis hR).nested ⟨i, by omega⟩

/-! ### Structure preservation -/

/-- **Symmetry is preserved**: if `A` is symmetric then so is every `A_k`. Source:
Trefethen–Bau (1997) [`tb97`], Lect. 28; Golub–Van Loan (2013) [`gvl13`], §8.3.
atlas: qr-algorithm-simultaneous-iteration -/
theorem isHermitian_qrAlgorithm (hA : A.IsHermitian) {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k) :
    (qrAlgorithm qr μ A k).IsHermitian := by
  rw [qrAlgorithm_eq_transpose_mul_mul h]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hA

/-- If no shift is an eigenvalue (`det (A − μ_j I) ≠ 0` for `j < k`), every `R_{j+1}` has a
nonzero diagonal (`A_j − μ_j I` is orthogonally similar to `A − μ_j I`). Source: Golub–Van Loan
(2013) [`gvl13`], §7.4.2. Helper for `qr-algorithm-simultaneous-iteration`. -/
theorem qrAlgorithmFactors_snd_apply_self_ne_zero {k : ℕ} (h : QRAlgorithmSucceeds qr μ A k)
    (hμ : ∀ j < k, IsUnit (A - μ j • (1 : Matrix (Fin n) (Fin n) ℝ)).det) {j : ℕ} (hj : j < k)
    (i : Fin n) : (qrAlgorithmFactors qr μ A j).2 i i ≠ 0 := by
  have hj' : QRAlgorithmSucceeds qr μ A j := h.mono hj.le
  have hQ := transpose_mul_self_qrAlgorithmQ hj'
  set Q := qrAlgorithmQ qr μ A j
  have hsim : qrAlgorithm qr μ A j - μ j • (1 : Matrix (Fin n) (Fin n) ℝ) =
      Qᵀ * (A - μ j • (1 : Matrix (Fin n) (Fin n) ℝ)) * Q := by
    rw [qrAlgorithm_eq_transpose_mul_mul hj', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hQ]
  have hdetQ : Qᵀ.det * Q.det = 1 := by rw [← Matrix.det_mul, hQ, Matrix.det_one]
  have hdet : IsUnit (qrAlgorithm qr μ A j - μ j • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [hsim, Matrix.det_mul, Matrix.det_mul, mul_comm Qᵀ.det, mul_assoc, hdetQ, mul_one]
    exact hμ j hj
  have hqr := h j hj
  rw [hqr.eq, Matrix.det_mul] at hdet
  exact hqr.isUnit_det_iff.1 (isUnit_of_mul_isUnit_right hdet) i

/-- **Hessenberg form is preserved** when every `R_j` is invertible: if `A` is upper
Hessenberg, so is every `A_k`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 28–29; Golub–Van
Loan (2013) [`gvl13`], §7.4.2. Deviation: for an arbitrary QR routine the invertibility of the
`R_j` cannot be dropped (see `isUpperHessenberg_mul_of_isQR`); with Givens rotations it can
(`isUpperHessenberg_qrAlgorithm_givensQR`).
atlas: qr-algorithm-simultaneous-iteration -/
theorem isUpperHessenberg_qrAlgorithm (hA : IsUpperHessenberg A) {k : ℕ}
    (h : QRAlgorithmSucceeds qr μ A k)
    (hR : ∀ j < k, ∀ i, (qrAlgorithmFactors qr μ A j).2 i i ≠ 0) :
    IsUpperHessenberg (qrAlgorithm qr μ A k) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    have hk := ih (h.mono (Nat.le_succ k)) fun j hj => hR j (Nat.lt_succ_of_lt hj)
    rw [qrAlgorithm_succ]
    exact (isUpperHessenberg_mul_of_isQR (hk.sub_smul_one (μ k)) (h k (Nat.lt_succ_self k))
      (hR k (Nat.lt_succ_self k))).add_smul_one (μ k)

/-- **Symmetric tridiagonal form is preserved** when every `R_j` is invertible. Source:
Trefethen–Bau (1997) [`tb97`], Lect. 28–29; Golub–Van Loan (2013) [`gvl13`], §8.3.
atlas: qr-algorithm-simultaneous-iteration -/
theorem isTridiagonal_qrAlgorithm (hS : A.IsHermitian) (hA : IsTridiagonal A) {k : ℕ}
    (h : QRAlgorithmSucceeds qr μ A k)
    (hR : ∀ j < k, ∀ i, (qrAlgorithmFactors qr μ A j).2 i i ≠ 0) :
    IsTridiagonal (qrAlgorithm qr μ A k) :=
  (isUpperHessenberg_qrAlgorithm hA.1 h hR).isTridiagonal_of_isHermitian (isHermitian_qrAlgorithm hS h)

/-! ### The Hessenberg QR algorithm with Givens rotations -/

/-- **The Givens QR algorithm keeps Hessenberg form** with no invertibility hypothesis: if `A`
is upper Hessenberg then so is every `A_k` computed with `qr = givensQR`. Source: Golub–Van Loan
(2013) [`gvl13`], §7.4.2 (Alg. 7.4.1); Trefethen–Bau (1997) [`tb97`], Lect. 28–29.
atlas: qr-algorithm-simultaneous-iteration -/
theorem isUpperHessenberg_qrAlgorithm_givensQR (hA : IsUpperHessenberg A) (k : ℕ) :
    IsUpperHessenberg (qrAlgorithm givensQR μ A k) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    rw [qrAlgorithm_succ]
    exact (isUpperHessenberg_givensQR_snd_mul_fst (ih.sub_smul_one (μ k))).add_smul_one (μ k)

/-- **Realisation for the Givens routine**: on an upper Hessenberg `A`, every factor pair of the
Givens QR algorithm is a QR factorization, so all the identities above apply
(`A_k = Q^{(k)ᵀ} A Q^{(k)}`, `∏ (A − μ_j I) = Q^{(k)} R^{(k)}`). Source: Golub–Van Loan (2013)
[`gvl13`], §7.4.2.
atlas: qr-algorithm-simultaneous-iteration -/
theorem qrAlgorithmSucceeds_givensQR (hA : IsUpperHessenberg A) (k : ℕ) :
    QRAlgorithmSucceeds givensQR μ A k := fun j _ =>
  isQR_givensQR ((isUpperHessenberg_qrAlgorithm_givensQR hA j).sub_smul_one (μ j))

/-- **The Givens QR algorithm keeps symmetric tridiagonal form**: if `A` is symmetric
tridiagonal then so is every `A_k` computed with `qr = givensQR`. Source: Golub–Van Loan (2013)
[`gvl13`], §8.3.2–8.3.3; Trefethen–Bau (1997) [`tb97`], Lect. 28–29.
atlas: qr-algorithm-simultaneous-iteration -/
theorem isTridiagonal_qrAlgorithm_givensQR (hS : A.IsHermitian) (hA : IsTridiagonal A) (k : ℕ) :
    IsTridiagonal (qrAlgorithm givensQR μ A k) :=
  (isUpperHessenberg_qrAlgorithm_givensQR hA.1 k).isTridiagonal_of_isHermitian
    (isHermitian_qrAlgorithm hS (qrAlgorithmSucceeds_givensQR hA.1 k))

/-- A valid QR factorization of a Hessenberg matrix need not preserve Hessenberg
form after swapping the factors. The explicit rational three-by-three example
explains the nonzero-diagonal hypothesis for arbitrary QR choices in
`isUpperHessenberg_qrAlgorithm`; the realized Givens routine needs no such restriction.
This is the singular-input precision correction for `qr-algorithm-simultaneous-iteration`. -/
theorem exists_isQR_isUpperHessenberg_not_isUpperHessenberg_mul :
    ∃ A Q R : Matrix (Fin 3) (Fin 3) ℝ,
      IsQR A Q R ∧ IsUpperHessenberg A ∧ ¬ IsUpperHessenberg (R * Q) := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 1, 0; 0, 0, 2]
  let Q : Matrix (Fin 3) (Fin 3) ℝ := !![3 / 5, 0, 4 / 5; 0, 1, 0; 4 / 5, 0, -(3 / 5)]
  let R : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 8 / 5; 0, 1, 0; 0, 0, -(6 / 5)]
  have heq : A = Q * R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Q, R, Matrix.mul_apply, Fin.sum_univ_succ]
  have hQ : HasOrthonormalCols Q := by
    change Qᴴ * Q = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  have hR : R.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [R] at *
  refine ⟨A, Q, R, ⟨heq, hQ, hR⟩, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [A] at *
  · intro h
    have hbad := h 2 0 (by decide)
    norm_num [Q, R, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] at hbad

end NLAlib
