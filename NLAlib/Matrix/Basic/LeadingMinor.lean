import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Leading principal submatrices and minors

* `leadingSubmatrix A k`: the `k × k` block of `A : Matrix n n R` on the `k` smallest indices of
  the linearly ordered finite type `n`, indexed by `Fin k`. Total: for `k > card n` the rows and
  columns beyond `card n` are zero (`leadingSubmatrix_apply_of_card_le`). On `Fin m` with
  `k ≤ m` it is `A.submatrix (Fin.castLE hk) (Fin.castLE hk)` (`leadingSubmatrix_fin`).
* `leadingMinor A k = det (leadingSubmatrix A k)`, the `k`-th leading principal minor: `1` for
  `k = 0`, `det A` for `k = card n`, `0` for `k > card n`.

Golub–Van Loan 2013, §3.2 (`A(1:k, 1:k)`), §4.2.1; Horn–Johnson 2013, §0.7.1 and Thm 7.2.5
(Sylvester's criterion). The trailing minor is `leadingMinor` of the order-reversed matrix
(`Matrix/Spectral/SylvesterCriterion.lean`) and the principal minor on an arbitrary index set is
`principalMinor` (`Matrix/Inequalities/PrincipalMinorProducts.lean`).
-/

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n] {R : Type*}

/-- The **leading principal `k × k` submatrix** of `A`: the block on the `k` smallest indices of
`n` (0-based: row `i` of the block is row `(i + 1)`-th smallest index of `A`). Entries with
`i ≥ card n` or `j ≥ card n` are `0`, so the definition is total in `k`. Golub–Van Loan 2013,
§3.2. -/
def leadingSubmatrix [Zero R] (A : Matrix n n R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j =>
    if h : (i : ℕ) < Fintype.card n ∧ (j : ℕ) < Fintype.card n then
      A (monoEquivOfFin n rfl ⟨i, h.1⟩) (monoEquivOfFin n rfl ⟨j, h.2⟩)
    else 0

/-- The **`k`-th leading principal minor** `det A(1:k, 1:k)`: `1` for `k = 0`, `det A` for
`k = card n`, `0` for `k > card n` (`leadingMinor_of_card_lt`). Golub–Van Loan 2013, §4.2.1;
Horn–Johnson 2013, §0.7.1. -/
def leadingMinor [CommRing R] (A : Matrix n n R) (k : ℕ) : R :=
  (leadingSubmatrix A k).det

section Zero

variable [Zero R]

theorem leadingSubmatrix_apply (A : Matrix n n R) {k : ℕ} (i j : Fin k)
    (hi : (i : ℕ) < Fintype.card n) (hj : (j : ℕ) < Fintype.card n) :
    leadingSubmatrix A k i j = A (monoEquivOfFin n rfl ⟨i, hi⟩) (monoEquivOfFin n rfl ⟨j, hj⟩) := by
  simp [leadingSubmatrix, hi, hj]

theorem leadingSubmatrix_apply_of_card_le (A : Matrix n n R) {k : ℕ} (i j : Fin k)
    (h : Fintype.card n ≤ i ∨ Fintype.card n ≤ j) :
    leadingSubmatrix A k i j = 0 := by
  rcases h with h | h <;> simp [leadingSubmatrix, not_lt.2 h]

/-- For `k ≤ card n` the leading block is the submatrix along the `k` smallest indices. -/
theorem leadingSubmatrix_eq_submatrix (A : Matrix n n R) {k : ℕ} (hk : k ≤ Fintype.card n) :
    leadingSubmatrix A k =
      A.submatrix (fun i : Fin k => monoEquivOfFin n rfl (Fin.castLE hk i))
        (fun j : Fin k => monoEquivOfFin n rfl (Fin.castLE hk j)) := by
  ext i j
  rw [leadingSubmatrix_apply A i j (lt_of_lt_of_le i.2 hk) (lt_of_lt_of_le j.2 hk)]
  rfl

/-- On `Fin m` with `k ≤ m`, `leadingSubmatrix A k = A(0:k, 0:k)`. -/
theorem leadingSubmatrix_fin {m : ℕ} (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k ≤ m) :
    leadingSubmatrix A k = A.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
  ext i j
  have hi : (i : ℕ) < Fintype.card (Fin m) := by simpa using lt_of_lt_of_le i.2 hk
  have hj : (j : ℕ) < Fintype.card (Fin m) := by simpa using lt_of_lt_of_le j.2 hk
  rw [leadingSubmatrix_apply A i j hi hj]
  have e : monoEquivOfFin (Fin m) rfl = Fin.castOrderIso (Fintype.card_fin m) :=
    Subsingleton.elim _ _
  rw [e]
  rfl

@[simp] theorem leadingSubmatrix_transpose (A : Matrix n n R) (k : ℕ) :
    leadingSubmatrix Aᵀ k = (leadingSubmatrix A k)ᵀ := by
  ext i j
  by_cases h : (i : ℕ) < Fintype.card n ∧ (j : ℕ) < Fintype.card n
  · simp [leadingSubmatrix, h]
  · rw [not_and_or, not_lt, not_lt] at h
    simp [Matrix.transpose_apply, leadingSubmatrix_apply_of_card_le _ _ _ h,
      leadingSubmatrix_apply_of_card_le _ _ _ h.symm]

end Zero

section CommRing

variable [CommRing R]

@[simp] theorem leadingMinor_zero (A : Matrix n n R) : leadingMinor A 0 = 1 := by
  simp [leadingMinor, Matrix.det_isEmpty]

/-- Beyond the dimension the leading minor is `0` (a zero row appears). -/
theorem leadingMinor_of_card_lt (A : Matrix n n R) {k : ℕ} (hk : Fintype.card n < k) :
    leadingMinor A k = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero ⟨Fintype.card n, hk⟩ fun j =>
    leadingSubmatrix_apply_of_card_le A _ j (Or.inl le_rfl)

/-- The full leading minor is the determinant. -/
theorem leadingMinor_card (A : Matrix n n R) : leadingMinor A (Fintype.card n) = A.det := by
  rw [leadingMinor, leadingSubmatrix_eq_submatrix A le_rfl]
  have : (fun i : Fin (Fintype.card n) => monoEquivOfFin n rfl (Fin.castLE le_rfl i)) =
      (monoEquivOfFin n rfl : Fin (Fintype.card n) ≃ n) := by
    ext i; rfl
  rw [this]
  exact Matrix.det_submatrix_equiv_self _ _

/-- On `Fin m` with `k ≤ m`, the leading minor is `det A(0:k, 0:k)`. -/
theorem leadingMinor_fin {m : ℕ} (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k ≤ m) :
    leadingMinor A k = (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  rw [leadingMinor, leadingSubmatrix_fin A hk]

@[simp] theorem leadingMinor_transpose (A : Matrix n n R) (k : ℕ) :
    leadingMinor Aᵀ k = leadingMinor A k := by
  rw [leadingMinor, leadingSubmatrix_transpose, Matrix.det_transpose, leadingMinor]

end CommRing

end NLAlib
