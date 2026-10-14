import Mathlib.LinearAlgebra.Matrix.Permutation
import NLAlib.Matrix.Basic.SchurComplement
import NLAlib.Matrix.Basic.LeadingMinor
/-!
# LU factorization and Gaussian elimination

The factorization predicate, the algorithm as a total recursion, and the realisation theorems
(`docs/ALGORITHM_CONVENTIONS.md`), in exact arithmetic.

* `IsLU A L U`: `A = L U` with `L` unit lower triangular and `U` upper triangular (any linearly
  ordered index). `IsLU.unique` (invertible `A`), `IsLU.det_eq_prod`, and the restriction to
  leading blocks `IsLU.leadingSubmatrix` (`leadingSubmatrix`, `leadingMinor` from
  `NLAlib.Matrix.Basic.LeadingMinor`). Existence, over any linearly ordered finite index:
  `exists_isLU_of_forall_leadingMinor_ne_zero` (leading minors `1, …, n − 1` nonzero) and
  `exists_isLU_iff_forall_leadingMinor_ne_zero` (invertible `A`).
* Gaussian elimination without pivoting: `lu A`, a recursion on the leading pivot through
  `pivotSchur` (the elimination step `eq_borderedMatrix_mul_borderedMatrix_pivotSchur`);
  `LUSucceeds A` (every pivot nonzero); `luSucceeds_iff_forall_leadingMinor_ne_zero`; `isLU_lu`.
* Partial pivoting: `IsPLU A σ L U` (`PA = LU` with `P = σ.permMatrix`, written
  `A.submatrix σ id`), `luPartialPivot A` (pivot on the first entry of largest modulus in the
  current column, `absArgmax`), `isPLU_luPartialPivot` with no hypothesis on `A`,
  `abs_luPartialPivot_lower_le_one` (`|lᵢⱼ| ≤ 1`), `LUPartialPivotSucceeds A ↔ IsUnit A.det`.
* Growth factor: `abs_luPartialPivot_upper_le` (`|uᵢⱼ| ≤ 2^i max|A|`) and the corollary
  `≤ 2^{n−1} max|A|` (`abs_luPartialPivot_upper_le_two_pow`).

Total recursions: a zero pivot gives junk through `x / 0 = 0`, never an error; with partial
pivoting a zero pivot means a zero column and the junk is a valid factorization.

Sources: Trefethen–Bau 1997, Lect. 20–22; Golub–Van Loan 2013, §3.2–3.4; Horn–Johnson 2013,
§3.5. Atlas: `lu-decomposition`, `lu-algorithm`, `lu-partial-pivoting`, `lu-growth-factor`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-! ### The factorization predicate -/

section Predicate

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **LU factorization**: `A = L U` with `L` unit lower triangular and `U` upper triangular.
Trefethen–Bau 1997, Lect. 20; Golub–Van Loan 2013, §3.2.
atlas: lu-decomposition -/
structure IsLU (A L U : Matrix n n ℝ) : Prop where
  /-- `L` is unit lower triangular. -/
  isUnitLowerTriangular : IsUnitLowerTriangular L
  /-- `U` is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- `A = L U`. -/
  eq_mul : A = L * U

/-- For an LU factorization, `det A = ∏ᵢ uᵢᵢ`. Golub–Van Loan 2013, §3.2. -/
theorem IsLU.det_eq_prod {A L U : Matrix n n ℝ} (h : IsLU A L U) : A.det = ∏ i, U i i := by
  rw [h.eq_mul, det_mul, h.isUnitLowerTriangular.det_eq_one, one_mul,
    det_of_isUpperTriangular h.isUpperTriangular]

/-- **Uniqueness of the LU factorization** of an invertible matrix. Proof: `L'⁻¹ L = U' U⁻¹` is
unit lower and upper triangular, hence the identity. Golub–Van Loan 2013, Thm 3.2.1;
Horn–Johnson 2013, Cor. 3.5.6; Trefethen–Bau 1997, Lect. 20.
atlas: lu-decomposition -/
theorem IsLU.unique {A L U L' U' : Matrix n n ℝ} (hA : IsUnit A.det) (h₁ : IsLU A L U)
    (h₂ : IsLU A L' U') : L = L' ∧ U = U' := by
  have hU : IsUnit U.det := by
    rwa [h₁.eq_mul, det_mul, h₁.isUnitLowerTriangular.det_eq_one, one_mul] at hA
  have hL : IsUnit L.det := by rw [h₁.isUnitLowerTriangular.det_eq_one]; exact isUnit_one
  have hL' : IsUnit L'.det := by rw [h₂.isUnitLowerTriangular.det_eq_one]; exact isUnit_one
  have hLU : L * U = L' * U' := h₁.eq_mul.symm.trans h₂.eq_mul
  have key : L'⁻¹ * L = U' * U⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * L * (U * U⁻¹) := by rw [mul_nonsing_inv U hU, Matrix.mul_one]
      _ = L'⁻¹ * (L * U) * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L'⁻¹ * (L' * U') * U⁻¹ := by rw [hLU]
      _ = U' * U⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul L' hL', Matrix.one_mul]
  have hup : (L'⁻¹ * L).IsUpperTriangular := by
    rw [key]; exact BlockTriangular.mul h₂.isUpperTriangular
      (isUpperTriangular_inv h₁.isUpperTriangular)
  have h1 : L'⁻¹ * L = 1 := eq_one_of_isUnitLowerTriangular_of_isUpperTriangular
    (h₂.isUnitLowerTriangular.inv.mul h₁.isUnitLowerTriangular) hup
  have hLL : L = L' := by
    calc L = L' * (L'⁻¹ * L) := by rw [← Matrix.mul_assoc, mul_nonsing_inv L' hL', Matrix.one_mul]
      _ = L' := by rw [h1, Matrix.mul_one]
  refine ⟨hLL, ?_⟩
  have hLU' : L * U = L * U' := by rw [hLU, hLL]
  calc U = L⁻¹ * (L * U) := by rw [← Matrix.mul_assoc, nonsing_inv_mul L hL, Matrix.one_mul]
    _ = L⁻¹ * (L * U') := by rw [hLU']
    _ = U' := by rw [← Matrix.mul_assoc, nonsing_inv_mul L hL, Matrix.one_mul]

end Predicate

/-! ### Leading principal submatrices -/

section Leading

variable {n : ℕ}

/-- Leading blocks of an LU factorization form an LU factorization of the leading block:
`A(1:k,1:k) = L(1:k,1:k) U(1:k,1:k)`, since `L` vanishes above and `U` below the diagonal.
Golub–Van Loan 2013, proof of Thm 3.2.1. -/
theorem IsLU.leadingSubmatrix {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) (k : ℕ)
    (hk : k ≤ n) :
    IsLU (leadingSubmatrix A k) (leadingSubmatrix L k) (leadingSubmatrix U k) := by
  rw [leadingSubmatrix_fin A hk, leadingSubmatrix_fin L hk, leadingSubmatrix_fin U hk]
  have hL := isLowerTriangular_iff.1 h.isUnitLowerTriangular.isLowerTriangular
  have hU := isUpperTriangular_iff.1 h.isUpperTriangular
  refine ⟨⟨isLowerTriangular_iff.2 fun i j hij => hL _ _ ((Fin.castLE_lt_castLE_iff hk).2 hij),
    fun i => h.isUnitLowerTriangular.apply_self _⟩,
    isUpperTriangular_iff.2 fun i j hij => hU _ _ ((Fin.castLE_lt_castLE_iff hk).2 hij), ?_⟩
  ext i j
  simp only [submatrix_apply, Matrix.mul_apply, h.eq_mul]
  symm
  have hmap : (∑ l : Fin k, L (Fin.castLE hk i) (Fin.castLE hk l) * U (Fin.castLE hk l)
      (Fin.castLE hk j)) = ∑ l ∈ Finset.univ.map (Fin.castLEEmb hk),
        L (Fin.castLE hk i) l * U l (Fin.castLE hk j) := by
    rw [Finset.sum_map]; rfl
  rw [hmap]
  refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
  have hkl : k ≤ (l : ℕ) := by
    by_contra hlt
    exact hl (Finset.mem_map.2 ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]

/-- For an LU factorization the leading principal minors are the partial products of the
pivots: `det A(1:k,1:k) = ∏_{i<k} uᵢᵢ`. Golub–Van Loan 2013, proof of Thm 3.2.1. -/
theorem IsLU.leadingMinor_eq_prod {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) (k : ℕ)
    (hk : k ≤ n) :
    leadingMinor A k = ∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) := by
  have := (h.leadingSubmatrix k hk).det_eq_prod
  rwa [leadingSubmatrix_fin U hk] at this

/-- The pivot Schur complement commutes with taking leading blocks:
`pivotSchur (A(1:k+1, 1:k+1)) = (pivotSchur A)(1:k, 1:k)`. -/
theorem pivotSchur_leadingSubmatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {k : ℕ}
    (hk : k + 1 ≤ n + 1) :
    pivotSchur (leadingSubmatrix A (k + 1)) = leadingSubmatrix (pivotSchur A) k := by
  rw [leadingSubmatrix_fin A hk, leadingSubmatrix_fin (pivotSchur A) (Nat.le_of_succ_le_succ hk)]
  have h0 : Fin.castLE hk 0 = 0 := rfl
  have hs : ∀ i : Fin k, Fin.castLE hk i.succ = (Fin.castLE (Nat.le_of_succ_le_succ hk) i).succ :=
    fun i => rfl
  ext i j
  simp [h0, hs]

/-- The `1 × 1` leading minor is the pivot. -/
theorem leadingMinor_one (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    leadingMinor A 1 = A 0 0 := by
  rw [leadingMinor_fin A (Nat.succ_le_succ (Nat.zero_le n)), det_fin_one]; rfl

/-- A first-pivot Schur step factors every larger leading minor by the pivot:
`det A(1:k+1,1:k+1) = a₁₁ · det (pivotSchur A)(1:k,1:k)`. Horn–Johnson 2013, proof of
Thm 7.2.5; Golub–Van Loan 2013, Thm 3.2.1 (proof). -/
theorem leadingMinor_succ_eq_mul_leadingMinor_pivotSchur
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ha : A 0 0 ≠ 0) {k : ℕ} (hk : k + 1 ≤ n + 1) :
    leadingMinor A (k + 1) = A 0 0 * leadingMinor (pivotSchur A) k := by
  rw [leadingMinor, leadingMinor, ← pivotSchur_leadingSubmatrix A hk, leadingSubmatrix_fin A hk]
  exact det_eq_mul_det_pivotSchur _ ha

end Leading

/-! ### Gaussian elimination without pivoting -/

section Algorithm

/-- **Gaussian elimination without pivoting** (Doolittle LU) as a total recursion on the
leading pivot: with `A = [[a, rᵀ], [c, C]]`, `L = [[1, 0], [c/a, L']]`,
`U = [[a, rᵀ], [0, U']]` where `(L', U') = lu (C − c rᵀ/a)`. A zero pivot gives junk through
`x / 0 = 0`. For `n = 0` the output is `(1, A)` (both are the empty matrix).
Trefethen–Bau 1997, Alg. 20.1; Golub–Van Loan 2013, Alg. 3.2.1 (outer-product form).
atlas: lu-algorithm -/
def lu : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  | 0, A => (1, A)
  | _ + 1, A =>
    (borderedMatrix 1 0 ((A 0 0)⁻¹ • fun i => A i.succ 0) (lu (pivotSchur A)).1,
      borderedMatrix (A 0 0) (fun j => A 0 j.succ) 0 (lu (pivotSchur A)).2)

/-- **Success of Gaussian elimination**: every pivot (the `(1,1)` entry of `A` and of each
successive Schur complement) is nonzero. All `n` pivots are required, so success also gives an
invertible `U`; the realisation `A = LU` itself only uses the first `n − 1` (see
`exists_isLU_of_forall_det_ne_zero`). Trefethen–Bau 1997, Lect. 20; Golub–Van Loan 2013, §3.2.
atlas: lu-algorithm -/
def LUSucceeds : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → Prop
  | 0, _ => True
  | _ + 1, A => A 0 0 ≠ 0 ∧ LUSucceeds (pivotSchur A)

/-- The `L` factor of `lu` is unit lower triangular, with no hypothesis on `A`.
Trefethen–Bau 1997, Alg. 20.1. -/
theorem isUnitLowerTriangular_lu_fst {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUnitLowerTriangular (lu A).1 := by
  induction n with
  | zero => exact isUnitLowerTriangular_one
  | succ n ih =>
    have h := ih (pivotSchur A)
    refine ⟨isLowerTriangular_borderedMatrix_iff.2 ⟨rfl, h.isLowerTriangular⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [lu]
    · simpa [lu] using h.apply_self i

/-- The `U` factor of `lu` is upper triangular, with no hypothesis on `A`.
Trefethen–Bau 1997, Alg. 20.1. -/
theorem isUpperTriangular_lu_snd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (lu A).2.IsUpperTriangular := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    exact isUpperTriangular_borderedMatrix_iff.2 ⟨rfl, ih (pivotSchur A)⟩

/-- The pivots are the diagonal of `U`: elimination succeeds iff `(lu A).2` has nonzero
diagonal. Trefethen–Bau 1997, Lect. 20. -/
theorem luSucceeds_iff_forall_lu_snd_apply_self_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : LUSucceeds A ↔ ∀ i, (lu A).2 i i ≠ 0 := by
  induction n with
  | zero => simp [LUSucceeds]
  | succ n ih =>
    rw [LUSucceeds, ih, Fin.forall_fin_succ]
    simp [lu]

/-- **Realisation of Gaussian elimination**: if every pivot is nonzero, `lu` returns an LU
factorization. Proof: induction on `n`; the step is
`eq_borderedMatrix_mul_borderedMatrix_pivotSchur` with the factorization of the Schur
complement in the trailing blocks. Trefethen–Bau 1997, Alg. 20.1; Golub–Van Loan 2013,
Alg. 3.2.1.
atlas: lu-algorithm -/
theorem isLU_lu {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (h : LUSucceeds A) :
    IsLU A (lu A).1 (lu A).2 := by
  induction n with
  | zero =>
    exact ⟨isUnitLowerTriangular_lu_fst A, isUpperTriangular_lu_snd A, by ext i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨ha, hS⟩ := h
    have hLU := (ih hS).eq_mul
    refine ⟨isUnitLowerTriangular_lu_fst A, isUpperTriangular_lu_snd A, ?_⟩
    simp only [lu]
    rw [borderedMatrix_mul_borderedMatrix, ← hLU]
    conv_lhs => rw [← borderedMatrix_eta A]
    congr 1
    · simp
    · ext j; simp
    · ext i; simp [ha]
    · ext i j; simp [pivotSchur, vecMulVec_apply]

/-- **Breakdown of Gaussian elimination**: elimination without pivoting succeeds iff every
leading principal minor `det A(1:k,1:k)`, `k = 1, …, n`, is nonzero. Proof: induction on `n`
with `det A(1:k+1,1:k+1) = a₁₁ det (pivotSchur A)(1:k,1:k)` (`det_eq_mul_det_pivotSchur`,
`leadingMinor_succ_eq_mul_leadingMinor_pivotSchur`); the case `k = 1` gives `a₁₁ ≠ 0`.
Trefethen–Bau 1997, Lect. 20 (Ex. 20.1); Golub–Van Loan 2013, Thm 3.2.1.
atlas: lu-algorithm -/
theorem luSucceeds_iff_forall_leadingMinor_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    LUSucceeds A ↔ ∀ k ≤ n, leadingMinor A k ≠ 0 := by
  induction n with
  | zero =>
    simp only [LUSucceeds, true_iff]
    intro k hk
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    rw [LUSucceeds, ih]
    constructor
    · rintro ⟨ha, hS⟩ k hk
      rcases k with _ | k
      · simp
      · rw [leadingMinor_succ_eq_mul_leadingMinor_pivotSchur A ha hk]
        exact mul_ne_zero ha (hS k (Nat.le_of_succ_le_succ hk))
    · intro h
      have ha : A 0 0 ≠ 0 := by
        have := h 1 (Nat.succ_le_succ (Nat.zero_le n))
        rwa [leadingMinor_one] at this
      refine ⟨ha, fun k hk => ?_⟩
      have := h (k + 1) (Nat.succ_le_succ hk)
      rw [leadingMinor_succ_eq_mul_leadingMinor_pivotSchur A ha (Nat.succ_le_succ hk)] at this
      exact right_ne_zero_of_mul this

/-- **Realisation of Gaussian elimination under the minimal hypothesis**: if the leading
principal minors of orders `1, …, n − 1` are nonzero, `lu A` is an LU factorization (the last
pivot is never divided by, so `det A` may vanish). Proof: induction on `n`; the `1 × 1` case is
trivial, otherwise the pivot is `det A(1:1,1:1) ≠ 0` and the Schur complement inherits the
hypothesis through `leadingMinor_succ_eq_mul_leadingMinor_pivotSchur`.
Golub–Van Loan 2013, Thm 3.2.1; Trefethen–Bau 1997, Alg. 20.1.
atlas: lu-algorithm -/
theorem isLU_lu_of_forall_leadingMinor_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ k < n, leadingMinor A k ≠ 0) :
    IsLU A (lu A).1 (lu A).2 := by
  induction n with
  | zero =>
    exact ⟨isUnitLowerTriangular_lu_fst A, isUpperTriangular_lu_snd A, by ext i; exact i.elim0⟩
  | succ n ih =>
    refine ⟨isUnitLowerTriangular_lu_fst A, isUpperTriangular_lu_snd A, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext i j
      obtain rfl : i = 0 := Fin.ext (by omega)
      obtain rfl : j = 0 := Fin.ext (by omega)
      simp [lu, Matrix.mul_apply]
    · have ha : A 0 0 ≠ 0 := by
        have := h 1 (by omega)
        rwa [leadingMinor_one] at this
      have hS : ∀ k < n, leadingMinor (pivotSchur A) k ≠ 0 := by
        intro k hk
        have := h (k + 1) (by omega)
        rw [leadingMinor_succ_eq_mul_leadingMinor_pivotSchur A ha (by omega)] at this
        exact right_ne_zero_of_mul this
      have hLU := (ih hS).eq_mul
      simp only [lu]
      rw [borderedMatrix_mul_borderedMatrix, ← hLU]
      conv_lhs => rw [← borderedMatrix_eta A]
      congr 1
      · simp
      · ext j; simp
      · ext i; simp [ha]
      · ext i j; simp [pivotSchur, vecMulVec_apply]

end Algorithm

/-! ### Existence over any linearly ordered index -/

section Existence

variable {m n : Type*} [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]

/-- An LU factorization transports along an order isomorphism of the index type. -/
theorem IsLU.submatrix {A L U : Matrix n n ℝ} (h : IsLU A L U) (e : m ≃o n) :
    IsLU (A.submatrix e e) (L.submatrix e e) (U.submatrix e e) where
  isUnitLowerTriangular :=
    ⟨isLowerTriangular_iff.2 fun _ _ hij =>
        isLowerTriangular_iff.1 h.isUnitLowerTriangular.isLowerTriangular _ _ (e.strictMono hij),
      fun i => h.isUnitLowerTriangular.apply_self (e i)⟩
  isUpperTriangular := isUpperTriangular_iff.2 fun _ _ hij =>
    isUpperTriangular_iff.1 h.isUpperTriangular _ _ (e.strictMono hij)
  eq_mul := by rw [h.eq_mul]; exact (Matrix.submatrix_mul_equiv L U e e.toEquiv e).symm

/-- The leading minors of `A` are those of its reindexing along the sorting isomorphism
`Fin (card n) ≃o n`. -/
theorem leadingMinor_submatrix_monoEquivOfFin (A : Matrix n n ℝ) (k : ℕ) :
    leadingMinor (A.submatrix (monoEquivOfFin n rfl) (monoEquivOfFin n rfl)) k =
      leadingMinor A k := by
  unfold leadingMinor
  congr 1
  ext i j
  by_cases h : (i : ℕ) < Fintype.card n ∧ (j : ℕ) < Fintype.card n
  · have hi' : (i : ℕ) < Fintype.card (Fin (Fintype.card n)) := by simpa using h.1
    have hj' : (j : ℕ) < Fintype.card (Fin (Fintype.card n)) := by simpa using h.2
    rw [leadingSubmatrix_apply _ i j hi' hj', leadingSubmatrix_apply A i j h.1 h.2]
    have e : monoEquivOfFin (Fin (Fintype.card n)) rfl =
        Fin.castOrderIso (Fintype.card_fin _) := Subsingleton.elim _ _
    rw [e]
    rfl
  · have h' : Fintype.card (Fin (Fintype.card n)) ≤ i ∨ Fintype.card (Fin (Fintype.card n)) ≤ j := by
      rw [not_and_or, not_lt, not_lt] at h; simpa using h
    rw [not_and_or, not_lt, not_lt] at h
    rw [leadingSubmatrix_apply_of_card_le _ _ _ h', leadingSubmatrix_apply_of_card_le _ _ _ h]

/-- **Existence of LU** when the leading principal minors of orders `1, …, n − 1` are nonzero (no
condition on `det A` itself), on any linearly ordered finite index; on `Fin n` the witness is
`lu A` (`isLU_lu_of_forall_leadingMinor_ne_zero`). Golub–Van Loan 2013, Thm 3.2.1;
Horn–Johnson 2013, Cor. 3.5.6.
atlas: lu-decomposition -/
theorem exists_isLU_of_forall_leadingMinor_ne_zero (A : Matrix n n ℝ)
    (h : ∀ k < Fintype.card n, leadingMinor A k ≠ 0) : ∃ L U, IsLU A L U := by
  let e := monoEquivOfFin n rfl
  have h' : ∀ k < Fintype.card n, leadingMinor (A.submatrix e e) k ≠ 0 := fun k hk => by
    rw [leadingMinor_submatrix_monoEquivOfFin]; exact h k hk
  have hLU := (isLU_lu_of_forall_leadingMinor_ne_zero h').submatrix e.symm
  have hA : (A.submatrix e e).submatrix e.symm e.symm = A := by ext i j; simp
  rw [hA] at hLU
  exact ⟨_, _, hLU⟩

/-- **Existence of LU for invertible matrices**: an invertible `A` has an LU factorization iff
all its leading principal minors are nonzero (and it is then unique, `IsLU.unique`).
Trefethen–Bau 1997, Lect. 20; Golub–Van Loan 2013, Thm 3.2.1; Horn–Johnson 2013, Cor. 3.5.6.
atlas: lu-decomposition -/
theorem exists_isLU_iff_forall_leadingMinor_ne_zero {A : Matrix n n ℝ} (hA : IsUnit A.det) :
    (∃ L U, IsLU A L U) ↔ ∀ k ≤ Fintype.card n, leadingMinor A k ≠ 0 := by
  constructor
  · rintro ⟨L, U, h⟩ k hk
    have hd : ∀ i, U i i ≠ 0 := by
      intro i hi
      rw [h.det_eq_prod, Finset.prod_eq_zero (f := fun j => U j j) (Finset.mem_univ i) hi] at hA
      exact not_isUnit_zero hA
    rw [← leadingMinor_submatrix_monoEquivOfFin,
      (h.submatrix (monoEquivOfFin n rfl)).leadingMinor_eq_prod k hk]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd _
  · intro h
    exact exists_isLU_of_forall_leadingMinor_ne_zero A fun k hk => h k hk.le

end Existence

/-! ### Partial pivoting -/

section PartialPivoting

/-- **LU with row permutation**: `P A = L U` with `P = σ.permMatrix ℝ`, written as
`A.submatrix σ id = L U` (row `i` of `PA` is row `σ i` of `A`; `Matrix.toMatrix_toPEquiv_mul`
converts). Trefethen–Bau 1997, Lect. 21; Golub–Van Loan 2013, §3.4.
atlas: lu-partial-pivoting -/
def IsPLU {n : Type*} [Fintype n] [LinearOrder n] (A : Matrix n n ℝ) (σ : Equiv.Perm n)
    (L U : Matrix n n ℝ) : Prop :=
  IsLU (A.submatrix σ id) L U

/-- The permutation-matrix form of `IsPLU`: `P A = L U` with `P = σ.permMatrix ℝ`. -/
theorem IsPLU.permMatrix_mul_eq {n : Type*} [Fintype n] [LinearOrder n] {A L U : Matrix n n ℝ}
    {σ : Equiv.Perm n} (h : IsPLU A σ L U) : Equiv.Perm.permMatrix ℝ σ * A = L * U := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]; exact h.eq_mul

/-- The first index of an entry of largest modulus (`argmaxᵢ |vᵢ|`, ties to the smallest index),
as a recursion; the pivot search of partial pivoting. Golub–Van Loan 2013, Alg. 3.4.1. -/
def absArgmax : {n : ℕ} → (Fin (n + 1) → ℝ) → Fin (n + 1)
  | 0, _ => 0
  | _ + 1, v =>
    if |v (absArgmax fun i => v i.succ).succ| ≤ |v 0| then 0 else (absArgmax fun i => v i.succ).succ

/-- `absArgmax v` maximises `|vᵢ|`. -/
theorem abs_le_abs_absArgmax {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    |v i| ≤ |v (absArgmax v)| := by
  induction n with
  | zero =>
    rw [show i = absArgmax v from Fin.ext (by have := i.isLt; have := (absArgmax v).isLt; omega)]
  | succ n ih =>
    have h := ih (fun i => v i.succ)
    simp only [absArgmax]
    split_ifs with hk
    · exact Fin.cases le_rfl (fun i => (h i).trans hk) i
    · exact Fin.cases (not_le.1 hk).le (fun i => h i) i

/-- The row swap of partial pivoting: exchange row `0` with the row of an entry of largest
modulus in column `0`. Golub–Van Loan 2013, Alg. 3.4.1. -/
def partialPivotSwap {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  A.submatrix (Equiv.swap 0 (absArgmax fun i => A i 0)) id

/-- After the partial-pivoting swap the pivot dominates its column. -/
theorem abs_partialPivotSwap_le {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) : |partialPivotSwap A i 0| ≤ |partialPivotSwap A 0 0| := by
  simp only [partialPivotSwap, submatrix_apply, id, Equiv.swap_apply_left]
  exact abs_le_abs_absArgmax (fun i => A i 0) _

/-- Rows of `A` permuted by `decomposeFin⁻¹ (p, τ)` (row `p` first, then the rows of the swapped
matrix in the order `τ`), as a bordered matrix. -/
theorem submatrix_decomposeFin_symm {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    A.submatrix (Equiv.Perm.decomposeFin.symm (p, τ)) id =
      borderedMatrix (A p 0) (fun j => A p j.succ) (fun i => A (Equiv.swap 0 p (τ i).succ) 0)
        (fun i j => A (Equiv.swap 0 p (τ i).succ) j.succ) := by
  conv_lhs => rw [← borderedMatrix_eta (A.submatrix _ id)]
  congr 1
  · simp
  · ext j; simp
  · ext i; simp
  · ext i j; simp

/-- **Gaussian elimination with partial pivoting** as a total recursion. With
`B = partialPivotSwap A = [[a, rᵀ], [c, C]]` and `(σ', L', U') = luPartialPivot (C − c rᵀ/a)`,
the output is `σ = decomposeFin⁻¹ (p, σ')` (row `p` first, then the rows of `B` in the order
`σ'`), `L = [[1, 0], [σ'(c/a), L']]` (multipliers permuted by the later swaps, as in the
textbook's "swap the rows of `L` too"), `U = [[a, rᵀ], [0, U']]`.
Trefethen–Bau 1997, Alg. 21.1; Golub–Van Loan 2013, Alg. 3.4.1.
atlas: lu-partial-pivoting -/
def luPartialPivot : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ →
    Equiv.Perm (Fin n) × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  | 0, A => (1, 1, A)
  | _ + 1, A =>
    (Equiv.Perm.decomposeFin.symm
        (absArgmax (fun i => A i 0), (luPartialPivot (pivotSchur (partialPivotSwap A))).1),
      borderedMatrix 1 0
        (fun i => (partialPivotSwap A 0 0)⁻¹ *
          partialPivotSwap A ((luPartialPivot (pivotSchur (partialPivotSwap A))).1 i).succ 0)
        (luPartialPivot (pivotSchur (partialPivotSwap A))).2.1,
      borderedMatrix (partialPivotSwap A 0 0) (fun j => partialPivotSwap A 0 j.succ) 0
        (luPartialPivot (pivotSchur (partialPivotSwap A))).2.2)

/-- **Success of partial pivoting**: every pivot (after the row swap) is nonzero.
Golub–Van Loan 2013, §3.4.
atlas: lu-partial-pivoting -/
def LUPartialPivotSucceeds : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → Prop
  | 0, _ => True
  | _ + 1, A =>
    partialPivotSwap A 0 0 ≠ 0 ∧ LUPartialPivotSucceeds (pivotSchur (partialPivotSwap A))

/-- **Realisation of partial pivoting**, for every square `A` (no invertibility hypothesis):
`luPartialPivot A` is a factorization `PA = LU`. When the pivot is zero the whole column is
zero and the junk multipliers `0⁻¹ · 0 = 0` give a valid step. Proof: induction on `n`, the step
is the elimination identity for `partialPivotSwap A` conjugated by the permutation of the
trailing rows. Trefethen–Bau 1997, Lect. 21; Golub–Van Loan 2013, Thm 3.4.1 (existence for
singular `A` as in the atlas note).
atlas: lu-partial-pivoting -/
theorem isPLU_luPartialPivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsPLU A (luPartialPivot A).1 (luPartialPivot A).2.1 (luPartialPivot A).2.2 := by
  induction n with
  | zero =>
    exact ⟨isUnitLowerTriangular_one, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨⟨hL1, hL2⟩, hU, hLU⟩ := ih (pivotSchur (partialPivotSwap A))
    have hcol : partialPivotSwap A 0 0 = 0 → ∀ i, partialPivotSwap A i 0 = 0 := fun h0 i =>
      abs_nonpos_iff.1 ((abs_partialPivotSwap_le A i).trans (by rw [h0, abs_zero]))
    refine ⟨⟨isLowerTriangular_borderedMatrix_iff.2 ⟨rfl, hL1⟩, fun i => ?_⟩,
      isUpperTriangular_borderedMatrix_iff.2 ⟨rfl, hU⟩, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [luPartialPivot]
      · simpa [luPartialPivot] using hL2 i
    · simp only [luPartialPivot]
      rw [submatrix_decomposeFin_symm, borderedMatrix_mul_borderedMatrix, ← hLU]
      congr 1
      · simp [partialPivotSwap]
      · ext j; simp [partialPivotSwap]
      · ext i
        have hc := hcol
        simp only [partialPivotSwap, submatrix_apply, id, Equiv.swap_apply_left] at hc ⊢
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_zero, Pi.zero_apply, add_zero]
        by_cases h0 : A (absArgmax fun i => A i 0) 0 = 0
        · rw [h0, hc h0]; simp
        · field_simp
      · ext i j
        simp [partialPivotSwap, pivotSchur, vecMulVec_apply]
        ring

/-- **Bounded multipliers**: partial pivoting gives `|lᵢⱼ| ≤ 1`, for every `A`.
Trefethen–Bau 1997, Lect. 21; Golub–Van Loan 2013, §3.4.
atlas: lu-partial-pivoting -/
theorem abs_luPartialPivot_lower_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |(luPartialPivot A).2.1 i j| ≤ 1 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [luPartialPivot]
    · simp [luPartialPivot]
    · simp only [luPartialPivot, borderedMatrix_succ_zero, abs_mul, abs_inv]
      by_cases h0 : partialPivotSwap A 0 0 = 0
      · simp [h0]
      · rw [inv_mul_le_one₀ (abs_pos.2 h0)]
        exact abs_partialPivotSwap_le A _
    · simpa [luPartialPivot] using ih (pivotSchur (partialPivotSwap A)) i j

/-- Partial pivoting succeeds iff `A` is invertible. Proof: `det A = ± ∏ᵢ uᵢᵢ` from
`isPLU_luPartialPivot` (`Matrix.det_permute`), and the pivots are the diagonal of `U`.
Trefethen–Bau 1997, Lect. 21; Golub–Van Loan 2013, Thm 3.4.1.
atlas: lu-partial-pivoting -/
theorem luPartialPivotSucceeds_iff_isUnit_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    LUPartialPivotSucceeds A ↔ IsUnit A.det := by
  have hdiag : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ),
      LUPartialPivotSucceeds A ↔ ∀ i, (luPartialPivot A).2.2 i i ≠ 0 := by
    intro m A
    induction m with
    | zero => simp [LUPartialPivotSucceeds]
    | succ m ih =>
      rw [LUPartialPivotSucceeds, ih, Fin.forall_fin_succ]
      simp [luPartialPivot]
  have hdet := (isPLU_luPartialPivot A).det_eq_prod
  rw [det_permute] at hdet
  rw [hdiag, isUnit_iff_ne_zero]
  constructor
  · intro h hA
    rw [hA, mul_zero, eq_comm] at hdet
    exact Finset.prod_ne_zero_iff.2 (fun i _ => h i) hdet
  · intro hA i hi
    rw [Finset.prod_eq_zero (f := fun j => (luPartialPivot A).2.2 j j) (Finset.mem_univ i) hi]
      at hdet
    rcases Int.units_eq_one_or (Equiv.Perm.sign (luPartialPivot A).1) with hs | hs <;>
      simp [hs, hA] at hdet

/-- Every square matrix has a factorization `PA = LU` with `|lᵢⱼ| ≤ 1`.
Trefethen–Bau 1997, Lect. 21; Golub–Van Loan 2013, Thm 3.4.1.
atlas: lu-partial-pivoting -/
theorem exists_isPLU_abs_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ σ L U, IsPLU A σ L U ∧ ∀ i j, |L i j| ≤ 1 :=
  ⟨_, _, _, isPLU_luPartialPivot A, abs_luPartialPivot_lower_le_one A⟩

/-- **Growth bound for partial pivoting, row form**: if `|aᵢⱼ| ≤ M` for all entries then row
`i` of `U` satisfies `|uᵢⱼ| ≤ 2^i M` (each elimination step at most doubles the entries, since
the multipliers are bounded by one). Trefethen–Bau 1997, Lect. 22; Higham 2002, §9.3,
eq. (9.13) (Wilkinson's bound). Exact arithmetic.
atlas: lu-growth-factor (partial) -/
theorem abs_luPartialPivot_upper_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {M : ℝ}
    (hM : ∀ i j, |A i j| ≤ M) (i j : Fin n) :
    |(luPartialPivot A).2.2 i j| ≤ 2 ^ (i : ℕ) * M := by
  induction n generalizing M with
  | zero => exact i.elim0
  | succ n ih =>
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
    have hB : ∀ i j, |partialPivotSwap A i j| ≤ M := fun i j => hM _ _
    have hS : ∀ i j, |pivotSchur (partialPivotSwap A) i j| ≤ 2 * M := by
      intro i j
      rw [pivotSchur_apply, two_mul]
      refine (abs_sub _ _).trans (add_le_add (hB _ _) ?_)
      rw [← mul_assoc, abs_mul]
      by_cases h0 : partialPivotSwap A 0 0 = 0
      · simp [h0, hM0]
      · have hl : |(partialPivotSwap A 0 0)⁻¹ * partialPivotSwap A i.succ 0| ≤ 1 := by
          rw [abs_mul, abs_inv, inv_mul_le_one₀ (abs_pos.2 h0)]
          exact abs_partialPivotSwap_le A _
        calc _ ≤ 1 * M := mul_le_mul hl (hB _ _) (abs_nonneg _) zero_le_one
          _ = M := one_mul M
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [luPartialPivot] using hB 0 0
    · simpa [luPartialPivot] using hB 0 j.succ
    · simp only [luPartialPivot, borderedMatrix_succ_zero, Pi.zero_apply, abs_zero]
      positivity
    · have := ih hS i j
      simp only [luPartialPivot, borderedMatrix_succ_succ, Fin.val_succ, pow_succ]
      linarith

/-- **Growth factor of partial pivoting**: `max |uᵢⱼ| ≤ 2^{n−1} max |aᵢⱼ|`, stated with an
entrywise bound `M` on `A`. The bound is attained (Wilkinson's example), which is not
formalized. Trefethen–Bau 1997, Lect. 22, eq. (22.4); Higham 2002, §9.3, eq. (9.13).
atlas: lu-growth-factor (partial) -/
theorem abs_luPartialPivot_upper_le_two_pow {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {M : ℝ}
    (hM : ∀ i j, |A i j| ≤ M) (i j : Fin n) :
    |(luPartialPivot A).2.2 i j| ≤ 2 ^ (n - 1) * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM i i)
  refine (abs_luPartialPivot_upper_le hM i j).trans ?_
  gcongr
  · norm_num
  · omega

end PartialPivoting

end NLAlib
