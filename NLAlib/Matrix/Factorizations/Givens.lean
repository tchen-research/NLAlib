import NLAlib.Matrix.Factorizations.QR
/-!
# Givens rotations and the QR factorization of an upper Hessenberg matrix

* `givens i j c s`: the plane rotation acting on coordinates `i, j`, identity elsewhere, with
  `(G x)_i = c x_i + s x_j`, `(G x)_j = −s x_i + c x_j`. This is the row-rotation form
  (`G A` rotates rows `i, j`), the transpose of Golub–Van Loan's `G(i, k, θ)`. Orthogonal when
  `c² + s² = 1` (`givens_transpose_mul_self`).
* `givensCos a b`, `givensSin a b`: the rotation zeroing `b` against `a`; total, with
  `(c, s) = (1, 0)` when `a = b = 0`, so `c² + s² = 1` always. `givensRotation i j x` zeroes
  `x_j` and puts `√(x_i² + x_j²)` in position `i`.
* Shape predicates on `Fin n`: `IsUpperHessenberg H` (`H i j = 0` for `j + 1 < i`) and
  `IsTridiagonal T` (`T` and `Tᵀ` upper Hessenberg), with the closure lemmas
  Hessenberg × upper triangular and upper triangular × Hessenberg, and symmetric Hessenberg ⇒
  tridiagonal. (They are used by `NLAlib.Matrix.Factorizations.Hessenberg` and by the QR
  algorithm; they could move to a shapes file later.)
* **Hessenberg QR by `n − 1` rotations**: the recursion `givensQRState` (`H₀ = H`,
  `H_{k+1} = G_k H_k` with `G_k` the rotation in rows `k, k+1` zeroing entry `(k+1, k)`), the
  accumulated `Q_k = G_0ᵀ ⋯ G_{k−1}ᵀ` (`givensQRQ`) and `givensQR H = (Q_{n−1}, H_{n−1})`.
  `Q R = H` and `Qᵀ Q = I` hold for every `H`; `R` upper triangular needs `H` upper Hessenberg
  (`isQR_givensQR`).
* **`RQ` is again Hessenberg** (`isUpperHessenberg_mul_of_isQR`, for any QR with invertible `R`;
  `isUpperHessenberg_givensQR_snd_mul_fst` for the Givens factors with no invertibility), and
  symmetric tridiagonal when `H` is symmetric (`isTridiagonal_mul_of_isQR`,
  `isTridiagonal_givensQR_snd_mul_fst`).

The success predicate is trivial (the recursion never breaks down), so there is no
`GivensQRSucceeds`.

Sources: Golub–Van Loan 2013 [`gvl13`], §5.1.8 (Givens rotations, Alg. 5.1.3), §7.4.2
(Hessenberg QR step, Alg. 7.4.1); Trefethen–Bau 1997 [`tb97`], Lect. 10 (exercise 10.4),
Lect. 28–29.
Atlas: `givens-rotation-def`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-! ### Rotations -/

section Rotation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Givens rotation** in the `(i, j)` plane with cosine `c` and sine `s`: row `i` is
`c eᵢᵀ + s eⱼᵀ`, row `j` is `−s eᵢᵀ + c eⱼᵀ`, every other row is that of the identity. This is the
transpose of Golub–Van Loan's `G(i, j, θ)` (we apply `G` on the left to zero an entry, GVL apply
`Gᵀ`). Golub–Van Loan 2013, §5.1.8.
atlas: givens-rotation-def -/
def givens (i j : n) (c s : ℝ) : Matrix n n ℝ :=
  Matrix.of fun a b =>
    if a = i then c * (if b = i then 1 else 0) + s * (if b = j then 1 else 0)
    else if a = j then -s * (if b = i then 1 else 0) + c * (if b = j then 1 else 0)
    else if a = b then 1 else 0

/-- Split a sum over a finite type at two distinct indices (helper). -/
theorem sum_eq_add_add_sum_erase_erase {i j : n} (hij : i ≠ j) (F : n → ℝ) :
    ∑ k, F k = F i + F j + ∑ k ∈ (Finset.univ.erase i).erase j, F k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]

/-- `(G x)_i = c x_i + s x_j`. Golub–Van Loan 2013, §5.1.8. -/
theorem givens_mulVec_apply_left (i j : n) (c s : ℝ) (x : n → ℝ) :
    (givens i j c s *ᵥ x) i = c * x i + s * x j := by
  simp [givens, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul]

/-- `(G x)_j = −s x_i + c x_j`. Golub–Van Loan 2013, §5.1.8. -/
theorem givens_mulVec_apply_right {i j : n} (hij : i ≠ j) (c s : ℝ) (x : n → ℝ) :
    (givens i j c s *ᵥ x) j = -s * x i + c * x j := by
  simp [givens, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul, hij.symm]

/-- `G` fixes every coordinate other than `i, j`. Golub–Van Loan 2013, §5.1.8. -/
theorem givens_mulVec_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : ℝ)
    (x : n → ℝ) : (givens i j c s *ᵥ x) a = x a := by
  simp [givens, mulVec, dotProduct, hai, haj, ite_mul]

/-- A rotation in the `(i, j)` plane fixes every vector vanishing at `i` and `j`. -/
theorem givens_mulVec_of_apply_eq_zero {i j : n} (hij : i ≠ j) (c s : ℝ) {x : n → ℝ}
    (hi : x i = 0) (hj : x j = 0) : givens i j c s *ᵥ x = x := by
  ext a
  by_cases hai : a = i
  · subst hai; rw [givens_mulVec_apply_left, hi, hj]; ring
  by_cases haj : a = j
  · subst haj; rw [givens_mulVec_apply_right hij, hi, hj]; ring
  exact givens_mulVec_apply_of_ne hai haj c s x

/-- **A Givens rotation is orthogonal**: `GᵀG = I` when `i ≠ j` and `c² + s² = 1`.
Golub–Van Loan 2013, §5.1.8.
atlas: givens-rotation-def -/
theorem givens_transpose_mul_self {i j : n} (hij : i ≠ j) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (givens i j c s)ᵀ * givens i j c s = 1 := by
  ext a b
  rw [Matrix.mul_apply, sum_eq_add_add_sum_erase_erase hij]
  set S := (Finset.univ.erase i).erase j
  have hrest : ∑ k ∈ S, (givens i j c s)ᵀ a k * givens i j c s k b =
      if a ∈ S then (if a = b then 1 else 0) else 0 := by
    rw [← Finset.sum_ite_eq' S a (fun _ => if a = b then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkj, hk'⟩ := Finset.mem_erase.1 hk
    have hki := (Finset.mem_erase.1 hk').1
    simp only [givens, transpose_apply, of_apply, if_neg hki, if_neg hkj]
    by_cases hka : k = a <;> by_cases hkb : k = b <;> simp_all
  rw [hrest]
  simp only [S, givens, transpose_apply, of_apply, if_neg hij.symm, if_true, Matrix.one_apply,
    Finset.mem_erase, Finset.mem_univ, and_true]
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
    by_cases hbj : b = j <;> subst_vars <;> simp_all <;>
    first | nlinarith [hcs] | exact fun h => ‹¬b = _› h.symm

/-- `G Gᵀ = I` as well (square matrices). Golub–Van Loan 2013, §5.1.8. -/
theorem givens_mul_transpose_self {i j : n} (hij : i ≠ j) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    givens i j c s * (givens i j c s)ᵀ = 1 :=
  mul_eq_one_comm.mp (givens_transpose_mul_self hij hcs)

/-- The cosine of the rotation zeroing `b` against `a`: `a / √(a² + b²)`, and `1` when
`a = b = 0` (so that the rotation is always orthogonal). Golub–Van Loan 2013, Alg. 5.1.3 (up to
the sign convention, which we do not need: exact arithmetic).
atlas: givens-rotation-def -/
def givensCos (a b : ℝ) : ℝ := if a ^ 2 + b ^ 2 = 0 then 1 else a / √(a ^ 2 + b ^ 2)

/-- The sine of the rotation zeroing `b` against `a`: `b / √(a² + b²)` (`0` when `a = b = 0`).
Golub–Van Loan 2013, Alg. 5.1.3.
atlas: givens-rotation-def -/
def givensSin (a b : ℝ) : ℝ := b / √(a ^ 2 + b ^ 2)

private lemma sq_add_sq_eq_zero {a b : ℝ} (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 :=
  ⟨by nlinarith [sq_nonneg a, sq_nonneg b], by nlinarith [sq_nonneg a, sq_nonneg b]⟩

/-- `givensCos² + givensSin² = 1` for all inputs. Golub–Van Loan 2013, §5.1.8. -/
theorem givensCos_sq_add_givensSin_sq (a b : ℝ) : givensCos a b ^ 2 + givensSin a b ^ 2 = 1 := by
  unfold givensCos givensSin
  split_ifs with h
  · obtain ⟨-, rfl⟩ := sq_add_sq_eq_zero h; simp
  · have hpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_pow, div_pow, Real.sq_sqrt hpos.le, ← add_div, div_self h]

/-- The rotation in the `(i, j)` plane that zeroes `x_j` against `x_i`. Golub–Van Loan 2013,
§5.1.8.
atlas: givens-rotation-def -/
def givensRotation (i j : n) (x : n → ℝ) : Matrix n n ℝ :=
  givens i j (givensCos (x i) (x j)) (givensSin (x i) (x j))

/-- `givensRotation i j x` is orthogonal. Golub–Van Loan 2013, §5.1.8. -/
theorem givensRotation_transpose_mul_self {i j : n} (hij : i ≠ j) (x : n → ℝ) :
    (givensRotation i j x)ᵀ * givensRotation i j x = 1 :=
  givens_transpose_mul_self hij (givensCos_sq_add_givensSin_sq _ _)

/-- **A Givens rotation zeroes the chosen entry**: `(G x)_j = 0`. Golub–Van Loan 2013, §5.1.8.
atlas: givens-rotation-def -/
theorem givensRotation_mulVec_apply_right {i j : n} (hij : i ≠ j) (x : n → ℝ) :
    (givensRotation i j x *ᵥ x) j = 0 := by
  rw [givensRotation, givens_mulVec_apply_right hij]
  unfold givensCos givensSin
  split_ifs with h
  · obtain ⟨-, hb⟩ := sq_add_sq_eq_zero h; simp [hb]
  · ring

/-- The rotated pivot: `(G x)_i = √(x_i² + x_j²)`. Golub–Van Loan 2013, §5.1.8.
atlas: givens-rotation-def -/
theorem givensRotation_mulVec_apply_left (i j : n) (x : n → ℝ) :
    (givensRotation i j x *ᵥ x) i = √(x i ^ 2 + x j ^ 2) := by
  rw [givensRotation, givens_mulVec_apply_left]
  unfold givensCos givensSin
  split_ifs with h
  · obtain ⟨ha, hb⟩ := sq_add_sq_eq_zero h; simp [ha, hb]
  · have hpos : 0 < √(x i ^ 2 + x j ^ 2) :=
      Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) (Ne.symm h))
    field_simp
    rw [Real.sq_sqrt (by positivity)]

/-- A rotation leaves the other coordinates alone. Golub–Van Loan 2013, §5.1.8. -/
theorem givensRotation_mulVec_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j)
    (x y : n → ℝ) : (givensRotation i j x *ᵥ y) a = y a :=
  givens_mulVec_apply_of_ne hai haj _ _ y

end Rotation

/-! ### Hessenberg and tridiagonal shapes -/

section Shapes

variable {n : ℕ}

/-- `H` is **upper Hessenberg**: `H i j = 0` whenever `j + 1 < i` (zero below the first
subdiagonal). Golub–Van Loan 2013, §7.4; Trefethen–Bau 1997, Lect. 26.
atlas: givens-rotation-def -/
def IsUpperHessenberg (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (j : ℕ) + 1 < i → H i j = 0

/-- `T` is **tridiagonal**: `T` and `Tᵀ` are upper Hessenberg (`T i j = 0` for `|i − j| > 1`).
Golub–Van Loan 2013, §8.3; Trefethen–Bau 1997, Lect. 26.
atlas: givens-rotation-def -/
def IsTridiagonal (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperHessenberg T ∧ IsUpperHessenberg Tᵀ

/-- An upper triangular matrix is upper Hessenberg. -/
theorem isUpperHessenberg_of_isUpperTriangular {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsUpperTriangular) : IsUpperHessenberg U :=
  fun i j hij => hU (show j < i by rw [Fin.lt_def]; omega)

/-- **Hessenberg × upper triangular is Hessenberg.** Golub–Van Loan 2013, §7.4.2 (proof of
Hessenberg preservation). -/
theorem IsUpperHessenberg.mul_isUpperTriangular {H U : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (hU : U.IsUpperTriangular) : IsUpperHessenberg (H * U) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) + 1 < i
  · rw [hH i k hk, zero_mul]
  · rw [hU (show j < k by rw [Fin.lt_def]; omega), mul_zero]

/-- **Upper triangular × Hessenberg is Hessenberg.** Golub–Van Loan 2013, §7.4.2. -/
theorem IsUpperHessenberg.isUpperTriangular_mul {H U : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (hU : U.IsUpperTriangular) : IsUpperHessenberg (U * H) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < i
  · rw [hU (Fin.lt_def.2 hk), zero_mul]
  · rw [hH k j (by omega), mul_zero]

/-- **A symmetric upper Hessenberg matrix is tridiagonal.** Golub–Van Loan 2013, §8.3.1;
Trefethen–Bau 1997, Lect. 26. -/
theorem IsUpperHessenberg.isTridiagonal_of_isSymm {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (hS : H.IsSymm) : IsTridiagonal H :=
  ⟨hH, by rw [hS.eq]; exact hH⟩

/-- For a square QR, `RQ = QᵀHQ` (`R = QᵀH`). Golub–Van Loan 2013, §7.3.1 (the QR step is an
orthogonal similarity). -/
theorem IsQR.mul_eq_transpose_mul_mul {H Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR H Q R) :
    R * Q = Qᵀ * H * Q := by
  rw [h.transpose_mul_eq]

/-- **`RQ` of a Hessenberg matrix is Hessenberg**: if `H` is upper Hessenberg and `H = QR` is a
QR factorization with `R` invertible, then `RQ` is upper Hessenberg. (`Q = HR⁻¹` is
Hessenberg, and so is `R · Q`.) The invertibility of `R` cannot be dropped for an arbitrary QR
(for singular `H` the factorization is not unique and `Q` need not be Hessenberg); for the
Givens factors see `isUpperHessenberg_givensQR_snd_mul_fst`. Golub–Van Loan 2013, §7.4.2;
Trefethen–Bau 1997, Lect. 28.
atlas: givens-rotation-def -/
theorem isUpperHessenberg_mul_of_isQR {H Q R : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (h : IsQR H Q R) (hR : ∀ i, R i i ≠ 0) :
    IsUpperHessenberg (R * Q) := by
  have hdet : IsUnit R.det := h.isUnit_det_iff.2 hR
  have hQ : Q = H * R⁻¹ := by
    rw [h.eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have := R.invertibleOfIsUnitDet hdet
  have hRinv : R⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular h.upper
  rw [hQ]
  exact (hH.mul_isUpperTriangular hRinv).isUpperTriangular_mul h.upper

/-- For a square QR, `RQ = QᵀHQ` is symmetric when `H` is. Golub–Van Loan 2013, §8.3. -/
theorem isSymm_mul_of_isQR {H Q R : Matrix (Fin n) (Fin n) ℝ} (hS : H.IsSymm)
    (h : IsQR H Q R) : (R * Q).IsSymm := by
  rw [h.mul_eq_transpose_mul_mul]
  exact isSymm_transpose_mul_mul hS Q

/-- **`RQ` of a symmetric tridiagonal matrix is symmetric tridiagonal** (for a QR with
invertible `R`). Golub–Van Loan 2013, §8.3.2; Trefethen–Bau 1997, Lect. 28.
atlas: givens-rotation-def -/
theorem isTridiagonal_mul_of_isQR {H Q R : Matrix (Fin n) (Fin n) ℝ} (hS : H.IsSymm)
    (hT : IsTridiagonal H) (h : IsQR H Q R) (hR : ∀ i, R i i ≠ 0) :
    IsTridiagonal (R * Q) :=
  (isUpperHessenberg_mul_of_isQR hT.1 h hR).isTridiagonal_of_isSymm (isSymm_mul_of_isQR hS h)

end Shapes

/-! ### QR of an upper Hessenberg matrix by `n − 1` rotations -/

section HessenbergQR

variable {n : ℕ}

/-- The rotation of step `k` of Hessenberg QR applied to the current matrix `W`: the Givens
rotation in rows `k, k+1` that zeroes `W (k+1) k`; the identity when `k + 1 ≥ n`.
Golub–Van Loan 2013, Alg. 7.4.1 (Hessenberg QR step). -/
def givensQRStep (W : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : k + 1 < n then givensRotation ⟨k, by omega⟩ ⟨k + 1, h⟩ (W.col ⟨k, by omega⟩) else 1

/-- The matrix after `k` rotations: `H₀ = H`, `H_{k+1} = G_k H_k`. Golub–Van Loan 2013,
Alg. 7.4.1.
atlas: givens-rotation-def -/
def givensQRState (H : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => H
  | k + 1 => givensQRStep (givensQRState H k) k * givensQRState H k

/-- The accumulated orthogonal factor after `k` rotations: `Q₀ = I`, `Q_{k+1} = Q_k G_kᵀ`, i.e.
`Q_k = G_0ᵀ ⋯ G_{k−1}ᵀ`. Golub–Van Loan 2013, §7.4.2.
atlas: givens-rotation-def -/
def givensQRQ (H : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => givensQRQ H k * (givensQRStep (givensQRState H k) k)ᵀ

/-- **Hessenberg QR by Givens rotations**: `(Q, R) = (G_0ᵀ ⋯ G_{n−2}ᵀ, G_{n−2} ⋯ G_0 H)`, using
`n − 1` rotations. Golub–Van Loan 2013, Alg. 7.4.1, §7.4.2; Trefethen–Bau 1997, Ex. 10.4.
atlas: givens-rotation-def -/
def givensQR (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  (givensQRQ H (n - 1), givensQRState H (n - 1))

/-- Each step's rotation is orthogonal. -/
theorem givensQRStep_transpose_mul_self (W : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (givensQRStep W k)ᵀ * givensQRStep W k = 1 := by
  unfold givensQRStep
  split_ifs with h
  · exact givensRotation_transpose_mul_self (by simp [Fin.ext_iff]) _
  · simp

/-- The invariant `Q_k H_k = H` of the Givens recursion (any `H`). Golub–Van Loan 2013, §7.4.2. -/
theorem givensQRQ_mul_givensQRState (H : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    givensQRQ H k * givensQRState H k = H := by
  induction k with
  | zero => simp [givensQRQ, givensQRState]
  | succ k ih =>
    rw [givensQRQ, givensQRState, Matrix.mul_assoc, ← Matrix.mul_assoc _ (givensQRStep _ k),
      givensQRStep_transpose_mul_self, Matrix.one_mul, ih]

/-- The accumulated `Q_k` is orthogonal (any `H`). Golub–Van Loan 2013, §7.4.2. -/
theorem givensQRQ_transpose_mul_self (H : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (givensQRQ H k)ᵀ * givensQRQ H k = 1 := by
  induction k with
  | zero => simp [givensQRQ]
  | succ k ih =>
    rw [givensQRQ, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (givensQRQ H k)ᵀ, ih, Matrix.one_mul,
      mul_eq_one_comm.mp (givensQRStep_transpose_mul_self _ k)]

/-- The invariant of the Givens recursion on an upper Hessenberg `H`: after `k` rotations the
matrix is still upper Hessenberg and its first `k` subdiagonal entries vanish.
Golub–Van Loan 2013, §7.4.2. -/
theorem givensQRState_invariant {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg H)
    (k : ℕ) : IsUpperHessenberg (givensQRState H k) ∧
      ∀ i j : Fin n, (i : ℕ) = j + 1 → (j : ℕ) < k → givensQRState H k i j = 0 := by
  induction k with
  | zero => exact ⟨hH, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hk : k + 1 < n
    · set W := givensQRState H k with hWdef
      set K : Fin n := ⟨k, by omega⟩ with hK
      set K1 : Fin n := ⟨k + 1, hk⟩ with hK1
      have hKK : K ≠ K1 := by simp [hK, hK1, Fin.ext_iff]
      have happ : ∀ a b, givensQRState H (k + 1) a b =
          (givensRotation K K1 (W.col K) *ᵥ W.col b) a := by
        intro a b
        simp only [givensQRState, givensQRStep, dif_pos hk]
        rfl
      -- columns `j < k` vanish in rows `k, k+1`, hence are unchanged
      have hcol : ∀ j : Fin n, (j : ℕ) < k → ∀ a, givensQRState H (k + 1) a j = W a j := by
        intro j hj a
        rw [happ, givensRotation, givens_mulVec_of_apply_eq_zero hKK]
        · rfl
        · show W K j = 0
          by_cases hj' : (j : ℕ) + 1 < k
          · exact ih1 K j hj'
          · exact ih2 K j (by simp [hK]; omega) hj
        · exact ih1 K1 j (by simp [hK1]; omega)
      refine ⟨fun i j hij => ?_, fun i j hij hj => ?_⟩
      · by_cases hj : (j : ℕ) < k
        · rw [hcol j hj]; exact ih1 i j hij
        · rw [happ, givensRotation_mulVec_apply_of_ne (by simp [hK, Fin.ext_iff]; omega)
            (by simp [hK1, Fin.ext_iff]; omega)]
          exact ih1 i j hij
      · by_cases hjk : (j : ℕ) < k
        · rw [hcol j hjk]; exact ih2 i j hij hjk
        · obtain rfl : j = K := Fin.ext (by simp [hK]; omega)
          obtain rfl : i = K1 := Fin.ext (by simp [hK1]; omega)
          rw [happ]
          exact givensRotation_mulVec_apply_right hKK _
    · have hstep : givensQRState H (k + 1) = givensQRState H k := by
        simp only [givensQRState, givensQRStep, dif_neg hk, Matrix.one_mul]
      rw [hstep]
      exact ⟨ih1, fun i j hij _ => ih2 i j hij (by have := i.isLt; omega)⟩

/-- **The Givens recursion triangularises an upper Hessenberg matrix**: `G_{n−2} ⋯ G_0 H` is
upper triangular. Golub–Van Loan 2013, §7.4.2 (Alg. 7.4.1); Trefethen–Bau 1997, Ex. 10.4.
atlas: givens-rotation-def -/
theorem isUpperTriangular_givensQR_snd {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) : (givensQR H).2.IsUpperTriangular := by
  obtain ⟨h1, h2⟩ := givensQRState_invariant hH (n - 1)
  intro i j hij
  change j < i at hij
  have hij' := Fin.lt_def.1 hij
  by_cases h : (j : ℕ) + 1 < i
  · exact h1 i j h
  · exact h2 i j (by omega) (by have := i.isLt; omega)

/-- **Realisation: Hessenberg QR by `n − 1` Givens rotations.** For upper Hessenberg `H`,
`givensQR H` is a (square) QR factorization of `H` with `Q` the product of `n − 1` rotations.
Golub–Van Loan 2013, §7.4.2; Trefethen–Bau 1997, Ex. 10.4.
atlas: givens-rotation-def -/
theorem isQR_givensQR {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg H) :
    IsQR H (givensQR H).1 (givensQR H).2 where
  eq := (givensQRQ_mul_givensQRState H (n - 1)).symm
  orth := givensQRQ_transpose_mul_self H (n - 1)
  upper := isUpperTriangular_givensQR_snd hH

/-- SCAFFOLD: givens-rotation-def. The invariant of the accumulated Givens factor: `Q_k` is upper
Hessenberg and its columns beyond `k` are those of the identity. Golub–Van Loan 2013, §7.4.2.
Proof sketch (difficulty 2): induction on `k`; the step multiplies row-wise by the rotation in the
plane `(k, k+1)` (`givensRotation_mulVec_apply_of_ne` for the untouched columns); for rows `a` with
`a > k + 1` the two rotated entries are zero by the induction hypothesis, so
`givens_mulVec_of_apply_eq_zero` leaves the row unchanged; columns `> k + 1` are identity columns by
the second clause. A previous attempt left unsolved goals at the row case; restart from the
statement. -/
theorem givensQRQ_invariant (H : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    IsUpperHessenberg (givensQRQ H k) ∧
      ∀ a b : Fin n, k < (b : ℕ) → givensQRQ H k a b = if a = b then 1 else 0 := by
  sorry

/-- **The Givens `Q` is upper Hessenberg** (for every `H`): a product `G_0ᵀ G_1ᵀ ⋯ G_{n−2}ᵀ` of
rotations in consecutive planes `(k, k+1)` is upper Hessenberg. Golub–Van Loan 2013, §7.4.2
(proof of Hessenberg preservation of the QR step).
atlas: givens-rotation-def -/
theorem isUpperHessenberg_givensQR_fst (H : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperHessenberg (givensQR H).1 :=
  (givensQRQ_invariant H (n - 1)).1

/-- **`RQ` is again Hessenberg** for the Givens factors of an upper Hessenberg `H`, with no
invertibility hypothesis (upper triangular × Hessenberg). Golub–Van Loan 2013, §7.4.2.
atlas: givens-rotation-def -/
theorem isUpperHessenberg_givensQR_snd_mul_fst {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) : IsUpperHessenberg ((givensQR H).2 * (givensQR H).1) :=
  (isUpperHessenberg_givensQR_fst H).isUpperTriangular_mul (isUpperTriangular_givensQR_snd hH)

/-- **`RQ` is symmetric tridiagonal** for the Givens factors of a symmetric tridiagonal `H`.
Golub–Van Loan 2013, §8.3.2 (symmetric QR step); Trefethen–Bau 1997, Lect. 28.
atlas: givens-rotation-def -/
theorem isTridiagonal_givensQR_snd_mul_fst {H : Matrix (Fin n) (Fin n) ℝ} (hS : H.IsSymm)
    (hT : IsTridiagonal H) : IsTridiagonal ((givensQR H).2 * (givensQR H).1) :=
  (isUpperHessenberg_givensQR_snd_mul_fst hT.1).isTridiagonal_of_isSymm
    (isSymm_mul_of_isQR hS (isQR_givensQR hT.1))

end HessenbergQR

end NLAlib
