import NLAlib.Matrix.Factorizations.QR
import NLAlib.Matrix.Norms.Core
/-!
# Householder reflectors and Householder QR

* `householder v = I − (2 / vᵀv) v vᵀ` (and `I` for `v = 0`, by `2 / 0 = 0`): symmetric
  (`householder_transpose`), involutive (`householder_mul_self`), orthogonal
  (`householder_transpose_mul_self`), `H v = −v` (`householder_mulVec_self`), `H` fixes `v^⊥`
  (`householder_mulVec_of_dotProduct_eq_zero`).
* The Trefethen–Bau vector `householderVector x i₀ = x + sign(x_{i₀}) ‖x‖ e_{i₀}` (with
  `sign 0 = 1`, `householderSign`), which avoids cancellation, and
  `householder_mulVec_householderVector : H x = −sign(x_{i₀}) ‖x‖ e_{i₀}`.
* **Householder QR** as a total recursion on `Fin m × Fin n` (`householderQR`): reflect the
  first column onto `e₀`, recurse on the trailing block. It returns the list of reflector
  vectors (padded with leading zeros to length `m`) and `R`; `householderQ A` is the product
  `H₁ H₂ ⋯ H_k` of the reflectors (`k = min m n`, `length_householderQR_fst`).
  The realisation theorem `isFullQR_householderQR` has **no rank or shape hypothesis**; the thin
  QR for `n ≤ m` is `isQR_householderQR`.

The recursion never breaks down (`x / 0 = 0` makes a zero column reflect by the identity), so
there is no success predicate. Unlike Trefethen–Bau Alg. 10.1 the recursion stores `R` directly
(first row of `H₁A`, then zeros below the pivot, then the recursive `R`), rather than
overwriting `A` in place; the subdiagonal zeros are put in by construction and the realisation
theorem says this is exact.

Sources: Trefethen–Bau 1997 [`tb97`], Lect. 10 (Alg. 10.1, eq. (10.5)); Golub–Van Loan 2013
[`gvl13`], §5.1.2–5.1.3, Alg. 5.2.1.
Atlas: `householder-reflector-def`, `householder-qr`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

/-- `‖x‖₂ = √(x ⬝ x)` for real vectors (proof helper; the squared bridge is
`norm_toLp_sq_eq_dotProduct_self`). -/
private theorem norm_toLp_eq_sqrt_dotProduct_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ = √(x ⬝ᵥ x) := by
  rw [← norm_toLp_sq_eq_dotProduct_self, Real.sqrt_sq (norm_nonneg _)]

/-! ### Reflectors -/

section Reflector

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The **Householder reflector** `H_v = I − (2 / vᵀv) v vᵀ`. For `v = 0` it is the identity
(`2 / 0 = 0` in Lean; Trefethen–Bau set `H_0 = I` by convention as well).
Trefethen–Bau 1997, Lect. 10, eq. (10.4); Golub–Van Loan 2013, §5.1.2.
atlas: householder-reflector-def -/
def householder (v : m → ℝ) : Matrix m m ℝ := 1 - (2 / (v ⬝ᵥ v)) • vecMulVec v v

/-- `H_0 = I`. Trefethen–Bau 1997, Lect. 10. -/
@[simp]
theorem householder_zero : householder (0 : m → ℝ) = 1 := by
  simp [householder]

/-- `H_v x = x − (2 vᵀx / ‖v‖²) v`. Trefethen–Bau 1997, Lect. 10. -/
theorem householder_mulVec (v x : m → ℝ) :
    householder v *ᵥ x = x - (2 * (v ⬝ᵥ x) / ‖(WithLp.toLp 2 v : EuclideanSpace ℝ m)‖ ^ 2) • v := by
  rw [norm_toLp_sq_eq_dotProduct_self, householder, sub_mulVec, one_mulVec, smul_mulVec,
    vecMulVec_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    smul_eq_mul]
  ring

/-- `H_v` is symmetric. Trefethen–Bau 1997, Lect. 10; Golub–Van Loan 2013, §5.1.2.
atlas: householder-reflector-def -/
theorem householder_transpose (v : m → ℝ) : (householder v)ᵀ = householder v := by
  rw [householder, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

private lemma two_div_sq_mul (t : ℝ) : (2 / t) * (2 / t) * t = 2 * (2 / t) := by
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

/-- `H_v` is an involution, `H_v² = I`. Trefethen–Bau 1997, Lect. 10; Golub–Van Loan 2013,
§5.1.2.
atlas: householder-reflector-def -/
theorem householder_mul_self (v : m → ℝ) : householder v * householder v = 1 := by
  set c := 2 / (v ⬝ᵥ v)
  have hP : vecMulVec v v * vecMulVec v v = (v ⬝ᵥ v) • vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hc : c * c * (v ⬝ᵥ v) = 2 * c := two_div_sq_mul _
  rw [householder, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, smul_smul, hc]
  module

/-- `H_v` is orthogonal, `H_vᵀ H_v = I`. Trefethen–Bau 1997, Lect. 10; Golub–Van Loan 2013,
§5.1.2.
atlas: householder-reflector-def -/
theorem householder_transpose_mul_self (v : m → ℝ) :
    (householder v)ᵀ * householder v = 1 := by
  rw [householder_transpose, householder_mul_self]

/-- `H_v` has orthonormal columns. Trefethen–Bau 1997, Lect. 10.
atlas: householder-reflector-def -/
theorem hasOrthonormalCols_householder (v : m → ℝ) : HasOrthonormalCols (householder v) :=
  householder_transpose_mul_self v

/-- `H_v v = −v`. Trefethen–Bau 1997, Lect. 10; Golub–Van Loan 2013, §5.1.2.
atlas: householder-reflector-def -/
theorem householder_mulVec_self (v : m → ℝ) : householder v *ᵥ v = -v := by
  rw [householder_mulVec, norm_toLp_sq_eq_dotProduct_self]
  by_cases hv : v ⬝ᵥ v = 0
  · rw [dotProduct_self_eq_zero.1 hv]; simp
  · rw [mul_div_assoc, div_self hv, mul_one, two_smul]; abel

/-- `H_v` fixes the hyperplane `v^⊥`. Trefethen–Bau 1997, Lect. 10; Golub–Van Loan 2013,
§5.1.2.
atlas: householder-reflector-def -/
theorem householder_mulVec_of_dotProduct_eq_zero {v w : m → ℝ} (h : v ⬝ᵥ w = 0) :
    householder v *ᵥ w = w := by
  rw [householder_mulVec, h]; simp

/-- The sign used by Trefethen–Bau: `sign t = 1` for `t ≥ 0` and `−1` for `t < 0` (so
`sign 0 = 1`). Trefethen–Bau 1997, Lect. 10, eq. (10.5).
atlas: householder-reflector-def -/
def householderSign (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

/-- `sign t ^ 2 = 1`. -/
theorem householderSign_sq (t : ℝ) : householderSign t ^ 2 = 1 := by
  unfold householderSign; split_ifs <;> norm_num

/-- `sign t * t = |t|`. -/
theorem householderSign_mul_self (t : ℝ) : householderSign t * t = |t| := by
  unfold householderSign; split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.1 h)]; ring

/-- The **Trefethen–Bau Householder vector** `v = x + sign(x_{i₀}) ‖x‖ e_{i₀}`, whose reflector
maps `x` to `−sign(x_{i₀}) ‖x‖ e_{i₀}` (`householder_mulVec_householderVector`). The sign avoids
cancellation (both signs give valid reflectors in exact arithmetic). Trefethen–Bau 1997,
Lect. 10, eq. (10.5); Golub–Van Loan 2013, Alg. 5.1.1 (with the other sign convention).
atlas: householder-reflector-def -/
def householderVector (x : m → ℝ) (i₀ : m) : m → ℝ :=
  x + (householderSign (x i₀) * √(x ⬝ᵥ x)) • Pi.single i₀ 1

/-- **The reflector maps `x` onto the axis**: `H_v x = −sign(x_{i₀}) ‖x‖ e_{i₀}` for the
Trefethen–Bau vector `v = householderVector x i₀`. No hypothesis (for `x = 0`, `v = 0`).
Trefethen–Bau 1997, Lect. 10 (eq. (10.5) and Fig. 10.2); Golub–Van Loan 2013, §5.1.2.
atlas: householder-reflector-def -/
theorem householder_mulVec_householderVector (x : m → ℝ) (i₀ : m) :
    householder (householderVector x i₀) *ᵥ x =
      (-(householderSign (x i₀) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖)) • Pi.single i₀ 1 := by
  rw [norm_toLp_eq_sqrt_dotProduct_self]
  set σ := householderSign (x i₀)
  set ν := √(x ⬝ᵥ x)
  set v := householderVector x i₀
  have hν : ν ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dotProduct_self_nonneg x)
  have hσ : σ ^ 2 = 1 := householderSign_sq _
  have hvx : v ⬝ᵥ x = x ⬝ᵥ x + σ * ν * x i₀ := by
    simp only [v, householderVector, add_dotProduct, smul_dotProduct, single_dotProduct,
      smul_eq_mul, one_mul, σ, ν]
  have hvv : v ⬝ᵥ v = 2 * (v ⬝ᵥ x) := by
    have e : v = x + (σ * ν) • Pi.single i₀ 1 := rfl
    have ha : (σ * ν) * (σ * ν) = x ⬝ᵥ x := by rw [← hν, ← mul_one (ν ^ 2), ← hσ]; ring
    rw [hvx, e]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      single_dotProduct, dotProduct_single, smul_eq_mul, one_mul, mul_one, Pi.add_apply,
      Pi.smul_apply, Pi.single_eq_same]
    linear_combination ha
  rw [householder_mulVec, norm_toLp_sq_eq_dotProduct_self]
  by_cases h0 : v ⬝ᵥ x = 0
  · have hv0 : v = 0 := dotProduct_self_eq_zero.1 (by rw [hvv, h0, mul_zero])
    have hx : x = (-(σ * ν)) • Pi.single i₀ 1 := by
      have : x + (σ * ν) • Pi.single i₀ (1 : ℝ) = 0 := hv0
      rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, this]
    rw [h0, mul_zero, zero_div, zero_smul, sub_zero]
    exact hx
  · rw [hvv, div_self (by simpa using h0), one_smul]
    simp only [v, householderVector, neg_smul]
    abel

end Reflector

/-! ### Householder QR -/

section QR

variable {m n : ℕ}

/-- A reflector padded with a leading zero is `diag(1, H_w)`. Trefethen–Bau 1997, Lect. 10
(eq. (10.3): `Q_k = [[I, 0], [0, F]]`). -/
theorem householder_vecCons_zero (w : Fin m → ℝ) :
    householder (vecCons 0 w) = borderedUpper (vecCons 1 0) (householder w) := by
  ext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [householder]
    | succ j => simp [householder, (Fin.succ_ne_zero j).symm]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [householder]
    | succ j => simp [householder, vecMulVec_apply, Matrix.one_apply]

/-- **Householder QR** as a total recursion (Trefethen–Bau Alg. 10.1). On `A : (m+1) × (n+1)`:
`v = householderVector (A e₀) 0`, `B = H_v A`; recurse on the trailing block `B(1:, 1:)`; return
the reflector vectors `v, (0, v₂), (0, 0, v₃), …` (padded to length `m`) and
`R = [[B(0, :)], [0, R']]`. With no rows or no columns, no reflector and `R = A`. Exactly
`min m n` reflectors are produced (`length_householderQR_fst`; for `m = n` the last one is a
`1 × 1` sign flip, as in Trefethen–Bau). Trefethen–Bau 1997, Alg. 10.1; Golub–Van Loan 2013,
Alg. 5.2.1.
atlas: householder-qr -/
def householderQR : {m n : ℕ} → Matrix (Fin m) (Fin n) ℝ →
    List (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ
  | 0, _, A => ([], A)
  | _ + 1, 0, A => ([], A)
  | _ + 1, _ + 1, A =>
    let v := householderVector (A.col 0) 0
    let B := householder v * A
    let rest := householderQR (B.submatrix Fin.succ Fin.succ)
    (v :: rest.1.map (vecCons 0), borderedUpper (B 0) rest.2)

/-- The orthogonal factor of Householder QR: the product `H₁ H₂ ⋯ H_k` of the reflectors.
Trefethen–Bau 1997, Lect. 10, eq. (10.2) and Alg. 10.3 (implicit `Q`).
atlas: householder-qr -/
def householderQ (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ((householderQR A).1.map householder).prod

/-- The triangular factor of Householder QR. Trefethen–Bau 1997, Alg. 10.1.
atlas: householder-qr -/
def householderR (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  (householderQR A).2

/-- Householder QR uses `min m n` reflectors. Trefethen–Bau 1997, Alg. 10.1. -/
theorem length_householderQR_fst (A : Matrix (Fin m) (Fin n) ℝ) :
    (householderQR A).1.length = min m n := by
  induction m generalizing n with
  | zero => simp [householderQR]
  | succ m ih =>
    cases n with
    | zero => simp [householderQR]
    | succ n => simp [householderQR, ih, Nat.succ_min_succ]

/-- A product of matrices with orthonormal columns (square, so orthogonal) is orthogonal. -/
theorem hasOrthonormalCols_list_prod {k : Type*} [Fintype k] [DecidableEq k]
    (l : List (Matrix k k ℝ)) (hl : ∀ M ∈ l, HasOrthonormalCols M) :
    HasOrthonormalCols l.prod := by
  induction l with
  | nil => simp [HasOrthonormalCols]
  | cons M l ih =>
    have hM : Mᵀ * M = 1 := by
      have h := (hl M List.mem_cons_self).conjTranspose_mul_self
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have hl' : l.prodᵀ * l.prod = 1 := by
      have h := (ih fun N hN => hl N (List.mem_cons_of_mem _ hN)).conjTranspose_mul_self
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial, List.prod_cons,
      Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM, Matrix.one_mul, hl']

/-- The Householder `Q` is orthogonal (no hypothesis). Trefethen–Bau 1997, Lect. 10.
atlas: householder-qr -/
theorem hasOrthonormalCols_householderQ (A : Matrix (Fin m) (Fin n) ℝ) :
    HasOrthonormalCols (householderQ A) :=
  hasOrthonormalCols_list_prod _ fun M hM => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hM
    exact hasOrthonormalCols_householder v

/-- `QᵀQ = I` for the Householder `Q` (proof-helper form of `hasOrthonormalCols_householderQ`). -/
theorem householderQ_transpose_mul_self (A : Matrix (Fin m) (Fin n) ℝ) :
    (householderQ A)ᵀ * householderQ A = 1 := by
  have h := (hasOrthonormalCols_householderQ A).conjTranspose_mul_self
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The Householder `R` is upper trapezoidal (no hypothesis). Trefethen–Bau 1997, Alg. 10.1.
atlas: householder-qr -/
theorem isUpperTrapezoidal_householderR (A : Matrix (Fin m) (Fin n) ℝ) :
    IsUpperTrapezoidal (householderR A) := by
  induction m generalizing n with
  | zero => exact fun i => i.elim0
  | succ m ih =>
    cases n with
    | zero => exact fun _ j => j.elim0
    | succ n => exact isUpperTrapezoidal_borderedUpper _ (ih _)

/-- Padding every reflector vector with a leading zero turns the product of reflectors into
`diag(1, ∏ H_w)`. Trefethen–Bau 1997, Lect. 10, eq. (10.3). -/
theorem prod_map_householder_map_vecCons_zero (l : List (Fin m → ℝ)) :
    ((l.map (vecCons 0)).map householder).prod =
      borderedUpper (vecCons 1 0) ((l.map householder).prod) := by
  induction l with
  | nil => simp [borderedUpper_one_one]
  | cons w l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, ih, householder_vecCons_zero,
      borderedUpper_one_mul_borderedUpper, List.map_cons, List.prod_cons]

/-- One step of the recursion for `Q`: `Q(A) = H_v · diag(1, Q(B'))` with `B' = (H_v A)(1:, 1:)`.
Trefethen–Bau 1997, Lect. 10, eq. (10.2). -/
theorem householderQ_succ_succ (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) :
    householderQ A = householder (householderVector (A.col 0) 0) *
      borderedUpper (vecCons 1 0) (householderQ
        ((householder (householderVector (A.col 0) 0) * A).submatrix Fin.succ Fin.succ)) := by
  rw [householderQ, householderQR, List.map_cons, List.prod_cons,
    prod_map_householder_map_vecCons_zero]
  rfl

/-- **Realisation of Householder QR**: `(householderQ A, householderR A)` is a full QR of every
real `m × n` matrix, with `Q` the product of `min m n` reflectors; no rank or shape
hypothesis (unlike Gram–Schmidt). Trefethen–Bau 1997, Lect. 10, Alg. 10.1 and Thm 7.1
(existence via Householder); Golub–Van Loan 2013, Alg. 5.2.1. Proof: induction on `m`, each
step being `isFullQR_mul_borderedUpper` with `W = H_v` (symmetric, orthogonal), whose first
column condition is `householder_mulVec_householderVector`.
atlas: householder-qr -/
theorem isFullQR_householderQR : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
    IsFullQR A (householderQ A) (householderR A)
  | 0, _, A => ⟨by simp [householderQ, householderR, householderQR],
      householderQ_transpose_mul_self A, isUpperTrapezoidal_householderR A⟩
  | _ + 1, 0, A => ⟨by simp [householderQ, householderR, householderQR],
      householderQ_transpose_mul_self A, isUpperTrapezoidal_householderR A⟩
  | m + 1, n + 1, A => by
    set H := householder (householderVector (A.col 0) 0) with hHdef
    have hW : HasOrthonormalCols H := hasOrthonormalCols_householder _
    have hB : ∀ i : Fin m, (Hᵀ * A) i.succ 0 = 0 := by
      intro i
      rw [hHdef, householder_transpose]
      have := congrFun (householder_mulVec_householderVector (A.col 0) 0) i.succ
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero] at this
      exact this
    have key := isFullQR_mul_borderedUpper hW hB
      (isFullQR_householderQR ((Hᵀ * A).submatrix Fin.succ Fin.succ))
    rw [hHdef, householder_transpose] at key
    rw [householderQ_succ_succ]
    exact key

/-- **`QR = A` for Householder QR**, for every `A`. Trefethen–Bau 1997, Lect. 10
(eq. (10.1)–(10.2)); Golub–Van Loan 2013, §5.2.2.
atlas: householder-qr -/
theorem householderQ_mul_householderR (A : Matrix (Fin m) (Fin n) ℝ) :
    householderQ A * householderR A = A :=
  (isFullQR_householderQR A).eq.symm

/-- **Thin QR from Householder** (`n ≤ m`): the first `n` columns of the Householder `Q` and the
first `n` rows of `R`. Trefethen–Bau 1997, Lect. 10; Golub–Van Loan 2013, §5.2.2.
atlas: householder-qr -/
theorem isQR_householderQR (A : Matrix (Fin m) (Fin n) ℝ) (hnm : n ≤ m) :
    IsQR A ((householderQ A).submatrix id (Fin.castLE hnm))
      ((householderR A).submatrix (Fin.castLE hnm) id) :=
  (isFullQR_householderQR A).isQR_castLE hnm

end QR

end NLAlib
