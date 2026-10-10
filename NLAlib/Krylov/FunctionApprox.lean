import Mathlib.LinearAlgebra.Lagrange
import NLAlib.Krylov.GaussQuadrature
import NLAlib.Polynomial.Approximation

/-!
# Matrix functions by Krylov compression: `f(A) b ≈ Q f(QᵀAQ) Qᵀ b`

For a matrix `Q` with orthonormal columns whose range contains the Krylov space `K_q(A, b)` and
the compression `T = Qᵀ A Q`, the Krylov (Lanczos-FA) approximation of `f(A) b` is
`krylovFunApprox Q A f b = Q f(T) Qᵀ b` (`f(T) = cfc f T`). Three faces
(`docs/KRYLOV_DEFINITIONS.md` §3.7, §3.9):

* **Exactness on polynomials** (`mulVec_aeval_transpose_mul_mul_mulVec_eq`,
  `transpose_mulVec_aeval_mulVec_eq`, `krylovFunApprox_eval_eq_aeval`): `Q p(T) Qᵀ b = p(A) b`
  for `deg p < q` (any `A`), and `Qᵀ p(A) b = p(T) Qᵀ b` for `deg p ≤ q`.
* **Interpolation at the Ritz values** (`krylovFunApprox_eq_aeval_of_forall_eval_eq`,
  `krylovFunApprox_eq_aeval_interpolate`): `Q f(T) Qᵀ b = p(A) b` for the Lagrange interpolant `p`
  of `f` at the eigenvalues of `T`.
* **Error bound** (`dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le`):
  `‖f(A) b − Q f(T) Qᵀ b‖² ≤ (2E)² ‖b‖²` when `|f − p| ≤ E` on an interval containing the
  spectrum of `A`, for some `p` with `deg p < q`; the case `f = 1/x` with the Chebyshev rate is
  `dotProduct_cfc_inv_mulVec_sub_krylovFunApprox_self_le`.

The approximation depends only on `range Q` (`krylovFunApprox_congr`).

Matrix-calculus helpers proved here for want of a better home (they belong in
`NLAlib.Matrix.PolynomialCalculus`): `cfc_eq_aeval_of_forall_eval_eq` (a matrix function is the
polynomial calculus of any polynomial agreeing with `f` on the eigenvalues) and
`dotProduct_cfc_mulVec_self_le` (the `cfc` form of `polynomial-spectral-bound`).

Source: Saad (1992) [`saad92`], Lemma 3.1, Thm 3.3, Thm 3.4; Druskin–Knizhnerman (1989) [`dk89`];
Higham (2008) [`higham08`], §13.2. Atlas: `krylov-polynomial-exactness`, `lanczos-fa-error`.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k : Type*} [Fintype k] [DecidableEq k]

/-! ### Matrix functions are interpolating polynomials -/

/-- A matrix function of a symmetric `A` equals the polynomial calculus of any polynomial that
agrees with `f` at the eigenvalues: `f(A) = p(A)` when `p(λᵢ) = f(λᵢ)` for all `i`.
Standard (Higham 2008 [`higham08`], Def. 1.4 and Thm 1.12). Atlas: `lanczos-fa-error` (helper;
belongs in `NLAlib.Matrix.PolynomialCalculus`). -/
theorem cfc_eq_aeval_of_forall_eval_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ}
    {p : ℝ[X]} (h : ∀ i, p.eval (hA.eigenvalues i) = f (hA.eigenvalues i)) :
    cfc f A = aeval A p := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint]
  refine cfc_congr fun x hx => ?_
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (h i).symm

/-- The Lagrange interpolant at the distinct eigenvalues takes the value `f(λᵢ)` at `λᵢ`. -/
private lemma eval_interpolate_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (i : n) :
    (Lagrange.interpolate (Finset.univ.image hA.eigenvalues) id f).eval (hA.eigenvalues i) =
      f (hA.eigenvalues i) :=
  Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _)
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- `f(A)` is `p(A)` for the Lagrange interpolant `p` of `f` at the (distinct) eigenvalues of the
symmetric `A`. Standard (Higham 2008 [`higham08`], Def. 1.4). Atlas: `lanczos-fa-error`
(helper; belongs in `NLAlib.Matrix.PolynomialCalculus`). -/
theorem cfc_eq_aeval_interpolate {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = aeval A (Lagrange.interpolate (Finset.univ.image hA.eigenvalues) id f) :=
  cfc_eq_aeval_of_forall_eval_eq hA (eval_interpolate_eigenvalues hA f)

/-- **Spectral bound, `cfc` form.** If every eigenvalue of the symmetric `A` lies in `S` and
`|g| ≤ M` on `S`, then `‖g(A) v‖² ≤ M² ‖v‖²`. The `cfc` form of
`dotProduct_aeval_mulVec_self_le` (Saad 2003, §6.11). Atlas: `lanczos-fa-error` (helper; the
`cfc` form of `polynomial-spectral-bound`). -/
theorem dotProduct_cfc_mulVec_self_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {g : ℝ → ℝ}
    {S : Set ℝ} {M : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ S) (hg : ∀ x ∈ S, |g x| ≤ M)
    (v : n → ℝ) : (cfc g A *ᵥ v) ⬝ᵥ (cfc g A *ᵥ v) ≤ M ^ 2 * (v ⬝ᵥ v) := by
  rw [cfc_eq_aeval_interpolate hA g]
  refine dotProduct_aeval_mulVec_self_le hA (S := Set.range hA.eigenvalues) (fun i => ⟨i, rfl⟩)
    ?_ v
  rintro _ ⟨i, rfl⟩
  rw [eval_interpolate_eigenvalues hA g]
  exact hg _ (hspec i)

/-- `‖(f(A) − p(A)) v‖² ≤ E² ‖v‖²` when `|f − p| ≤ E` at the eigenvalues of the symmetric `A`. -/
private lemma dotProduct_cfc_sub_aeval_mulVec_self_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {p : ℝ[X]} {E : ℝ}
    (hfp : ∀ i, |f (hA.eigenvalues i) - p.eval (hA.eigenvalues i)| ≤ E) (v : n → ℝ) :
    ((cfc f A - aeval A p) *ᵥ v) ⬝ᵥ ((cfc f A - aeval A p) *ᵥ v) ≤ E ^ 2 * (v ⬝ᵥ v) := by
  set r := Lagrange.interpolate (Finset.univ.image hA.eigenvalues) id f
  rw [cfc_eq_aeval_interpolate hA f, ← map_sub]
  refine dotProduct_aeval_mulVec_self_le hA (S := Set.range hA.eigenvalues) (fun i => ⟨i, rfl⟩)
    ?_ v
  rintro _ ⟨i, rfl⟩
  rw [eval_sub, eval_interpolate_eigenvalues hA f]
  exact hfp i

/-! ### The approximant and its exactness on polynomials -/

/-- The Krylov (Lanczos-FA) approximation of `f(A) b` from a basis matrix `Q`:
`Q f(QᵀAQ) Qᵀ b`, with `f(QᵀAQ) = cfc f (Qᵀ * A * Q)`. With the Lanczos basis, `Qᵀ b = ‖b‖ e₁`
and this is `‖b‖ Q f(T_q) e₁`. Source: Saad (1992) [`saad92`], eq. (3.2); Higham (2008)
[`higham08`], §13.2. Deviation: any `Q` (the theorems assume orthonormal columns and
`K_q(A,b) ⊆ range Q`). Atlas: `lanczos-fa-error` (definition). -/
def krylovFunApprox (Q : Matrix n k ℝ) (A : Matrix n n ℝ) (f : ℝ → ℝ) (b : n → ℝ) : n → ℝ :=
  Q *ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b))

/-- Compressed powers act like powers on `Qᵀ b` up to degree `q`: if `K_q(A,b) ⊆ range Q` and
`j ≤ q` then `Qᵀ Aʲ b = (QᵀAQ)ʲ Qᵀ b`. Source: Saad (1992) [`saad92`], Lemma 3.1.
Atlas: `krylov-polynomial-exactness` (helper). -/
theorem transpose_mulVec_pow_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {j : ℕ} (hj : j ≤ q) :
    Qᵀ *ᵥ (A ^ j *ᵥ b) = (Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmem := hK (pow_mulVec_mem_krylovSpace A b (show j < q by omega))
    calc Qᵀ *ᵥ (A ^ (j + 1) *ᵥ b) = Qᵀ *ᵥ (A *ᵥ (A ^ j *ᵥ b)) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec]
      _ = Qᵀ *ᵥ (A *ᵥ (Q *ᵥ (Qᵀ *ᵥ (A ^ j *ᵥ b)))) := by
          rw [mulVec_transpose_mulVec_of_mem_range hQ hmem]
      _ = (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ (A ^ j *ᵥ b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (Qᵀ * A * Q) *ᵥ ((Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b)) := by rw [ih (by omega)]
      _ = (Qᵀ * A * Q) ^ (j + 1) *ᵥ (Qᵀ *ᵥ b) := by rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- **Krylov projection is exact on polynomials of degree `< q`.** If `Q` has orthonormal
columns and `K_q(A,b) ⊆ range Q`, then `Q p(QᵀAQ) Qᵀ b = p(A) b` for every `p` with
`deg p < q`, for any square `A`. Source: Saad (1992) [`saad92`], Lemma 3.1; Trefethen–Bau
(1997) [`tb97`], Thm 34.1 (Arnoldi form).
atlas: krylov-polynomial-exactness (partial) -/
theorem mulVec_aeval_transpose_mul_mul_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {p : ℝ[X]} (hp : p.degree < q) :
    Q *ᵥ (aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) = aeval A p *ᵥ b := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hnat : p.natDegree < q := (natDegree_lt_iff_degree_lt hp0).2 hp
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.sum_mulVec,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
    mulVec_pow_transpose_mul_mul_mulVec_eq hQ b hK
      (lt_of_le_of_lt (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hnat)]

/-- **Compression commutes with polynomials of degree `≤ q`.** If `Q` has orthonormal columns
and `K_q(A,b) ⊆ range Q`, then `Qᵀ p(A) b = p(QᵀAQ) Qᵀ b` for every `p` with `deg p ≤ q`, for
any square `A`. Source: Saad (1992) [`saad92`], Lemma 3.1.
atlas: krylov-polynomial-exactness (partial) -/
theorem transpose_mulVec_aeval_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {p : ℝ[X]} (hp : p.degree ≤ q) :
    Qᵀ *ᵥ (aeval A p *ᵥ b) = aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hnat : p.natDegree ≤ q := (natDegree_le_iff_degree_le).2 hp
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.sum_mulVec,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
    transpose_mulVec_pow_mulVec_eq hQ b hK
      ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)).trans hnat)]

/-- **Lanczos-FA is exact on polynomials.** For symmetric `A`, `Q` with orthonormal columns and
`K_q(A,b) ⊆ range Q`, `krylovFunApprox Q A p b = p(A) b` for every `p` with `deg p < q`.
Source: Saad (1992) [`saad92`], Lemma 3.1.
Deviation: the matrix-function form needs `A` symmetric (so that `QᵀAQ` is self-adjoint and
`cfc` is the polynomial calculus); `mulVec_aeval_transpose_mul_mul_mulVec_eq` is the form for
any `A`.
atlas: krylov-polynomial-exactness (partial) -/
theorem krylovFunApprox_eval_eq_aeval {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {p : ℝ[X]} (hp : p.degree < q) :
    krylovFunApprox Q A (fun x => p.eval x) b = aeval A p *ᵥ b := by
  rw [krylovFunApprox, cfc_polynomial p _ (isHermitian_transpose_mul_mul hA Q).isSelfAdjoint]
  exact mulVec_aeval_transpose_mul_mul_mulVec_eq hQ b hK hp

/-! ### Interpolation at the Ritz values -/

/-- **Lanczos-FA interpolates at the Ritz values (general form).** If `p` has `deg p < q` and
agrees with `f` at the eigenvalues of `T = QᵀAQ` (the Ritz values), then
`krylovFunApprox Q A f b = p(A) b`. Source: Saad (1992) [`saad92`], Thm 3.3.
Deviation: any orthonormal `Q` with `K_q(A,b) ⊆ range Q`; Lagrange (not Hermite)
interpolation, the agreement being only required at the Ritz values.
Atlas: proposed id `lanczos-fa-interpolation`; uses `krylov-polynomial-exactness`.
atlas: lanczos-fa-interpolation -/
theorem krylovFunApprox_eq_aeval_of_forall_eval_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {f : ℝ → ℝ} {p : ℝ[X]}
    (hp : p.degree < q)
    (hpf : ∀ j, p.eval ((isHermitian_transpose_mul_mul hA Q).eigenvalues j) =
      f ((isHermitian_transpose_mul_mul hA Q).eigenvalues j)) :
    krylovFunApprox Q A f b = aeval A p *ᵥ b := by
  rw [krylovFunApprox, cfc_eq_aeval_of_forall_eval_eq _ hpf]
  exact mulVec_aeval_transpose_mul_mul_mulVec_eq hQ b hK hp

/-- **Lanczos-FA is the interpolant at the Ritz values.** If `Q` has at most `q` columns, then
`krylovFunApprox Q A f b = p(A) b` for the Lagrange interpolant `p` of `f` at the distinct
eigenvalues of `QᵀAQ`. Source: Saad (1992) [`saad92`], Thm 3.3.
Deviation: `Q` is any orthonormal matrix with at most `q` columns and `K_q(A,b) ⊆ range Q` (the
source takes the Lanczos basis, `range Q = K_q`); the Ritz values are interpolated without
multiplicity (Lagrange, not Hermite), which suffices because `f(T)` only sees `f` on `spec T`.
Atlas: proposed id `lanczos-fa-interpolation`; uses `krylov-polynomial-exactness`.
atlas: lanczos-fa-interpolation -/
theorem krylovFunApprox_eq_aeval_interpolate {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) (hk : Fintype.card k ≤ q)
    (f : ℝ → ℝ) :
    krylovFunApprox Q A f b =
      aeval A (Lagrange.interpolate
        (Finset.univ.image (isHermitian_transpose_mul_mul hA Q).eigenvalues) id f) *ᵥ b := by
  refine krylovFunApprox_eq_aeval_of_forall_eval_eq hA hQ b hK ?_
    (eval_interpolate_eigenvalues _ f)
  refine (Lagrange.degree_interpolate_lt f (Set.injOn_id _)).trans_le ?_
  exact_mod_cast Finset.card_image_le.trans (by simpa using hk)

/-! ### Dependence on the range only -/

omit [DecidableEq k] in
/-- `Q p(QᵀAQ) Qᵀ = p(QQᵀA) QQᵀ` for any `Q` and polynomial `p`. -/
private lemma mul_aeval_transpose_mul_mul_mul_transpose (A : Matrix n n ℝ) (Q : Matrix n k ℝ)
    [DecidableEq k] (p : ℝ[X]) :
    Q * aeval (Qᵀ * A * Q) p * Qᵀ = aeval (Q * Qᵀ * A) p * (Q * Qᵀ) := by
  have hpow : ∀ j : ℕ, Q * (Qᵀ * A * Q) ^ j * Qᵀ = (Q * Qᵀ * A) ^ j * (Q * Qᵀ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', pow_succ', Matrix.mul_assoc (Q * Qᵀ * A), ← ih]
      simp only [Matrix.mul_assoc]
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hpow]

/-- **Lanczos-FA depends only on the range of `Q`.** If `Q` and `Q'` have orthonormal columns
and the same range, then `Q f(QᵀAQ) Qᵀ b = Q' f(Q'ᵀAQ') Q'ᵀ b` (for `Q' = QU` with `U`
orthogonal, `f(UᵀTU) = Uᵀ f(T) U`). Source: `docs/KRYLOV_DEFINITIONS.md` §3.9; Saad (1992)
[`saad92`], §3 (basis-independence of the Krylov projection).
Deviation: `A` symmetric (for nonsymmetric `A` the real `cfc` is not the matrix function).
Atlas: `lanczos-fa-error` (helper: basis independence of the approximant). -/
theorem krylovFunApprox_congr {A : Matrix n n ℝ} (hA : A.IsHermitian) {k' : Type*} [Fintype k']
    [DecidableEq k'] {Q : Matrix n k ℝ} {Q' : Matrix n k' ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q')
    (hR : LinearMap.range Q.mulVecLin = LinearMap.range Q'.mulVecLin) (f : ℝ → ℝ) (b : n → ℝ) :
    krylovFunApprox Q A f b = krylovFunApprox Q' A f b := by
  set hT := isHermitian_transpose_mul_mul hA Q
  set hT' := isHermitian_transpose_mul_mul hA Q'
  set s := Finset.univ.image hT.eigenvalues ∪ Finset.univ.image hT'.eigenvalues
  set p := Lagrange.interpolate s id f
  have hnode : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
  have h1 : cfc f (Qᵀ * A * Q) = aeval (Qᵀ * A * Q) p := cfc_eq_aeval_of_forall_eval_eq hT
    fun i => hnode _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : cfc f (Q'ᵀ * A * Q') = aeval (Q'ᵀ * A * Q') p := cfc_eq_aeval_of_forall_eval_eq hT'
    fun i => hnode _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hP := mul_transpose_eq_of_range_eq hQ hQ' hR
  simp only [krylovFunApprox, Matrix.mulVec_mulVec, h1, h2]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_aeval_transpose_mul_mul_mul_transpose,
    mul_aeval_transpose_mul_mul_mul_transpose, hP]

/-! ### The error bound -/

omit [DecidableEq n] in
/-- `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
private lemma dotProduct_sub_self_le (x y : n → ℝ) :
    (x - y) ⬝ᵥ (x - y) ≤ 2 * (x ⬝ᵥ x) + 2 * (y ⬝ᵥ y) := by
  have h : 0 ≤ (x + y) ⬝ᵥ (x + y) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
    dotProduct_comm y x] at h ⊢
  linarith

/-- **Lanczos-FA error bound.** Let `A` be symmetric with every eigenvalue in `[a, c]`, `Q` with
orthonormal columns and `K_q(A,b) ⊆ range Q`, and `p` a polynomial with `deg p < q` and
`|f − p| ≤ E` on `[a, c]`. Then `‖f(A) b − Q f(QᵀAQ) Qᵀ b‖² ≤ (2E)² ‖b‖²`, i.e.
`‖f(A) b − Q f(T) Qᵀ b‖ ≤ 2E ‖b‖`. Source: Saad (1992) [`saad92`], Thm 3.4 (with Lemma 3.1);
Druskin–Knizhnerman (1989) [`dk89`]; Higham (2008) [`higham08`], §13.2.
Deviation: an arbitrary approximant `p` in place of the best one (minimise over `p` to get the
printed form); squared Euclidean norms as dot products; no `q ≥ 1` (at `q = 0`, `p = 0`).
atlas: lanczos-fa-error -/
theorem dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {f : ℝ → ℝ} {p : ℝ[X]}
    (hp : p.degree < q) {a c E : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) :
    (cfc f A *ᵥ b - krylovFunApprox Q A f b) ⬝ᵥ (cfc f A *ᵥ b - krylovFunApprox Q A f b) ≤
      (2 * E) ^ 2 * (b ⬝ᵥ b) := by
  set T := Qᵀ * A * Q
  have hT : T.IsHermitian := isHermitian_transpose_mul_mul hA Q
  set c' := Qᵀ *ᵥ b
  set x := (cfc f A - aeval A p) *ᵥ b
  set w := (cfc f T - aeval T p) *ᵥ c'
  have hexact := mulVec_aeval_transpose_mul_mul_mulVec_eq hQ b hK hp
  have he : cfc f A *ᵥ b - krylovFunApprox Q A f b = x - Q *ᵥ w := by
    simp only [x, w, T, c', krylovFunApprox, Matrix.sub_mulVec, Matrix.mulVec_sub, hexact]
    abel
  have hx : x ⬝ᵥ x ≤ E ^ 2 * (b ⬝ᵥ b) :=
    dotProduct_cfc_sub_aeval_mulVec_self_le hA (fun i => hfp _ (hspec i)) b
  have hw : w ⬝ᵥ w ≤ E ^ 2 * (c' ⬝ᵥ c') :=
    dotProduct_cfc_sub_aeval_mulVec_self_le hT
      (fun j => hfp _ (eigenvalues_transpose_mul_mul_mem_Icc hA hQ hT hspec j)) c'
  have hc : c' ⬝ᵥ c' ≤ b ⬝ᵥ b := transpose_mulVec_dotProduct_self_le hQ b
  have hQw : (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) = w ⬝ᵥ w :=
    mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ w
  rw [he]
  refine (dotProduct_sub_self_le x (Q *ᵥ w)).trans ?_
  rw [hQw]
  nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg E)]

/-- **Lanczos-FA error for `f(x) = 1/x`** (the linear-system case): if `A` is symmetric with
every eigenvalue in `[a, c]`, `0 < a < c`, then
`‖A⁻¹ b − Q (QᵀAQ)⁻¹ Qᵀ b‖ ≤ 2 (2/a) ((√c − √a)/(√c + √a))^q ‖b‖` (squared form, with
`A⁻¹ = cfc (1/x) A`). Corollary of `dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le` and
`exists_degree_lt_abs_eval_sub_inv_le` (atlas `inverse-polynomial-approx`).
Source: Saad (1992) [`saad92`], Thm 3.4; Golub–Meurant (2010) [`gm10`], Ch. 8 (the rate).
atlas: lanczos-fa-error (partial) -/
theorem dotProduct_cfc_inv_mulVec_sub_krylovFunApprox_self_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) :
    (cfc (fun x : ℝ => 1 / x) A *ᵥ b - krylovFunApprox Q A (fun x : ℝ => 1 / x) b) ⬝ᵥ
        (cfc (fun x : ℝ => 1 / x) A *ᵥ b - krylovFunApprox Q A (fun x : ℝ => 1 / x) b) ≤
      (2 * ((2 / a) * ((√c - √a) / (√c + √a)) ^ q)) ^ 2 * (b ⬝ᵥ b) := by
  obtain ⟨p, hpdeg, hpE⟩ := exists_degree_lt_abs_eval_sub_inv_le q ha hac
  exact dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le hA hQ b hK hpdeg hspec
    fun x hx => by rw [abs_sub_comm]; exact hpE x hx

end NLAlib
