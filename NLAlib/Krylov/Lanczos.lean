import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import NLAlib.Krylov.GaussQuadrature

/-!
# The Lanczos basis and the tridiagonal (Jacobi) matrix

The Lanczos basis of `K_q(A, b)` is the Gram–Schmidt orthonormalisation of the Krylov vectors
`b, A b, …, A^{q−1} b` (Mathlib's `InnerProductSpace.gramSchmidtNormed` in `EuclideanSpace ℝ n`).
With `Q = lanczosMatrix A b q` (columns the basis vectors) and `T = Qᵀ A Q`:

* `NLAlib.range_lanczosMatrix`: `range Q = K_q(A, b)` (no hypothesis);
* `NLAlib.hasOrthonormalCols_lanczosMatrix`: `QᵀQ = I` when the Krylov vectors are linearly
  independent (no breakdown, `dim K_q = q`);
* `NLAlib.lanczos_apply_eq_zero_of_add_one_lt`: `T` is upper Hessenberg, `T_ij = 0` for
  `i > j + 1`, for every `A`; for symmetric `A`, `T` is symmetric and hence tridiagonal
  (`NLAlib.lanczos_apply_eq_zero_of_add_one_lt'`);
* `NLAlib.transpose_lanczosMatrix_mulVec_apply_eq_zero`: `Qᵀ b` is supported on the first index;
* `NLAlib.dotProduct_aeval_mulVec_eq_lanczos`: Gauss–Lanczos quadrature `bᵀ p(A) b =
  (Qᵀb)ᵀ p(T) (Qᵀb)` for `deg p ≤ 2q − 1`.

The three-term recurrence `A Q_q = Q_q T_q + β_q q_{q+1} e_qᵀ` is the column form of the
Hessenberg/tridiagonal structure; it is not stated separately.

Source: Golub–Meurant (2010) [`gm10`], Ch. 4 (Lanczos algorithm, Thm 4.2); Trefethen–Bau (1997)
[`tb97`], Lecture 36. Atlas: `lanczos-recurrence`; uses `krylov-subspace`,
`lanczos-gauss-quadrature`.
Deviation: the basis is defined by Gram–Schmidt, not by the three-term recurrence (the two agree
in exact arithmetic up to signs).
-/

noncomputable section

open scoped Matrix
open Matrix InnerProductSpace

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Krylov vectors `A^i b`, `i < q`, as elements of `EuclideanSpace ℝ n`.
Atlas: `lanczos-recurrence`. -/
def krylovVectors (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : Fin q → EuclideanSpace ℝ n :=
  fun i => WithLp.toLp 2 ((A ^ (i : ℕ)) *ᵥ b)

/-- The Lanczos basis vectors: the Gram–Schmidt orthonormalisation of `b, A b, …, A^{q−1} b`.
Source: Golub–Meurant (2010) [`gm10`], §4.1. Atlas: `lanczos-recurrence`. -/
def lanczosBasis (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) (i : Fin q) : n → ℝ :=
  (gramSchmidtNormed ℝ (krylovVectors A b q) i).ofLp

/-- The matrix `Q_q` whose columns are the Lanczos basis vectors. Atlas: `lanczos-recurrence`.
atlas: lanczos-recurrence (partial) -/
def lanczosMatrix (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : Matrix n (Fin q) ℝ :=
  Matrix.of fun r i => lanczosBasis A b q i r

omit [DecidableEq n] in
/-- The real inner product on `EuclideanSpace ℝ n` is the dot product of the coordinates.
Atlas: `lanczos-recurrence` (helper). -/
theorem inner_eq_dotProduct_ofLp (x y : EuclideanSpace ℝ n) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

omit [DecidableEq n] in
/-- `(Qᵀ A Q)_ij = q_iᵀ A q_j` for the columns `q_i` of `Q`. Atlas: `lanczos-recurrence`
(helper). -/
theorem transpose_mul_mul_apply {k : Type*} (Q : Matrix n k ℝ) (A : Matrix n n ℝ) (i j : k) :
    (Qᵀ * A * Q) i j = (fun r => Q r i) ⬝ᵥ (A *ᵥ fun r => Q r j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The Lanczos basis spans the Krylov space**: `range Q_q = K_q(A, b)`, with no
non-breakdown hypothesis. Source: Golub–Meurant (2010) [`gm10`], Thm 4.2.
Atlas: `lanczos-recurrence`; uses `krylov-subspace`.
atlas: lanczos-recurrence (partial) -/
theorem range_lanczosMatrix (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    LinearMap.range (lanczosMatrix A b q).mulVecLin = krylovSpace A b q := by
  rw [Matrix.range_mulVecLin]
  have hcols : Set.range (lanczosMatrix A b q).col =
      (WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap ''
        Set.range (gramSchmidtNormed ℝ (krylovVectors A b q)) := by
    rw [← Set.range_comp]; rfl
  have hgen : Set.range (fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) =
      (WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap '' Set.range (krylovVectors A b q) := by
    rw [← Set.range_comp]; rfl
  rw [hcols, krylovSpace, hgen, Submodule.span_image, Submodule.span_image,
    span_gramSchmidtNormed_range, span_gramSchmidt]

/-- **The Lanczos basis is orthonormal** when the Krylov vectors `b, …, A^{q−1} b` are linearly
independent (no breakdown; equivalently `dim K_q(A, b) = q`): `Q_qᵀ Q_q = I`.
Source: Golub–Meurant (2010) [`gm10`], Thm 4.2. Atlas: `lanczos-recurrence`.
atlas: lanczos-recurrence (partial) -/
theorem hasOrthonormalCols_lanczosMatrix {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}
    (h : LinearIndependent ℝ fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b) :
    HasOrthonormalCols (lanczosMatrix A b q) := by
  have hli : LinearIndependent ℝ (krylovVectors A b q) :=
    h.map' (WithLp.linearEquiv 2 ℝ (n → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
  have hon := (orthonormal_iff_ite.1 (gramSchmidtNormed_orthonormal hli))
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, ← hon i j, inner_eq_dotProduct_ofLp]
  rfl

/-- The Gram–Schmidt vector `gᵢ` is orthogonal to `A x` for `x ∈ span{A^l b : l ≤ j}` when
`j + 1 < i`. -/
private lemma inner_gramSchmidt_toLp_mulVec_eq_zero (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    {i j : Fin q} (hij : (j : ℕ) + 1 < i) {x : EuclideanSpace ℝ n}
    (hx : x ∈ Submodule.span ℝ (krylovVectors A b q '' Set.Iic j)) :
    inner ℝ (gramSchmidt ℝ (krylovVectors A b q) i) (WithLp.toLp 2 (A *ᵥ x.ofLp)) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hl' : (l : ℕ) ≤ j := hl
    have hlt : (l : ℕ) + 1 < q := by omega
    have hy : WithLp.toLp 2 (A *ᵥ (krylovVectors A b q l).ofLp) =
        krylovVectors A b q ⟨l + 1, hlt⟩ := by
      simp only [krylovVectors, Matrix.mulVec_mulVec, ← pow_succ']
    rw [hy]
    exact gramSchmidt_inv_triangular ℝ _ (show (⟨l + 1, hlt⟩ : Fin q) < i from by
      rw [Fin.lt_def]; simp only; omega)
  | zero => simp
  | add y z _ _ hy hz =>
    simp only [WithLp.ofLp_add, Matrix.mulVec_add, WithLp.toLp_add, inner_add_right, hy, hz,
      add_zero]
  | smul c y _ hy =>
    simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, WithLp.toLp_smul, inner_smul_right, hy,
      mul_zero]

/-- **The projected matrix is upper Hessenberg**: `(Q_qᵀ A Q_q)_ij = 0` for `i > j + 1`, for
every matrix `A` (no symmetry, no non-breakdown hypothesis). Source: Golub–Meurant (2010)
[`gm10`], §4.1; Trefethen–Bau (1997) [`tb97`], Lecture 33 (Arnoldi). Atlas:
`lanczos-recurrence`.
atlas: lanczos-recurrence (partial) -/
theorem lanczos_apply_eq_zero_of_add_one_lt (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    {i j : Fin q} (hij : (j : ℕ) + 1 < i) :
    ((lanczosMatrix A b q)ᵀ * A * lanczosMatrix A b q) i j = 0 := by
  rw [transpose_mul_mul_apply]
  set f := krylovVectors A b q
  have hmem : gramSchmidt ℝ f j ∈ Submodule.span ℝ (f '' Set.Iic j) :=
    gramSchmidt_mem_span ℝ f le_rfl
  have h0 := inner_gramSchmidt_toLp_mulVec_eq_zero A b hij hmem
  have hcol : ∀ l, (fun r => lanczosMatrix A b q r l) = (gramSchmidtNormed ℝ f l).ofLp :=
    fun l => rfl
  rw [hcol, hcol, gramSchmidtNormed, gramSchmidtNormed, WithLp.ofLp_smul, WithLp.ofLp_smul,
    Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, ← inner_eq_dotProduct_ofLp]
  simp only [smul_eq_mul]
  rw [h0]
  ring

/-- **For symmetric `A` the Lanczos matrix is tridiagonal**: `(Q_qᵀ A Q_q)_ij = 0` for
`j > i + 1` as well. Source: Golub–Meurant (2010) [`gm10`], Thm 4.2; Trefethen–Bau (1997)
[`tb97`], Lecture 36. Atlas: `lanczos-recurrence`. -/
theorem lanczos_apply_eq_zero_of_add_one_lt' {A : Matrix n n ℝ} (hA : A.IsSymm) (b : n → ℝ)
    {q : ℕ} {i j : Fin q} (hij : (i : ℕ) + 1 < j) :
    ((lanczosMatrix A b q)ᵀ * A * lanczosMatrix A b q) i j = 0 := by
  rw [← (isSymm_transpose_mul_mul hA (lanczosMatrix A b q)).apply i j]
  exact lanczos_apply_eq_zero_of_add_one_lt A b hij

/-- The starting vector has Lanczos coordinates supported on the first index:
`(Q_qᵀ b)_i = 0` for `i > 0`. With orthonormal columns, `Q_qᵀ b = ‖b‖ e₁`.
Source: Golub–Meurant (2010) [`gm10`], §4.1 (`q₁ = b/‖b‖`). Atlas: `lanczos-recurrence`. -/
theorem transpose_lanczosMatrix_mulVec_apply_eq_zero (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    {i : Fin q} (hi : 0 < (i : ℕ)) : ((lanczosMatrix A b q)ᵀ *ᵥ b) i = 0 := by
  set f := krylovVectors A b q
  have h0 : inner ℝ (gramSchmidt ℝ f i) (f ⟨0, by omega⟩) = 0 :=
    gramSchmidt_inv_triangular ℝ f (show (⟨0, by omega⟩ : Fin q) < i from by
      rw [Fin.lt_def]; exact hi)
  have hf0 : (f ⟨0, by omega⟩).ofLp = b := by simp [f, krylovVectors]
  have hrow : ((lanczosMatrix A b q)ᵀ *ᵥ b) i = (gramSchmidtNormed ℝ f i).ofLp ⬝ᵥ b := rfl
  rw [hrow, gramSchmidtNormed, WithLp.ofLp_smul, smul_dotProduct, ← hf0,
    ← inner_eq_dotProduct_ofLp, h0, smul_zero]

/-- **Gauss–Lanczos quadrature.** For symmetric `A`, linearly independent Krylov vectors
`b, …, A^{q−1} b` and `q ≥ 1`, every polynomial `p` of degree at most `2q − 1` satisfies
`bᵀ p(A) b = (Q_qᵀ b)ᵀ p(T_q) (Q_qᵀ b)` with `T_q = Q_qᵀ A Q_q` tridiagonal.
Source: Golub–Meurant (2010) [`gm10`], Thm 6.6 and §7.1. Atlas: `lanczos-gauss-quadrature`;
uses `lanczos-recurrence`.
atlas: lanczos-gauss-quadrature -/
theorem dotProduct_aeval_mulVec_eq_lanczos {A : Matrix n n ℝ} (hA : A.IsSymm) {b : n → ℝ}
    {q : ℕ} (hq : 0 < q) (h : LinearIndependent ℝ fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b)
    {p : Polynomial ℝ} (hp : p.natDegree ≤ 2 * q - 1) :
    b ⬝ᵥ (Polynomial.aeval A p *ᵥ b) =
      ((lanczosMatrix A b q)ᵀ *ᵥ b) ⬝ᵥ
        (Polynomial.aeval ((lanczosMatrix A b q)ᵀ * A * lanczosMatrix A b q) p *ᵥ
          ((lanczosMatrix A b q)ᵀ *ᵥ b)) :=
  dotProduct_aeval_mulVec_eq_of_krylovSpace_le hA (hasOrthonormalCols_lanczosMatrix h) b hq
    (range_lanczosMatrix A b q).ge hp

end NLAlib
