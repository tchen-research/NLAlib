import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import NLAlib.Krylov.Arnoldi

/-!
# The Arnoldi process

The Arnoldi process as one noncomputable object (`docs/KRYLOV_DEFINITIONS.md` §3.5): Gram–Schmidt
of the Krylov sequence `b, A b, A² b, …` over `ℕ`, so that column `j` is the same vector for every
number of columns.

* `krylovSeq`, `arnoldiBasis : ℕ → n → ℝ` (zero after breakdown), `arnoldiMatrix A b q`,
  `arnoldiHessenberg A b q = Q_qᵀ A Q_q`;
* `range_arnoldiMatrix` (`range Q_q = K_q`, no hypothesis), `hasOrthonormalCols_arnoldiMatrix`
  (`q ≤ krylovGrade A b`), `arnoldiHessenberg_apply_eq_zero_of_add_one_lt` (upper Hessenberg,
  no hypothesis) and its symmetric (tridiagonal) form,
  `transpose_arnoldiMatrix_mulVec_apply_eq_zero`;
* the canonical witness `arnoldiDecomp A b q h : ArnoldiDecomp A b q` for `q ≤ krylovGrade A b`,
  with positive subdiagonal (`arnoldiDecomp_H_subdiag_pos`) and `q_1 ⬝ b = ‖b‖ > 0`
  (`arnoldiBasis_zero_dotProduct_pos`); it is the only decomposition with these signs
  (`ArnoldiDecomp.Q_eq_arnoldiMatrix`); `exists_isGradedKrylovBasis_iff`.

These replace the `Fin q`-indexed `lanczosBasis`/`lanczosMatrix` (renames in
`docs/renames/2026-10-10-krylov.json`).

Source: Saad (2003) [`saad03`], §6.3 (Alg. 6.1, Props 6.4–6.5); Trefethen–Bau (1997) [`tb97`],
Lect. 33, 36; Golub–Meurant (2010) [`gm10`], §4.1. Atlas: `arnoldi-def`,
`graded-krylov-basis-def` (existence); `lanczos-recurrence` (tridiagonality).
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open InnerProductSpace

omit [DecidableEq n] in
/-- The real inner product on `EuclideanSpace ℝ n` is the dot product of the coordinates.
Helper for `arnoldi-def`. -/
theorem inner_eq_dotProduct_ofLp (x y : EuclideanSpace ℝ n) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The Krylov sequence `b, A b, A² b, …` in `EuclideanSpace ℝ n` (the input of Gram–Schmidt).
Atlas: `arnoldi-def`. -/
def krylovSeq (A : Matrix n n ℝ) (b : n → ℝ) (i : ℕ) : EuclideanSpace ℝ n :=
  WithLp.toLp 2 ((A ^ i) *ᵥ b)

/-- The **Arnoldi basis** `q_0, q_1, …`: Gram–Schmidt orthonormalisation of `b, A b, A² b, …`
(`gramSchmidtNormed` over `ℕ`); `q_j = 0` from the grade on (breakdown). Column `j` does not
depend on how many columns are taken. Source: Saad (2003) [`saad03`], Alg. 6.1;
Trefethen–Bau (1997) [`tb97`], Lect. 33. Atlas: `arnoldi-def`. -/
def arnoldiBasis (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) : n → ℝ :=
  (gramSchmidtNormed ℝ (krylovSeq A b) j).ofLp

/-- The matrix `Q_q` of the first `q` Arnoldi vectors.
Source: Saad (2003) [`saad03`], §6.3.
atlas: arnoldi-def -/
def arnoldiMatrix (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : Matrix n (Fin q) ℝ :=
  Matrix.of fun r j => arnoldiBasis A b j r

/-- The Arnoldi Hessenberg matrix `H_q = Q_qᵀ A Q_q`.
Source: Saad (2003) [`saad03`], §6.3.
atlas: arnoldi-def -/
def arnoldiHessenberg (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  (arnoldiMatrix A b q)ᵀ * A * arnoldiMatrix A b q

/-- Column `j` of `Q_q` is the Arnoldi vector `q_j`. Atlas: `arnoldi-def`. -/
theorem arnoldiMatrix_col (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) (j : Fin q) :
    (arnoldiMatrix A b q).col j = arnoldiBasis A b j := rfl

/-- `range (fun j : Fin q => φ j) = φ '' {j | j < q}`. -/
private lemma range_fin_eq_image {α : Type*} (φ : ℕ → α) (q : ℕ) :
    Set.range (fun j : Fin q => φ j) = φ '' Set.Iio q := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩

/-- `K_j(A, b)` is the image of `span {krylovSeq A b i : i < j}`. -/
private lemma krylovSpace_eq_map (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    krylovSpace A b j = (Submodule.span ℝ (krylovSeq A b '' Set.Iio j)).map
      (WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap := by
  rw [← Submodule.span_image, ← Set.image_comp, krylovSpace]
  congr 1
  exact range_fin_eq_image (fun i => (A ^ i) *ᵥ b) j

/-- Transport of membership between `EuclideanSpace` and `n → ℝ`. -/
private lemma mem_span_krylovSeq_iff (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ n) :
    x ∈ Submodule.span ℝ (krylovSeq A b '' Set.Iio j) ↔ x.ofLp ∈ krylovSpace A b j := by
  rw [krylovSpace_eq_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := by
      have := congrArg (WithLp.toLp 2) hyx
      simpa using this
    rwa [← this]

/-- The unnormalised Gram–Schmidt vector `g_j` lies in `K_{j+1}`. -/
private lemma gramSchmidt_ofLp_mem (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    (gramSchmidt ℝ (krylovSeq A b) j).ofLp ∈ krylovSpace A b (j + 1) := by
  rw [← mem_span_krylovSeq_iff, show Set.Iio (j + 1) = Set.Iic j from by ext; simp]
  exact gramSchmidt_mem_span ℝ _ le_rfl

/-- `A^j b − g_j ∈ K_j`. -/
private lemma pow_mulVec_sub_gramSchmidt_mem (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    (A ^ j) *ᵥ b - (gramSchmidt ℝ (krylovSeq A b) j).ofLp ∈ krylovSpace A b j := by
  have h := gramSchmidt_def'' ℝ (krylovSeq A b) j
  have hmem : (∑ i ∈ Finset.Iio j, (inner ℝ (gramSchmidt ℝ (krylovSeq A b) i)
      (krylovSeq A b j) / ‖gramSchmidt ℝ (krylovSeq A b) i‖ ^ 2) •
        gramSchmidt ℝ (krylovSeq A b) i) ∈ Submodule.span ℝ (krylovSeq A b '' Set.Iio j) := by
    rw [← span_gramSchmidt_Iio]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
  rw [mem_span_krylovSeq_iff] at hmem
  convert hmem using 1
  have h' := congrArg WithLp.ofLp h
  rw [WithLp.ofLp_add] at h'
  change (A ^ j) *ᵥ b = _ at h'
  rw [h']
  abel

/-- `‖g_j‖ ≠ 0` below the grade. -/
private lemma gramSchmidt_ne_zero_of_lt (A : Matrix n n ℝ) (b : n → ℝ) {j : ℕ}
    (hj : j < krylovGrade A b) : gramSchmidt ℝ (krylovSeq A b) j ≠ 0 := by
  intro h0
  have h := pow_mulVec_sub_gramSchmidt_mem A b j
  rw [h0, WithLp.ofLp_zero, sub_zero] at h
  exact pow_mulVec_notMem_krylovSpace_of_lt_krylovGrade A b hj h

/-- `arnoldiBasis A b j = ‖g_j‖⁻¹ • g_j`. -/
private lemma arnoldiBasis_eq (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    arnoldiBasis A b j =
      ‖gramSchmidt ℝ (krylovSeq A b) j‖⁻¹ • (gramSchmidt ℝ (krylovSeq A b) j).ofLp := by
  rw [arnoldiBasis, gramSchmidtNormed, WithLp.ofLp_smul]
  rfl

/-- `g_i` is orthogonal to `span {g_l : l < i}`. -/
private lemma inner_gramSchmidt_eq_zero_of_mem_span (A : Matrix n n ℝ) (b : n → ℝ) {i : ℕ}
    {x : EuclideanSpace ℝ n}
    (hx : x ∈ Submodule.span ℝ (gramSchmidt ℝ (krylovSeq A b) '' Set.Iio i)) :
    inner ℝ (gramSchmidt ℝ (krylovSeq A b) i) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact gramSchmidt_orthogonal ℝ _ (Nat.ne_of_gt hl)
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]

/-- The Arnoldi vector `q_j` lies in `K_{j+1}(A, b)`. Atlas: `arnoldi-def`. -/
theorem arnoldiBasis_mem_krylovSpace (A : Matrix n n ℝ) (b : n → ℝ) (j : ℕ) :
    arnoldiBasis A b j ∈ krylovSpace A b (j + 1) := by
  rw [arnoldiBasis_eq]
  exact Submodule.smul_mem _ _ (gramSchmidt_ofLp_mem A b j)

/-- Orthonormality of the Arnoldi vectors below the grade: `q_i ⬝ q_j = δ_ij`. -/
theorem arnoldiBasis_dotProduct (A : Matrix n n ℝ) (b : n → ℝ) {i j : ℕ}
    (hi : i < krylovGrade A b) (hj : j < krylovGrade A b) :
    arnoldiBasis A b i ⬝ᵥ arnoldiBasis A b j = if i = j then 1 else 0 := by
  rw [arnoldiBasis, arnoldiBasis, ← inner_eq_dotProduct_ofLp]
  split_ifs with hij
  · subst hij
    have hne := gramSchmidt_ne_zero_of_lt A b hi
    rw [real_inner_self_eq_norm_sq,
      gramSchmidtNormed_unit_length' (by simp [gramSchmidtNormed, hne]), one_pow]
  · simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right,
      gramSchmidt_orthogonal ℝ _ hij, mul_zero]

/-- **The Arnoldi basis spans the Krylov space**: `range Q_q = K_q(A, b)`, with no hypothesis.
Source: Saad (2003) [`saad03`], Prop. 6.4.
atlas: arnoldi-def (partial) -/
theorem range_arnoldiMatrix (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    LinearMap.range (arnoldiMatrix A b q).mulVecLin = krylovSpace A b q := by
  rw [Matrix.range_mulVecLin, krylovSpace_eq_map, ← span_gramSchmidt_Iio,
    ← span_gramSchmidtNormed, Submodule.map_span, ← Set.image_comp]
  exact congrArg _ (range_fin_eq_image (fun j => arnoldiBasis A b j) q)

/-- **The Arnoldi basis is orthonormal below the grade**: `Q_qᵀ Q_q = I` for
`q ≤ krylovGrade A b`. Source: Saad (2003) [`saad03`], Prop. 6.4.
atlas: arnoldi-def (partial) -/
theorem hasOrthonormalCols_arnoldiMatrix {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}
    (h : q ≤ krylovGrade A b) : HasOrthonormalCols (arnoldiMatrix A b q) := by
  ext i j
  rw [transpose_mul_self_apply, arnoldiMatrix_col, arnoldiMatrix_col,
    arnoldiBasis_dotProduct A b (by omega) (by omega), Matrix.one_apply]
  simp [Fin.ext_iff]

/-- **The Arnoldi Hessenberg matrix is upper Hessenberg**, `h_ij = 0` for `i > j + 1`, for every
`A` and every `q` (no symmetry, no non-breakdown hypothesis).
Source: Saad (2003) [`saad03`], Prop. 6.5; Trefethen–Bau (1997) [`tb97`], Lect. 33.
atlas: arnoldi-def (partial) -/
theorem arnoldiHessenberg_apply_eq_zero_of_add_one_lt (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    {i j : Fin q} (hij : (j : ℕ) + 1 < i) : arnoldiHessenberg A b q i j = 0 := by
  rw [arnoldiHessenberg, transpose_mul_mul_apply, arnoldiMatrix_col, arnoldiMatrix_col,
    arnoldiBasis, gramSchmidtNormed, WithLp.ofLp_smul, smul_dotProduct,
    ← inner_eq_dotProduct_ofLp]
  have hx : WithLp.toLp 2 (A *ᵥ arnoldiBasis A b j) ∈
      Submodule.span ℝ (gramSchmidt ℝ (krylovSeq A b) '' Set.Iio i) := by
    rw [span_gramSchmidt_Iio, mem_span_krylovSeq_iff]
    exact krylovSpace_mono A b (by omega)
      (mulVec_mem_krylovSpace_succ A b (arnoldiBasis_mem_krylovSpace A b j))
  rw [inner_gramSchmidt_eq_zero_of_mem_span A b hx, smul_zero]

/-- **For symmetric `A` the Arnoldi Hessenberg matrix is tridiagonal**: also `h_ij = 0` for
`j > i + 1` (the Lanczos case). Source: Golub–Meurant (2010) [`gm10`], Thm 4.2;
Trefethen–Bau (1997) [`tb97`], Lect. 36.
atlas: lanczos-recurrence -/
theorem arnoldiHessenberg_apply_eq_zero_of_add_one_lt_of_isSymm {A : Matrix n n ℝ}
    (hA : A.IsSymm) (b : n → ℝ) {q : ℕ} {i j : Fin q} (hij : (i : ℕ) + 1 < j) :
    arnoldiHessenberg A b q i j = 0 := by
  rw [arnoldiHessenberg, ← (isSymm_transpose_mul_mul hA (arnoldiMatrix A b q)).apply i j]
  exact arnoldiHessenberg_apply_eq_zero_of_add_one_lt A b hij

/-- The starting vector has Arnoldi coordinates supported on the first index:
`(Q_qᵀ b)_i = 0` for `i > 0`. Source: Saad (2003) [`saad03`], Alg. 6.1 (`q₁ = b/‖b‖`).
Atlas: `arnoldi-def`. -/
theorem transpose_arnoldiMatrix_mulVec_apply_eq_zero (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    {i : Fin q} (hi : 0 < (i : ℕ)) : ((arnoldiMatrix A b q)ᵀ *ᵥ b) i = 0 := by
  have hb : WithLp.toLp 2 b ∈ Submodule.span ℝ (gramSchmidt ℝ (krylovSeq A b) '' Set.Iio i) := by
    rw [span_gramSchmidt_Iio, mem_span_krylovSeq_iff]
    simpa using pow_mulVec_mem_krylovSpace A b (i := 0) hi
  have h0 := inner_gramSchmidt_eq_zero_of_mem_span A b hb
  have hrow : ((arnoldiMatrix A b q)ᵀ *ᵥ b) i = arnoldiBasis A b i ⬝ᵥ b := rfl
  rw [hrow, arnoldiBasis, gramSchmidtNormed, WithLp.ofLp_smul, smul_dotProduct,
    show b = (WithLp.toLp 2 b).ofLp from rfl, ← inner_eq_dotProduct_ofLp, h0, smul_zero]

/-- The **canonical Arnoldi decomposition** (Gram–Schmidt, positive subdiagonal) of size
`q ≤ krylovGrade A b`. Source: Saad (2003) [`saad03`], Alg. 6.1 and Prop. 6.4.
atlas: arnoldi-def -/
def arnoldiDecomp (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) (h : q ≤ krylovGrade A b) :
    ArnoldiDecomp A b q where
  Q := arnoldiMatrix A b q
  graded := IsGradedKrylovBasis.of_mem (hasOrthonormalCols_arnoldiMatrix h) fun j =>
    arnoldiBasis_mem_krylovSpace A b j

/-- The basis of the canonical decomposition is `arnoldiMatrix`. Atlas: `arnoldi-def`. -/
theorem arnoldiDecomp_Q (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (h : q ≤ krylovGrade A b) :
    (arnoldiDecomp A b q h).Q = arnoldiMatrix A b q := rfl

/-- The Hessenberg matrix of the canonical decomposition is `arnoldiHessenberg`.
Atlas: `arnoldi-def`. -/
theorem arnoldiDecomp_H (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (h : q ≤ krylovGrade A b) :
    (arnoldiDecomp A b q h).H = arnoldiHessenberg A b q := rfl

/-- **Existence of graded bases**: a graded orthonormal Krylov basis with `q` columns exists iff
`q ≤ krylovGrade A b`. Source: Saad (2011) [`saad11`], §6.3; Saad (2003) [`saad03`], Prop. 6.4.
atlas: graded-krylov-basis-def (partial) -/
theorem exists_isGradedKrylovBasis_iff (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    (∃ Q : Matrix n (Fin q) ℝ, IsGradedKrylovBasis A b Q) ↔ q ≤ krylovGrade A b :=
  ⟨fun ⟨_, hQ⟩ => hQ.le_krylovGrade, fun h => ⟨_, (arnoldiDecomp A b q h).graded⟩⟩

/-- **The canonical decomposition has positive subdiagonal**: `h_{j+1,j} = ‖g_{j+1}‖/‖g_j‖ > 0`
with `g_j` the unnormalised Gram–Schmidt vectors. Source: Saad (2003) [`saad03`], Alg. 6.1
(`h_{j+1,j} = ‖w_j‖`).
atlas: arnoldi-def (partial) -/
theorem arnoldiDecomp_H_subdiag_pos (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    (h : q ≤ krylovGrade A b) {j : ℕ} (hj : j + 1 < q) :
    0 < (arnoldiDecomp A b q h).H ⟨j + 1, hj⟩ ⟨j, by omega⟩ := by
  set D := arnoldiDecomp A b q h
  set g := fun k => (gramSchmidt ℝ (krylovSeq A b) k).ofLp
  have hg : ∀ k, k < krylovGrade A b → 0 < ‖gramSchmidt ℝ (krylovSeq A b) k‖ := fun k hk =>
    norm_pos_iff.2 (gramSchmidt_ne_zero_of_lt A b hk)
  have hperp : ∀ x ∈ krylovSpace A b (j + 1), arnoldiBasis A b (j + 1) ⬝ᵥ x = 0 :=
    fun x hx => D.graded.col_dotProduct_eq_zero ⟨j + 1, hj⟩ hx
  rw [ArnoldiDecomp.H_apply]
  change arnoldiBasis A b (j + 1) ⬝ᵥ (A *ᵥ arnoldiBasis A b j) > 0
  -- `A q_j = ‖g_j‖⁻¹ (A^{j+1} b − A (A^j b − g_j))`
  have h1 : A *ᵥ arnoldiBasis A b j = ‖gramSchmidt ℝ (krylovSeq A b) j‖⁻¹ •
      ((A ^ (j + 1)) *ᵥ b - A *ᵥ ((A ^ j) *ᵥ b - g j)) := by
    rw [arnoldiBasis_eq, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_succ',
      sub_sub_cancel]
  have h2 : arnoldiBasis A b (j + 1) ⬝ᵥ (A *ᵥ ((A ^ j) *ᵥ b - g j)) = 0 :=
    hperp _ (mulVec_mem_krylovSpace_succ A b (pow_mulVec_sub_gramSchmidt_mem A b j))
  have h3 : arnoldiBasis A b (j + 1) ⬝ᵥ ((A ^ (j + 1)) *ᵥ b - g (j + 1)) = 0 :=
    hperp _ (pow_mulVec_sub_gramSchmidt_mem A b (j + 1))
  have h4 : arnoldiBasis A b (j + 1) ⬝ᵥ g (j + 1) = ‖gramSchmidt ℝ (krylovSeq A b) (j + 1)‖ := by
    have hpos := hg (j + 1) (by omega)
    rw [arnoldiBasis_eq, smul_dotProduct, ← inner_eq_dotProduct_ofLp, real_inner_self_eq_norm_sq,
      smul_eq_mul]
    field_simp
  rw [h1, dotProduct_smul, dotProduct_sub, h2, sub_zero, smul_eq_mul]
  rw [dotProduct_sub, h4, sub_eq_zero] at h3
  rw [h3]
  exact mul_pos (inv_pos.2 (hg j (by omega))) (hg (j + 1) (by omega))

/-- The first canonical Arnoldi vector is `b/‖b‖`: `q_1 ⬝ b = ‖b‖ > 0` (for `b ≠ 0`, i.e.
`0 < krylovGrade A b`). Source: Saad (2003) [`saad03`], Alg. 6.1. Atlas: `arnoldi-def`. -/
theorem arnoldiBasis_zero_dotProduct_pos (A : Matrix n n ℝ) (b : n → ℝ)
    (h : 0 < krylovGrade A b) : 0 < arnoldiBasis A b 0 ⬝ᵥ b := by
  have hg := norm_pos_iff.2 (gramSchmidt_ne_zero_of_lt A b h)
  have hb : (gramSchmidt ℝ (krylovSeq A b) 0).ofLp = b := by
    have h0 := pow_mulVec_sub_gramSchmidt_mem A b 0
    simp only [krylovSpace, Set.range_eq_empty, Submodule.span_empty,
      Submodule.mem_bot, pow_zero, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0.symm
  have hdot : (gramSchmidt ℝ (krylovSeq A b) 0).ofLp ⬝ᵥ b =
      ‖gramSchmidt ℝ (krylovSeq A b) 0‖ ^ 2 := by
    conv_lhs => arg 2; rw [← hb]
    rw [← inner_eq_dotProduct_ofLp, real_inner_self_eq_norm_sq]
  rw [arnoldiBasis_eq, smul_dotProduct, hdot, smul_eq_mul]
  positivity

/-- **Characterisation of the canonical decomposition**: an Arnoldi decomposition with
`q_1 ⬝ b > 0` and positive subdiagonal is the Gram–Schmidt one, `Q = arnoldiMatrix A b q`.
Source: Saad (2003) [`saad03`], §6.3 (implicit-Q); Trefethen–Bau (1997) [`tb97`], Lect. 33.
atlas: arnoldi-def (partial) -/
theorem ArnoldiDecomp.Q_eq_arnoldiMatrix {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}
    (D : ArnoldiDecomp A b q)
    (h0 : ∀ hq : 0 < q, 0 < D.Q.col ⟨0, hq⟩ ⬝ᵥ b)
    (hH : ∀ j (hj : j + 1 < q), 0 < D.H ⟨j + 1, hj⟩ ⟨j, by omega⟩) :
    D.Q = arnoldiMatrix A b q :=
  (arnoldiDecomp A b q D.le_krylovGrade).Q_eq_of_pos D
    (fun hq => arnoldiBasis_zero_dotProduct_pos A b (by have := D.le_krylovGrade; omega)) h0
    (fun _ hj => arnoldiDecomp_H_subdiag_pos A b _ hj) hH

end NLAlib
