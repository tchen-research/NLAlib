import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Quadratic forms

`NLAlib.quadForm A z = zᴴ A z := star z ⬝ᵥ (A *ᵥ z)` over any `[RCLike 𝕜]`, `𝕜`-valued, which is
Mathlib's `Matrix.PosSemidef` form (`Matrix.posSemidef_iff_dotProduct_mulVec`); over `ℝ` it is
`zᵀ A z = z ⬝ᵥ (A *ᵥ z)` by `rfl` (`quadForm_eq_dotProduct`). Its algebraic API: the expansion as a
double sum (`quadForm_eq_sum_star`, `quadForm_eq_sum_star_mul_mul`) and of its square
(`quadForm_sq_eq_sum_star`), invariance under relabelling (`quadForm_reindex`), additivity and
homogeneity (`quadForm_add`, `quadForm_smul`), the polarisation expansion on two real-scaled
vectors (`re_quadForm_smul_add_smul`), the rank-one form (`quadForm_vecMulVec_star_self`),
congruence (`quadForm_conjTranspose_mul_mul`), the normal-equations form
(`quadForm_conjTranspose_mul_self`), conjugation (`star_quadForm`) and positivity
(`quadForm_nonneg`, `re_quadForm_nonneg`, `quadForm_pos`); and the real-valued Rayleigh quotient
`rayleighQuotient A x = re (xᴴAx) / re (xᴴx)`.

Real corollaries keep their pre-RCLike names and `ᵀ`/`⬝ᵥ` statements (`quadForm_eq_sum`,
`quadForm_eq_sum_mul_mul`, `quadForm_sq_eq_sum`, `quadForm_smul_add_smul`,
`quadForm_vecMulVec_self`, `quadForm_transpose_mul_mul`, `quadForm_transpose_mul_self`), and
`rayleighQuotient_eq_div` is the `rfl` bridge `ρ(x) = xᵀAx / xᵀx` over `ℝ`.

Layer 0: used by the Krylov layer (spectral measure, CG energy norm, power method) and by the
Hutchinson estimators (`NLAlib.Estimation.Trace`).

Atlas: `hutchinson-unbiased`, `hutchinson-variance`, `spectral-measure` (definition used in their
statements).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The quadratic form `zᴴ A z = star z ⬝ᵥ (A *ᵥ z)` (𝕜-valued; Mathlib's `PosSemidef` form). Over
`ℝ` it is `zᵀ A z` by `rfl` (`quadForm_eq_dotProduct`). Atlas: `hutchinson-unbiased`,
`hutchinson-variance`.
atlas: quadform-def -/
def quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) : 𝕜 := star z ⬝ᵥ (A *ᵥ z)

/-- Unfolding lemma for `quadForm` (`rfl`). -/
theorem quadForm_def (A : Matrix n n 𝕜) (z : n → 𝕜) : quadForm A z = star z ⬝ᵥ (A *ᵥ z) := rfl

/-- Over `ℝ` the quadratic form is the dot product `z ⬝ᵥ (A *ᵥ z)` (`rfl`): the bridge to use in
real files instead of unfolding `quadForm`. -/
theorem quadForm_eq_dotProduct (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z = z ⬝ᵥ (A *ᵥ z) := rfl

/-- `0ᴴ A 0 = 0` (`@[simp]`). Atlas: `hutchinson-unbiased` (helper). -/
@[simp] theorem quadForm_zero_right (A : Matrix n n 𝕜) : quadForm A 0 = 0 := by
  simp [quadForm]

/-- The quadratic form of the zero matrix vanishes (`@[simp]`). -/
@[simp] theorem quadForm_zero_left (z : n → 𝕜) : quadForm (0 : Matrix n n 𝕜) z = 0 := by
  simp [quadForm]

/-- Expansion `zᴴ A z = ∑ᵢ ∑ⱼ A_ij (conj zᵢ) zⱼ`. -/
theorem quadForm_eq_sum_star (A : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm A z = ∑ i, ∑ j, A i j * (star (z i) * z j) := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Expansion `zᵀ A z = ∑ᵢ ∑ⱼ A_ij z_i z_j` (real corollary of `quadForm_eq_sum_star`).
Atlas: `hutchinson-unbiased` (helper). -/
theorem quadForm_eq_sum (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z = ∑ i, ∑ j, A i j * (z i * z j) := by
  simpa only [star_trivial] using quadForm_eq_sum_star A z

/-- The quadratic form as the double sum `zᴴ A z = ∑ᵢ ∑ⱼ (conj zᵢ) Aᵢⱼ zⱼ`. -/
theorem quadForm_eq_sum_star_mul_mul (A : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm A z = ∑ i, ∑ j, star (z i) * A i j * z j := by
  rw [quadForm_eq_sum_star]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form as the double sum `zᵀ A z = ∑ᵢ ∑ⱼ zᵢ Aᵢⱼ zⱼ` (the order of factors used
throughout the Hanson–Wright proof; real corollary of `quadForm_eq_sum_star_mul_mul`).
Atlas `hanson-wright` (helper). -/
theorem quadForm_eq_sum_mul_mul (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z = ∑ i, ∑ j, z i * A i j * z j := by
  simpa only [star_trivial] using quadForm_eq_sum_star_mul_mul A z

/-- Expansion `(zᴴ A z)² = ∑ᵢⱼₖₗ A_ij A_kl (conj z_i) z_j (conj z_k) z_l`. -/
theorem quadForm_sq_eq_sum_star (A : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm A z ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (star (z i) * z j * star (z k) * z l) := by
  rw [sq, quadForm_eq_sum_star, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Expansion `(zᵀ A z)² = ∑ᵢⱼₖₗ A_ij A_kl z_i z_j z_k z_l` (real corollary of
`quadForm_sq_eq_sum_star`). Atlas: `hutchinson-variance` (helper). -/
theorem quadForm_sq_eq_sum (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (z i * z j * z k * z l) := by
  simpa only [star_trivial] using quadForm_sq_eq_sum_star A z

/-- Relabelling the coordinates by an equivalence does not change the quadratic form.
Atlas `hanson-wright` (index transport). -/
theorem quadForm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι 𝕜) (e : ι ≃ κ)
    (z : ι → 𝕜) : quadForm (A.reindex e e) (fun k => z (e.symm k)) = quadForm A z := by
  rw [quadForm_eq_sum_star, quadForm_eq_sum_star]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun i => ∑ k, A i (e.symm k) * (star (z i) * z (e.symm k)))]
  exact Finset.sum_congr rfl fun i _ =>
    e.symm.sum_comp (fun j => A i j * (star (z i) * z j))

/-- Expansion of the quadratic form of a sum:
`(x + y)ᴴ A (x + y) = xᴴAx + xᴴAy + yᴴAx + yᴴAy`. -/
theorem quadForm_add (A : Matrix n n 𝕜) (x y : n → 𝕜) :
    quadForm A (x + y) =
      quadForm A x + star x ⬝ᵥ (A *ᵥ y) + star y ⬝ᵥ (A *ᵥ x) + quadForm A y := by
  simp only [quadForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  ring

/-- Homogeneity of the quadratic form: `(c z)ᴴ A (c z) = (conj c) c · zᴴ A z`. -/
theorem quadForm_smul (A : Matrix n n 𝕜) (c : 𝕜) (z : n → 𝕜) :
    quadForm A (c • z) = star c * c * quadForm A z := by
  simp only [quadForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, RCLike.star_def]
  ring

/-- Conjugating the quadratic form passes to the conjugate transpose: `conj (zᴴ A z) = zᴴ Aᴴ z`. -/
theorem star_quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) :
    star (quadForm A z) = quadForm Aᴴ z := by
  rw [quadForm, quadForm, Matrix.star_dotProduct, Matrix.star_mulVec, star_star,
    Matrix.dotProduct_mulVec]

/-- The quadratic form of a Hermitian matrix is real: `↑(re (zᴴ A z)) = zᴴ A z`. -/
theorem ofReal_re_quadForm {A : Matrix n n 𝕜} (hA : A.IsHermitian) (z : n → 𝕜) :
    ((RCLike.re (quadForm A z) : ℝ) : 𝕜) = quadForm A z := by
  rw [RCLike.conj_eq_iff_re.mp]
  rw [← RCLike.star_def, star_quadForm, hA.eq]

/-- For Hermitian `A`, the cross terms of the polarisation are conjugate:
`yᴴ A x = conj (xᴴ A y)`. -/
theorem star_dotProduct_mulVec_comm_of_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x y : n → 𝕜) : star y ⬝ᵥ (A *ᵥ x) = star (star x ⬝ᵥ (A *ᵥ y)) := by
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec,
    hA.eq]

/-- Expanding the real part of a Hermitian quadratic form on two real-scaled vectors gives the
diagonal energies and twice the real part of the cross term. Horn–Johnson (2013), Section
7.4.12; helper for Wielandt's inequality. -/
theorem re_quadForm_smul_add_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x y : n → 𝕜) (r s : ℝ) :
    RCLike.re (quadForm A ((r : 𝕜) • x + (s : 𝕜) • y)) =
      r ^ 2 * RCLike.re (quadForm A x) + 2 * r * s * RCLike.re (star x ⬝ᵥ (A *ᵥ y)) +
        s ^ 2 * RCLike.re (quadForm A y) := by
  have hcross : RCLike.re (star y ⬝ᵥ (A *ᵥ x)) = RCLike.re (star x ⬝ᵥ (A *ᵥ y)) := by
    rw [star_dotProduct_mulVec_comm_of_isHermitian hA, RCLike.star_def, RCLike.conj_re]
  rw [quadForm_add, quadForm_smul, quadForm_smul]
  simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    map_add, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, RCLike.re_ofReal_mul,
    hcross]
  ring

/-- Expanding a real symmetric quadratic form on two scaled vectors gives
the diagonal energies and twice the cross term (real corollary of `re_quadForm_smul_add_smul`).
Horn–Johnson (2013), Section 7.4.12; helper for Wielandt's inequality. -/
theorem quadForm_smul_add_smul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x y : n → ℝ) (r s : ℝ) :
    quadForm A (r • x + s • y) = r ^ 2 * quadForm A x +
      2 * r * s * (x ⬝ᵥ A *ᵥ y) + s ^ 2 * quadForm A y := by
  simpa using re_quadForm_smul_add_smul hA x y r s

/-- The quadratic form of a rank-one Gram matrix `b bᴴ` is `|zᴴ b|²`. Horn–Johnson (2013),
Section 7.1. -/
theorem quadForm_vecMulVec_star_self (b x : n → 𝕜) :
    quadForm (Matrix.vecMulVec b (star b)) x = (‖star x ⬝ᵥ b‖ : 𝕜) ^ 2 := by
  rw [quadForm, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul, ← RCLike.mul_conj,
    ← RCLike.star_def, ← Matrix.star_dotProduct_star, star_star]

/-- The quadratic form of a real rank-one Gram matrix is the squared
dot product with its defining vector (real corollary of `quadForm_vecMulVec_star_self`).
Horn–Johnson (2013), Section 7.1; helper for finite exponential certificates. -/
theorem quadForm_vecMulVec_self (b x : n → ℝ) :
    quadForm (Matrix.vecMulVec b b) x = (x ⬝ᵥ b) ^ 2 := by
  simpa only [star_trivial, Real.norm_eq_abs, sq_abs, RCLike.ofReal_real_eq_id, id] using
    quadForm_vecMulVec_star_self b x

/-- Congruence: `quadForm (WᴴAW) v = quadForm A (Wv)` for a rectangular `W`. Horn–Johnson (2013),
Theorem 4.5.9. -/
theorem quadForm_conjTranspose_mul_mul {k : Type*} [Fintype k] (A : Matrix n n 𝕜)
    (W : Matrix n k 𝕜) (v : k → 𝕜) :
    quadForm (Wᴴ * A * W) v = quadForm A (W *ᵥ v) := by
  rw [quadForm, quadForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (star v) Wᴴ, Matrix.star_mulVec]

/-- Congruence: `quadForm (WᵀAW) v = quadForm A (Wv)` for a rectangular real `W` (real corollary of
`quadForm_conjTranspose_mul_mul`). Helper for `preconditioned-cg` and
`ostrowski-congruence-eigenvalues` (Horn–Johnson 2013, Theorem 4.5.9). -/
theorem quadForm_transpose_mul_mul {k : Type*} [Fintype k] (A : Matrix n n ℝ)
    (W : Matrix n k ℝ) (v : k → ℝ) :
    quadForm (Wᵀ * A * W) v = quadForm A (W *ᵥ v) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    quadForm_conjTranspose_mul_mul A W v

/-- `(Aᴴ A y)ᴴ y = (Ay)ᴴ (Ay)`: the quadratic form of the normal-equations matrix. -/
theorem quadForm_conjTranspose_mul_self {m : Type*} [Fintype m] (A : Matrix m n 𝕜)
    (y : n → 𝕜) : quadForm (Aᴴ * A) y = star (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
  rw [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.vecMul_conjTranspose]

/-- `(Aᵀ A y) ⬝ y = ‖A y‖²`: the quadratic form of the normal-equations matrix (real corollary of
`quadForm_conjTranspose_mul_self`). Helper for `cgls-lsqr-bound`. -/
theorem quadForm_transpose_mul_self {m : Type*} [Fintype m] (A : Matrix m n ℝ) (y : n → ℝ) :
    quadForm (Aᵀ * A) y = (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, star_trivial] using
    quadForm_conjTranspose_mul_self A y

section Order

open scoped ComplexOrder

/-- The quadratic form of a positive semidefinite matrix is nonnegative (in the `ComplexOrder`
on `𝕜`; over `ℝ` the usual order). Mathlib's `Matrix.PosSemidef.dotProduct_mulVec_nonneg`. -/
theorem quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (z : n → 𝕜) :
    0 ≤ quadForm A z :=
  hA.dotProduct_mulVec_nonneg z

/-- The quadratic form of a positive definite matrix is positive at a nonzero vector (in the
`ComplexOrder` on `𝕜`). Mathlib's `Matrix.PosDef.dotProduct_mulVec_pos`. -/
theorem quadForm_pos {A : Matrix n n 𝕜} (hA : A.PosDef) {z : n → 𝕜} (hz : z ≠ 0) :
    0 < quadForm A z :=
  hA.dotProduct_mulVec_pos hz

/-- The real part of the quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem re_quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (z : n → 𝕜) :
    0 ≤ RCLike.re (quadForm A z) :=
  (RCLike.nonneg_iff.mp (quadForm_nonneg hA z)).1

end Order

/-- The Rayleigh quotient `ρ(x) = re (xᴴAx) / re (xᴴx)` (real-valued; junk value `0` at `x = 0`).
Over `ℝ` it is `xᵀAx / xᵀx` by `rfl` (`rayleighQuotient_eq_div`). Source: Trefethen–Bau
(1997) [`tb97`], Lect. 27. Helper for `power-iteration`; Mathlib's
`ContinuousLinearMap.rayleighQuotient` of `Matrix.toEuclideanCLM A` agrees with it at `ℝ`
(`rayleighQuotient_toEuclideanCLM_eq`). -/
def rayleighQuotient (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (quadForm A x) / RCLike.re (star x ⬝ᵥ x)

/-- Unfolding lemma for `rayleighQuotient` (`rfl`). -/
theorem rayleighQuotient_def (A : Matrix n n 𝕜) (x : n → 𝕜) :
    rayleighQuotient A x = RCLike.re (quadForm A x) / RCLike.re (star x ⬝ᵥ x) := rfl

/-- Over `ℝ` the Rayleigh quotient is `quadForm A x / (x ⬝ᵥ x)` (`rfl`): the bridge to use in
real files instead of unfolding `rayleighQuotient`. -/
theorem rayleighQuotient_eq_div (A : Matrix n n ℝ) (x : n → ℝ) :
    rayleighQuotient A x = quadForm A x / (x ⬝ᵥ x) := rfl

end NLAlib
