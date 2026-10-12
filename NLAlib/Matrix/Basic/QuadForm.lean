import Mathlib.Data.Real.Star
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Quadratic forms

`NLAlib.quadForm A z = zᵀ A z` and its algebraic API: the expansion as a double sum
(`quadForm_eq_sum`) and of its square (`quadForm_sq_eq_sum`), invariance under relabelling
(`quadForm_reindex`), the polarisation expansion on two vectors (`quadForm_smul_add_smul`), the
rank-one form (`quadForm_vecMulVec_self`), congruence (`quadForm_transpose_mul_mul`) and the
normal-equations form (`quadForm_transpose_mul_self`); and the Rayleigh quotient
`rayleighQuotient A x = xᵀAx / xᵀx`. Layer 0: used by the Krylov layer (spectral measure, CG
energy norm, power method) and by the estimators in `NLAlib.Estimation.Trace.Hutchinson`.

Atlas: `hutchinson-unbiased`, `hutchinson-variance`, `spectral-measure` (definition used in their
statements).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The quadratic form `zᵀ A z`. Atlas: `hutchinson-unbiased`, `hutchinson-variance`.
atlas: quadform-def -/
def quadForm (A : Matrix n n ℝ) (z : n → ℝ) : ℝ := z ⬝ᵥ (A *ᵥ z)

/-- `0ᵀ A 0 = 0` (`@[simp]`). Atlas: `hutchinson-unbiased` (helper). -/
@[simp] theorem quadForm_zero_right (A : Matrix n n ℝ) : quadForm A 0 = 0 := by
  simp [quadForm]

/-- Expansion `zᵀ A z = ∑ᵢ ∑ⱼ A_ij z_i z_j`. Atlas: `hutchinson-unbiased` (helper). -/
theorem quadForm_eq_sum (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z = ∑ i, ∑ j, A i j * (z i * z j) := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Expansion `(zᵀ A z)² = ∑ᵢⱼₖₗ A_ij A_kl z_i z_j z_k z_l`. Atlas: `hutchinson-variance`
(helper). -/
theorem quadForm_sq_eq_sum (A : Matrix n n ℝ) (z : n → ℝ) :
    quadForm A z ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (z i * z j * z k * z l) := by
  rw [sq, quadForm_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Relabelling the coordinates by an equivalence does not change the quadratic form.
Atlas `hanson-wright` (index transport). -/
theorem quadForm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (e : ι ≃ κ)
    (z : ι → ℝ) : quadForm (A.reindex e e) (fun k => z (e.symm k)) = quadForm A z := by
  rw [quadForm_eq_sum, quadForm_eq_sum]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun i => ∑ k, A i (e.symm k) * (z i * z (e.symm k)))]
  exact Finset.sum_congr rfl fun i _ =>
    e.symm.sum_comp (fun j => A i j * (z i * z j))

/-- Expanding a real symmetric quadratic form on two scaled vectors gives
the diagonal energies and twice the cross term. Horn--Johnson (2013),
Section 7.4.12; helper for Wielandt's inequality. -/
theorem quadForm_smul_add_smul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x y : n → ℝ) (r s : ℝ) :
    quadForm A (r • x + s • y) = r ^ 2 * quadForm A x +
      2 * r * s * (x ⬝ᵥ A *ᵥ y) + s ^ 2 * quadForm A y := by
  have hAt : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hcross : y ⬝ᵥ A *ᵥ x = x ⬝ᵥ A *ᵥ y := by
    simpa only [hAt] using Matrix.dotProduct_transpose_mulVec A y x
  simp only [quadForm, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, hcross]
  ring

/-- The quadratic form of a real rank-one Gram matrix is the squared
dot product with its defining vector. Horn--Johnson (2013), Section 7.1;
helper for finite exponential certificates. -/
theorem quadForm_vecMulVec_self (b x : n → ℝ) :
    quadForm (Matrix.vecMulVec b b) x = (x ⬝ᵥ b) ^ 2 := by
  simp [quadForm, Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_comm, sq]

/-- Congruence: `quadForm (WᵀAW) v = quadForm A (Wv)` for a rectangular `W`. Helper for
`preconditioned-cg` and `ostrowski-congruence-eigenvalues` (Horn–Johnson 2013, Theorem 4.5.9). -/
theorem quadForm_transpose_mul_mul {k : Type*} [Fintype k] (A : Matrix n n ℝ)
    (W : Matrix n k ℝ) (v : k → ℝ) :
    quadForm (Wᵀ * A * W) v = quadForm A (W *ᵥ v) := by
  simp only [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Wᵀ,
    Matrix.vecMul_transpose]

/-- `(Aᵀ A y) ⬝ y = ‖A y‖²`: the quadratic form of the normal-equations matrix.
Helper for `cgls-lsqr-bound`. -/
theorem quadForm_transpose_mul_self {m : Type*} [Fintype m] (A : Matrix m n ℝ) (y : n → ℝ) :
    quadForm (Aᵀ * A) y = (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
  rw [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The Rayleigh quotient `ρ(x) = xᵀAx/xᵀx` (junk value `0` at `x = 0`). Source: Trefethen–Bau
(1997) [`tb97`], Lect. 27. Helper for `power-iteration`; Mathlib's
`ContinuousLinearMap.rayleighQuotient` of `Matrix.toEuclideanCLM A` agrees with it
(`rayleighQuotient_toEuclideanCLM_eq`). -/
def rayleighQuotient (A : Matrix n n ℝ) (x : n → ℝ) : ℝ := quadForm A x / (x ⬝ᵥ x)

end NLAlib
