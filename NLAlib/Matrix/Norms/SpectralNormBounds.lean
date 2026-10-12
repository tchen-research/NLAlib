import NLAlib.Matrix.Norms.Core
import Mathlib.Data.Matrix.Block

/-!
# Spectral-norm bounds

Elementary spectral-norm facts that only need the definitions of `NLAlib.Matrix.Norms.Core`:

* `sqrt_mulVec_dotProduct_le_specNorm_mul`: `‖Ax‖₂ ≤ ‖A‖₂ ‖x‖₂` in the `√(v ⬝ v)` spelling;
* the reverse triangle inequality `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖₂` and its Frobenius corollary
  `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖_F` (atlas `norm-lipschitz`);
* invariance under multiplication by orthonormal frames, `‖PA‖₂ = ‖A‖₂` and `‖APᵀ‖₂ = ‖A‖₂`
  when `PᵀP = I`;
* bounds from coordinates: `‖A‖₂ ≤ C` from `∑ᵢ (Ax)ᵢ² ≤ C² ∑ⱼ xⱼ²`, `‖diag(v)‖₂ ≤ c` from
  `|vᵢ| ≤ c`, and `‖diag(A, …, A)‖₂ ≤ ‖A‖₂`.

Atlas: `norms-frob-spec`, `norm-lipschitz`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Spectral-norm control of the Euclidean length of a matrix-vector product.
Atlas: `norms-frob-spec`, `norm-lipschitz`. -/
theorem sqrt_mulVec_dotProduct_le_specNorm_mul (A : Matrix m n ℝ) (x : n → ℝ) :
    Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤ specNorm A * Real.sqrt (x ⬝ᵥ x) := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have hnAx : ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ x)‖ =
      Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, sq]
  simpa only [hnAx, ← sqrt_dotProduct_self_eq_norm, specNorm] using h

/-- Reverse triangle inequality for the spectral norm: `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖₂`.
Ported from Prove2me solution `GaussianMatrix.specNorm_lipschitz` (helper `specNorm_sub_le`).
Atlas `norm-lipschitz`. -/
theorem abs_specNorm_sub_specNorm_le (A B : Matrix m n ℝ) :
    |specNorm A - specNorm B| ≤ specNorm (A - B) :=
  abs_norm_sub_norm_le A B

/-- The spectral norm is `1`-Lipschitz for the Frobenius norm: `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖_F`
(Vershynin 2012, proof of Cor. 5.35). Generalised from `Fin N × Fin n` to arbitrary finite index
types. Ported from Prove2me solution `GaussianMatrix.specNorm_lipschitz`.
Atlas `norm-lipschitz`.
atlas: norm-lipschitz -/
theorem abs_specNorm_sub_specNorm_le_frobNorm (A B : Matrix m n ℝ) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) :=
  (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm (A - B))

/-- Multiplication by an orthonormal frame preserves the spectral norm.
Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_mul_left_of_hasOrthonormalCols {p : Type*} [Fintype p]
    [DecidableEq p] {P : Matrix m n ℝ} (hP : Pᵀ * P = 1) (A : Matrix n p ℝ) :
    specNorm (P * A) = specNorm A := by
  have hPA : P * A = P * (Pᵀ * (P * A)) := by
    rw [← Matrix.mul_assoc Pᵀ P, hP, Matrix.one_mul]
  have h := specNorm_transpose_mul_of_eq_mul hP hPA
  simpa only [← Matrix.mul_assoc, hP, Matrix.one_mul] using h.symm

/-- Right multiplication by the transpose of an orthonormal frame preserves
the spectral norm. Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_mul_transpose_right_of_hasOrthonormalCols {p : Type*}
    [Fintype p] [DecidableEq p] {P : Matrix m n ℝ} (hP : Pᵀ * P = 1)
    (A : Matrix p n ℝ) : specNorm (A * Pᵀ) = specNorm A := by
  rw [← specNorm_transpose (A * Pᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
    specNorm_mul_left_of_hasOrthonormalCols hP, specNorm_transpose]

/-- A spectral-norm bound from a bound on `‖Ax‖²`: if `0 ≤ C` and `∑ᵢ (Ax)ᵢ² ≤ C² ∑ⱼ xⱼ²` for
every `x`, then `‖A‖₂ ≤ C`. Atlas: `norms-frob-spec` (helper). -/
theorem specNorm_le_of_forall_sum_sq_mulVec_le (A : Matrix m n ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : n → ℝ, ∑ i, (A *ᵥ x) i ^ 2 ≤ C ^ 2 * ∑ j, x j ^ 2) : specNorm A ≤ C := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have h := h x.ofLp
  have hx : ∑ j, x.ofLp j ^ 2 = ‖x‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x).symm
  have hy : ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A x‖ ^ 2 =
      ∑ i, (A *ᵥ x.ofLp) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  rw [hx, ← mul_pow, ← hy] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hC (norm_nonneg x)) h

omit [Fintype m] [DecidableEq m] in
/-- `‖diag(v)‖₂ ≤ c` when every `|vᵢ| ≤ c` (`c ≥ 0`). Helper for
`subspace-iteration-convergence`. -/
theorem specNorm_diagonal_le {v : n → ℝ} {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    specNorm (Matrix.diagonal v) ≤ c := by
  rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).2 fun i => by simpa using hv i

omit [Fintype m] [DecidableEq m] in
/-- `‖diag(A, …, A)‖₂ ≤ ‖A‖₂`. Atlas: `hutchinson-tail` (helper). -/
theorem specNorm_blockDiagonal_const_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix n n ℝ) :
    specNorm (Matrix.blockDiagonal (fun _ : κ => A)) ≤ specNorm A := by
  refine specNorm_le_of_forall_sum_sq_mulVec_le _ (specNorm_nonneg A) fun x => ?_
  have hD : ∀ i k, (Matrix.blockDiagonal (fun _ : κ => A) *ᵥ x) (i, k) =
      (A *ᵥ fun j => x (j, k)) i := fun i k => by
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k
      (fun l _ hl => by simp [Matrix.blockDiagonal_apply, Ne.symm hl]) (by simp)]
    simp [Matrix.blockDiagonal_apply]
  simp only [Fintype.sum_prod_type, hD]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j k => x (j, k) ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => sum_sq_mulVec_le_specNorm_sq A _

end NLAlib
