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
* bounds from coordinates: `‖A‖₂ ≤ c` from `(Ax) ⬝ (Ax) ≤ c² (x ⬝ x)`, `‖diag(v)‖₂ ≤ c` from
 `|vᵢ| ≤ c`, and `‖diag(A, …, A)‖₂ ≤ ‖A‖₂`.

Atlas: `norms-frob-spec`, `norm-lipschitz`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
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

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- Reverse triangle inequality for the spectral norm: `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖₂`.
specNorm_lipschitz` (helper `specNorm_sub_le`).
Atlas `norm-lipschitz`. -/
theorem abs_specNorm_sub_specNorm_le (A B : Matrix m n ℝ) :
    |specNorm A - specNorm B| ≤ specNorm (A - B) :=
  abs_norm_sub_norm_le A B

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- The spectral norm is `1`-Lipschitz for the Frobenius norm: `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖_F`
(Vershynin 2012, proof of Cor. 5.35). Generalised from `Fin N × Fin n` to arbitrary finite index
types. specNorm_lipschitz`.
Atlas `norm-lipschitz`.
atlas: norm-lipschitz -/
theorem abs_specNorm_sub_specNorm_le_frobNorm (A B : Matrix m n ℝ) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) :=
  (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm (A - B))

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- Multiplication by a frame with orthonormal columns (`PᴴP = 1`) preserves the spectral
norm, over `ℝ` or `ℂ`. Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_mul_left_of_hasOrthonormalCols {𝕜 : Type*} [RCLike 𝕜] {p : Type*}
    [Fintype p] [DecidableEq p] {P : Matrix m n 𝕜} (hP : HasOrthonormalCols P)
    (A : Matrix n p 𝕜) : specNorm (P * A) = specNorm A := by
  have hP' : Pᴴ * P = 1 := hP.conjTranspose_mul_self
  have hPA : P * A = P * (Pᴴ * (P * A)) := by
    rw [← Matrix.mul_assoc Pᴴ P, hP', Matrix.one_mul]
  have h := specNorm_conjTranspose_mul_of_eq_mul hP' hPA
  simpa only [← Matrix.mul_assoc, hP', Matrix.one_mul] using h.symm

open scoped Matrix.Norms.L2Operator in
/-- Right multiplication by the conjugate transpose of a frame with orthonormal columns
(`PᴴP = 1`) preserves the spectral norm, over `ℝ` or `ℂ`. Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_mul_conjTranspose_right_of_hasOrthonormalCols {𝕜 : Type*} [RCLike 𝕜]
    {p : Type*} [Fintype p] [DecidableEq p] {P : Matrix m n 𝕜} (hP : HasOrthonormalCols P)
    (A : Matrix p n 𝕜) : specNorm (A * Pᴴ) = specNorm A := by
  rw [← specNorm_conjTranspose (A * Pᴴ), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, specNorm_mul_left_of_hasOrthonormalCols hP,
    specNorm_conjTranspose]

/-- Right multiplication by the transpose of a real frame with orthonormal columns preserves the
spectral norm (`specNorm_mul_conjTranspose_right_of_hasOrthonormalCols` at `ℝ`, with `Pᴴ = Pᵀ`).
Kept for the real consumers of the transpose spelling. -/
theorem specNorm_mul_transpose_right_of_hasOrthonormalCols {p : Type*} [Fintype p]
    [DecidableEq p] {P : Matrix m n ℝ} (hP : HasOrthonormalCols P) (A : Matrix p n ℝ) :
    specNorm (A * Pᵀ) = specNorm A := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hP A

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- A squared Euclidean vector bound controls the spectral norm: if `0 ≤ c` and
`(Ax) ⬝ (Ax) ≤ c² (x ⬝ x)` for every `x`, then `‖A‖₂ ≤ c`. This is the defining operator
supremum; used for Sylvester separation, projection gaps and block-diagonal bounds.
Atlas: `norms-frob-spec` (helper). -/
theorem specNorm_le_of_mulVec_sq_le {A : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → ℝ, (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ c ^ 2 * (x ⬝ᵥ x)) :
    specNorm A ≤ c := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have hh := h x.ofLp
  have hx : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
    simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq x).symm
  have hy : ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A x‖ ^ 2 =
      (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, sq]
    rfl
  rw [hx, ← hy, ← mul_pow] at hh
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hc (norm_nonneg x)) hh

open scoped Matrix.Norms.L2Operator in
omit [Fintype m] [DecidableEq m] in
/-- `‖diag(v)‖₂ ≤ c` when every `|vᵢ| ≤ c` (`c ≥ 0`). Helper for
`subspace-iteration-convergence`. -/
theorem specNorm_diagonal_le {v : n → ℝ} {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    specNorm (Matrix.diagonal v) ≤ c := by
  rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).2 fun i => by simpa using hv i

open scoped Matrix.Norms.L2Operator in
omit [Fintype m] [DecidableEq m] in
/-- `‖diag(A, …, A)‖₂ ≤ ‖A‖₂`. Atlas: `hutchinson-tail` (helper). -/
theorem specNorm_blockDiagonal_const_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix n n ℝ) :
    specNorm (Matrix.blockDiagonal (fun _ : κ => A)) ≤ specNorm A := by
  refine specNorm_le_of_mulVec_sq_le (specNorm_nonneg A) fun x => ?_
  simp only [dotProduct, ← sq]
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

open scoped Matrix.Norms.L2Operator in
omit [Fintype m] [DecidableEq m] in
/-- A diagonal entry is bounded by the spectral norm: `|Aᵢᵢ| ≤ ‖A‖₂`.
Moved from the Hanson–Wright chain (HighDimProb commit c0cb8d9); atlas `hanson-wright` (helper). -/
theorem abs_diag_le_specNorm (A : Matrix n n ℝ) (i : n) :
    |A i i| ≤ specNorm A := by
  let e : EuclideanSpace ℝ n := EuclideanSpace.single i (1 : ℝ)
  have hcoord :
      |A i i| ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A e‖ := by
    have h :=
      PiLp.norm_apply_le
        (x := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A e) i
    simpa [e, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one, Real.norm_eq_abs]
      using h
  have hop :=
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm e
  have he_norm : ‖e‖ = 1 := by
    simp [e]
  calc
    |A i i| ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A e‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ * ‖e‖ := hop
    _ = specNorm A := by
      rw [he_norm, mul_one]
      rfl

end NLAlib
