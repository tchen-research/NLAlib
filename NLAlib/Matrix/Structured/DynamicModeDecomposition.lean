import NLAlib.Matrix.Basic.MoorePenrose
import NLAlib.Matrix.Spectral.ThinSVD
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
/-!
# Exact and projected dynamic mode decomposition

The exact fit criterion is kernel inclusion, at every rank.  The reduced and
ambient products have the same nonzero spectrum, with algebraic multiplicities,
and their eigenvectors are related by the usual exact-mode lifting map.

Sources: Tu et al. (2014), §2; the matrix-toolkit re-derivation, §§61–62.
Atlas: `dmd-linear-consistency`, `dmd-reduced-eigenpair-lifting`.
-/

noncomputable section
open scoped Matrix
open Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
variable [DecidableEq n] [DecidableEq m] [DecidableEq r]

/-- The minimum-norm snapshot least-squares operator, defined at every rank. -/
def dmdOperator (X Y : Matrix n m 𝕜) : Matrix n n 𝕜 :=
  Y * moorePenroseInverse X

/-- The exact-mode lifting map from a retained positive singular block:
`B = Y V diag(σ⁻¹)`. Retaining fewer than all positive singular values
defines truncated DMD; no equality with the full pseudoinverse is presumed. -/
def dmdModeMap (Y : Matrix n m 𝕜) (V : Matrix m r 𝕜) (σ : r → ℝ) : Matrix n r 𝕜 :=
  Y * V * diagonal (fun i => ((σ i)⁻¹ : 𝕜))

/-- With the entire thin SVD, the exact-mode factorization equals full
Moore–Penrose DMD. This bridge does not assert that an arbitrary truncation
equals full DMD. Tu et al. (2014), §2.
atlas: dmd-reduced-eigenpair-lifting (partial) -/
theorem IsThinSVD.dmdOperator_eq {X : Matrix n m 𝕜} {U : Matrix n r 𝕜}
    {V : Matrix m r 𝕜} {σ : r → ℝ} (h : IsThinSVD X U V σ) (Y : Matrix n m 𝕜) :
    dmdOperator X Y = dmdModeMap Y V σ * Uᴴ := by
  rw [dmdOperator, h.moorePenroseInverse_eq, dmdModeMap]
  simp only [Matrix.mul_assoc]

/-- The snapshot residual is the component of the output snapshots on the
kernel of the input snapshot map. Tu et al. (2014), §2.
atlas: dmd-linear-consistency (partial) -/
theorem sub_dmdOperator_mul (X Y : Matrix n m 𝕜) :
    Y - dmdOperator X Y * X = Y * (1 - moorePenroseInverse X * X) := by
  simp [dmdOperator, Matrix.mul_sub, Matrix.mul_assoc]

/-- Exact DMD fits all snapshots precisely when every input dependence is an
output dependence. This includes zero and rank-deficient snapshot matrices.
Tu et al. (2014), linear consistency theorem.
atlas: dmd-linear-consistency (partial) -/
theorem dmdOperator_mul_eq_iff (X Y : Matrix n m 𝕜) :
    dmdOperator X Y * X = Y ↔
      LinearMap.ker X.mulVecLin ≤ LinearMap.ker Y.mulVecLin := by
  constructor
  · intro h v hv
    change X *ᵥ v = 0 at hv
    change Y *ᵥ v = 0
    rw [← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · intro h
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have hx : X *ᵥ (v - (moorePenroseInverse X * X) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
        ← Matrix.mul_assoc, mul_moorePenroseInverse_mul, sub_self]
    have hy : Y *ᵥ (v - (moorePenroseInverse X * X) *ᵥ v) = 0 := h hx
    rw [Matrix.mulVec_sub] at hy
    simpa [dmdOperator, Matrix.mul_assoc, Matrix.mulVec_mulVec] using
      (sub_eq_zero.mp hy).symm

/-- Every exact fitting operator agrees with DMD on the input snapshot range.
The fitting hypothesis is precisely the data equation, not a rank assumption.
atlas: dmd-linear-consistency (partial) -/
theorem mulVec_eq_dmdOperator_of_mem_range {X Y : Matrix n m 𝕜}
    (h : LinearMap.ker X.mulVecLin ≤ LinearMap.ker Y.mulVecLin)
    {F : Matrix n n 𝕜} (hF : F * X = Y) {v : n → 𝕜}
    (hv : v ∈ LinearMap.range X.mulVecLin) :
    F *ᵥ v = dmdOperator X Y *ᵥ v := by
  obtain ⟨u, rfl⟩ := hv
  change F *ᵥ (X *ᵥ u) = dmdOperator X Y *ᵥ (X *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hF,
    (dmdOperator_mul_eq_iff X Y).mpr h]

/-- For sequential, linearly consistent snapshots, DMD reproduces every
snapshot by powers of one operator, including the final output snapshot.
Tu et al. (2014), §2.
atlas: dmd-linear-consistency (partial) -/
theorem dmdOperator_pow_mulVec_snapshot {m : ℕ} (x : ℕ → n → 𝕜)
    (hc : LinearMap.ker (Matrix.mulVecLin (fun i (j : Fin m) => x j i)) ≤
      LinearMap.ker (Matrix.mulVecLin (fun i (j : Fin m) => x (j + 1) i)))
    {j : ℕ} (hj : j ≤ m) :
    (dmdOperator (fun i (j : Fin m) => x j i)
      (fun i (j : Fin m) => x (j + 1) i)) ^ j *ᵥ x 0 = x j := by
  let A := dmdOperator (fun i (j : Fin m) => x j i)
    (fun i (j : Fin m) => x (j + 1) i)
  have hfit := (dmdOperator_mul_eq_iff (fun i (j : Fin m) => x j i)
    (fun i (j : Fin m) => x (j + 1) i)).mpr hc
  have hstep (k : ℕ) (hk : k < m) : A *ᵥ x k = x (k + 1) := by
    funext i
    exact congr_fun (congr_fun hfit i) (⟨k, hk⟩ : Fin m)
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
    exact hstep j (by omega)

/-- Ambient and reduced DMD have the same nonzero characteristic roots with
their algebraic multiplicities. This is the rectangular product identity and
therefore also applies to any retained positive SVD block.
atlas: dmd-reduced-eigenpair-lifting (partial) -/
theorem charpoly_mul_conjTranspose_eq (B U : Matrix n r 𝕜)
    (hr : Fintype.card r ≤ Fintype.card n) :
    (B * Uᴴ).charpoly = Polynomial.X ^ (Fintype.card n - Fintype.card r) *
      (Uᴴ * B).charpoly :=
  Matrix.charpoly_mul_comm_of_le B Uᴴ hr

/-- A nonzero reduced eigenvalue lifts to a nonzero exact DMD mode `Bw`.
Tu et al. (2014), exact DMD eigenvector formula.
atlas: dmd-reduced-eigenpair-lifting (partial) -/
theorem mulVec_eigenvector_lift {B U : Matrix n r 𝕜} {w : r → 𝕜} {μ : 𝕜}
    (hμ : μ ≠ 0) (hw : w ≠ 0) (he : (Uᴴ * B) *ᵥ w = μ • w) :
    B *ᵥ w ≠ 0 ∧ (B * Uᴴ) *ᵥ (B *ᵥ w) = μ • (B *ᵥ w) := by
  constructor
  · intro hz
    have : μ • w = 0 := by rw [← he, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    exact hw ((smul_eq_zero.mp this).resolve_left hμ)
  · rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec w Uᴴ B, he, Matrix.mulVec_smul]

/-- Every ambient eigenmode at a nonzero eigenvalue has a nonzero reduced
mode, obtained by applying the retained left singular vectors' adjoint.
atlas: dmd-reduced-eigenpair-lifting (partial) -/
theorem mulVec_eigenvector_reduce {B U : Matrix n r 𝕜} {v : n → 𝕜} {μ : 𝕜}
    (hμ : μ ≠ 0) (hv : v ≠ 0) (he : (B * Uᴴ) *ᵥ v = μ • v) :
    Uᴴ *ᵥ v ≠ 0 ∧ (Uᴴ * B) *ᵥ (Uᴴ *ᵥ v) = μ • (Uᴴ *ᵥ v) := by
  constructor
  · intro hz
    have : μ • v = 0 := by rw [← he, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    exact hv ((smul_eq_zero.mp this).resolve_left hμ)
  · rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec v B Uᴴ, he, Matrix.mulVec_smul]

/-- The projected-mode defect is exactly the component of `Bw` perpendicular
to the retained subspace. This explains the difference between projected and
exact DMD modes.
atlas: dmd-reduced-eigenpair-lifting (partial) -/
theorem mulVec_projected_mode_sub {B U : Matrix n r 𝕜} {w : r → 𝕜} {μ : 𝕜}
    (hU : HasOrthonormalCols U) (he : (Uᴴ * B) *ᵥ w = μ • w) :
    (B * Uᴴ) *ᵥ (U *ᵥ w) - μ • (U *ᵥ w) =
      (1 - U * Uᴴ) *ᵥ (B *ᵥ w) := by
  have hUU : Uᴴ * U = 1 := hU
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hUU, Matrix.mul_one,
    Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec w Uᴴ B, he, Matrix.mulVec_smul]

end NLAlib
