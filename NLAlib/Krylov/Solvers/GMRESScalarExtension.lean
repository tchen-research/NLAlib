import NLAlib.Krylov.Solvers.GMRESIterate
import NLAlib.Matrix.Basic.MoorePenroseScalarExtension

/-!
# Real GMRES and its complex scalar extension

The concrete least-squares iterate commutes with extension of real data. Uniqueness
of residuals then identifies the residual of every real GMRES minimizer with that of
every complex GMRES minimizer for the same data, including singular matrices.
Source: Saad--Schultz (1986), Sections 2--3; Penrose uniqueness for scalar extension.
atlas: gmres-def (partial)
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private theorem ofReal_mulVec {m k : Type*} [Fintype k] (A : Matrix m k ℝ) (v : k → ℝ) :
    (algebraMap ℝ 𝕜) ∘ (A *ᵥ v) = A.map (algebraMap ℝ 𝕜) *ᵥ ((algebraMap ℝ 𝕜) ∘ v) := by
  funext i
  exact (algebraMap ℝ 𝕜).map_mulVec A v i

/-- Real scalar extension commutes with the actual Krylov generator matrix. -/
theorem krylovMatrix_map_ofReal (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    krylovMatrix (A.map (algebraMap ℝ 𝕜)) ((algebraMap ℝ 𝕜) ∘ b) q =
      (krylovMatrix A b q).map (algebraMap ℝ 𝕜) := by
  ext i j
  have hp := map_pow ((algebraMap ℝ 𝕜).mapMatrix :
    Matrix n n ℝ →+* Matrix n n 𝕜) A (j : ℕ)
  change (A ^ (j : ℕ)).map (algebraMap ℝ 𝕜) = (A.map (algebraMap ℝ 𝕜)) ^ (j : ℕ) at hp
  simpa only [krylovMatrix, Matrix.map_apply, ← hp] using
    ((algebraMap ℝ 𝕜).map_mulVec (A ^ (j : ℕ)) b i).symm

/-- The chosen GMRES iterate for real input agrees exactly with its complex scalar
extension. This includes singular matrices and any count past the Krylov grade.
atlas: gmres-def (partial) -/
theorem gmresIterate_map_ofReal (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) :
    gmresIterate (A.map (algebraMap ℝ 𝕜)) ((algebraMap ℝ 𝕜) ∘ c)
      ((algebraMap ℝ 𝕜) ∘ x₀) q = (algebraMap ℝ 𝕜) ∘ gmresIterate A c x₀ q := by
  have hr : ((algebraMap ℝ 𝕜) ∘ c) -
      A.map (algebraMap ℝ 𝕜) *ᵥ ((algebraMap ℝ 𝕜) ∘ x₀) =
      (algebraMap ℝ 𝕜) ∘ (c - A *ᵥ x₀) := by
    rw [← ofReal_mulVec]
    funext i
    simp
  dsimp only [gmresIterate]
  rw [hr]
  simp only [krylovMatrix_map_ofReal, ← Matrix.map_mul,
    moorePenroseInverse_map_ofReal, ← ofReal_mulVec]
  funext i
  simp

/-- Every complex GMRES residual on real data is the extension of every corresponding
real GMRES residual. The iterates themselves may be nonunique for a singular matrix.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.residual_map_ofReal {A : Matrix n n ℝ} {c x₀ x : n → ℝ} {q : ℕ}
    (hx : IsGMRESIterate A c x₀ q x) {y : n → 𝕜}
    (hy : IsGMRESIterate (A.map (algebraMap ℝ 𝕜)) ((algebraMap ℝ 𝕜) ∘ c)
      ((algebraMap ℝ 𝕜) ∘ x₀) q y) :
    ((algebraMap ℝ 𝕜) ∘ c) - A.map (algebraMap ℝ 𝕜) *ᵥ y =
      (algebraMap ℝ 𝕜) ∘ (c - A *ᵥ x) := by
  rw [hy.residual_eq (isGMRESIterate_gmresIterate _ _ _ _), gmresIterate_map_ofReal,
    ← ofReal_mulVec, hx.residual_eq (isGMRESIterate_gmresIterate _ _ _ _)]
  funext i
  simp

end NLAlib
