import NLAlib.Matrix.Spectral.PowerBoundedOrbits
import NLAlib.Matrix.Spectral.MatrixPowerReal
/-!
# Power boundedness and semisimple peripheral eigenvalues

The exact finite-dimensional criterion is spectral radius at most one and
equality of generalized and ordinary eigenspaces at unit-modulus scalars.
The complex criterion also governs real matrix powers through complexification.
Source: Horn–Johnson (2013), §5.6.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Complex matrix powers are bounded exactly when the spectral radius is
at most one and every peripheral eigenvalue is semisimple, expressed as
equality of maximal generalized and ordinary eigenspaces.
Horn–Johnson (2013), §5.6; empty shapes are included.
atlas: matrix-power-convergence (partial) -/
theorem exists_bound_norm_matrix_pow_iff (A : Matrix n n ℂ) :
    (∃ C : ℝ, ∀ k : ℕ, specNorm (A ^ k) ≤ C) ↔
      spectralRadius ℂ A ≤ 1 ∧
      ∀ μ : ℂ, ‖μ‖ = 1 → Module.End.maxGenEigenspace A.toEuclideanLin μ =
        Module.End.eigenspace A.toEuclideanLin μ := by
  unfold specNorm
  let f : Module.End ℂ (EuclideanSpace ℂ n) := A.toEuclideanLin
  have hnorm (k : ℕ) : ‖LinearMap.toContinuousLinearMap (f ^ k)‖ = ‖A ^ k‖ := by
    have hp : LinearMap.toContinuousLinearMap (f ^ k) =
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A ^ k) := by
      calc
        LinearMap.toContinuousLinearMap (f ^ k) = (LinearMap.toContinuousLinearMap f) ^ k :=
          (Module.End.toContinuousLinearMap (EuclideanSpace ℂ n)).map_pow f k
        _ = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A ^ k) :=
          (map_pow (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A k).symm
    rw [hp, Matrix.l2_opNorm_toEuclideanCLM]
  have hspec (μ : ℂ) : f.HasEigenvalue μ ↔ μ ∈ spectrum ℂ A := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    change μ ∈ spectrum ℂ ((Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℂ n)) A) ↔ _
    rw [AlgEquiv.spectrum_eq]
  have hradius : (∀ μ : ℂ, f.HasEigenvalue μ → ‖μ‖ ≤ 1) ↔ spectralRadius ℂ A ≤ 1 := by
    constructor
    · intro h
      apply iSup₂_le
      intro μ hμ
      exact_mod_cast h μ ((hspec μ).mpr hμ)
    · intro h μ hμ
      have hle : (‖μ‖₊ : ENNReal) ≤ 1 :=
        (le_iSup₂ (α := ENNReal) μ ((hspec μ).mp hμ)).trans h
      exact_mod_cast hle
  have h := exists_bound_norm_pow_iff_eigenvalues_le_one_and_peripheral_semisimple f
  simpa only [hnorm, hradius] using h

open scoped Matrix.Norms.L2Operator in
/-- Real matrix powers are bounded exactly when their complexifications'
powers are bounded. Source: Horn–Johnson (2013), §5.6; finite-dimensional
complexification is bounded, and real spectral norm is bounded by the
complexified operator norm. -/
theorem exists_bound_norm_real_matrix_pow_iff_complexification (A : Matrix n n ℝ) :
    (∃ C : ℝ, ∀ k : ℕ, specNorm (A ^ k) ≤ C) ↔
      ∃ C : ℝ, ∀ k : ℕ, specNorm ((A.map Complex.ofReal) ^ k) ≤ C := by
  unfold specNorm
  let L : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ :=
    { toFun M := M.map Complex.ofReal
      map_add' M N := by ext i j; simp
      map_smul' c M := by ext i j; simp [Complex.real_smul] }
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖L.toContinuousLinearMap‖ * C, fun k => ?_⟩
    have h := L.toContinuousLinearMap.le_opNorm (A ^ k)
    change ‖(A ^ k).map Complex.ofReal‖ ≤ ‖L.toContinuousLinearMap‖ * ‖A ^ k‖ at h
    rw [map_ofReal_matrix_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hC k) (norm_nonneg L.toContinuousLinearMap))
  · rintro ⟨C, hC⟩
    refine ⟨C, fun k => ?_⟩
    have h : specNorm (A ^ k) ≤ ‖(A ^ k).map Complex.ofReal‖ :=
      (specNorm_le_specNorm_map_ofReal (𝕜 := ℂ) (A ^ k)).trans_eq (specNorm_eq_norm _)
    rw [specNorm_eq_norm, map_ofReal_matrix_pow] at h
    exact h.trans (hC k)

open scoped Matrix.Norms.L2Operator in
/-- Real matrix powers are bounded exactly when the complex spectral radius
is at most one and its peripheral complex eigenspaces are semisimple.
Source: Horn–Johnson (2013), §5.6; repeated eigenvalues and empty shapes
are included without extra hypotheses.
atlas: matrix-power-convergence -/
theorem exists_bound_norm_real_matrix_pow_iff (A : Matrix n n ℝ) :
    (∃ C : ℝ, ∀ k : ℕ, specNorm (A ^ k) ≤ C) ↔
      spectralRadius ℂ (A.map Complex.ofReal) ≤ 1 ∧
      ∀ μ : ℂ, ‖μ‖ = 1 → Module.End.maxGenEigenspace (A.map Complex.ofReal).toEuclideanLin μ =
        Module.End.eigenspace (A.map Complex.ofReal).toEuclideanLin μ := by
  unfold specNorm
  rw [exists_bound_norm_real_matrix_pow_iff_complexification, exists_bound_norm_matrix_pow_iff]

end NLAlib
