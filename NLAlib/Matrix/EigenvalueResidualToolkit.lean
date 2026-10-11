import NLAlib.Matrix.EigenspaceProjector
import NLAlib.Matrix.RayleighDerivative

/-!
# Complete residual toolkit for symmetric eigenpairs

This declaration collects the residual inclusion, unique optimal shift,
Kato–Temple isolation bound, complete-eigenspace sine bound, and true Rayleigh
quotient derivative. Sources: Parlett §4.5, §10.6, §11.7; Saad §3.2.
Atlas: `eigenvalue-residual-bounds`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's Euclidean Rayleigh quotient is the matrix quadratic form
divided by the squared Euclidean length. Parlett §4.5, with total division
also making both sides zero at the zero vector. -/
theorem rayleighQuotient_toEuclideanCLM_eq_quadForm_div (A : Matrix n n ℝ) (x : n → ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 x) =
      quadForm A x/(x ⬝ᵥ x) := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  have hn : ‖WithLp.toLp 2 x‖^2=x ⬝ᵥ x := by
    simpa only [WithLp.ofLp_toLp, dotProduct, sq] using
      EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x : EuclideanSpace ℝ n)
  rw [hn]
  congr 1

/-- The complete approximate-eigenpair residual toolkit, including the
actual eigenspace projector and the nonzero-vector Rayleigh gradient.
Parlett §4.5, §10.6, §11.7; Saad §3.2. Finite index types may be empty, although
a unit vector itself can only exist in a nonempty space. Complementary
spectral separation is a pointwise positive lower bound, so an empty
complement is handled without an undefined minimum.
atlas: eigenvalue-residual-bounds -/
theorem eigenvalue_residual_bounds {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {x : n → ℝ} (hx : x ⬝ᵥ x=1) :
    (∀ μ : ℝ, ∃ i, |hA.eigenvalues i-μ| ≤
      Real.sqrt ((A*ᵥx-μ•x) ⬝ᵥ (A*ᵥx-μ•x))) ∧
    (∀ μ : ℝ,
      Real.sqrt ((A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x)) ≤
        Real.sqrt ((A*ᵥx-μ•x) ⬝ᵥ (A*ᵥx-μ•x)) ∧
      ((A*ᵥx-μ•x) ⬝ᵥ (A*ᵥx-μ•x) =
        (A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x) ↔ μ=quadForm A x)) ∧
    (∀ ℓ δ : ℝ, 0 < δ → |ℓ-quadForm A x| < δ →
      (∀ i, |hA.eigenvalues i-quadForm A x| < δ → hA.eigenvalues i=ℓ) →
      |ℓ-quadForm A x| ≤ ((A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x))/δ) ∧
    (∀ ℓ δ : ℝ, 0 < δ →
      (∀ i, hA.eigenvalues i ≠ ℓ → δ ≤ |hA.eigenvalues i-quadForm A x|) →
      Real.sqrt (((1-eigenvalueProjector hA ℓ)*ᵥx) ⬝ᵥ ((1-eigenvalueProjector hA ℓ)*ᵥx)) ≤
        Real.sqrt ((A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x))/δ) ∧
    (∀ y : EuclideanSpace ℝ n, y ≠ 0 →
      HasFDerivAt (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
        (innerSL ℝ ((2/‖y‖^2) • (Matrix.toEuclideanCLM (𝕜 := ℝ) A y -
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient y • y))) y) := by
  refine ⟨exists_eigenvalue_abs_sub_le_residual hA hx, ?_, ?_, ?_, ?_⟩
  · intro μ
    exact ⟨rayleigh_residual_le_shifted_residual A hx μ, shifted_residual_eq_rayleigh_residual_iff A hx μ⟩
  · intro ℓ δ hδ hℓ hiso
    exact abs_eigenvalue_sub_rayleigh_le_residual_sq_div hA hx hδ hℓ hiso
  · intro ℓ δ hδ hsep
    exact sqrt_complement_eigenvalueProjector_le_residual_div hA x hδ hsep
  · intro y hy
    exact hasFDerivAt_rayleighQuotient A hA y hy

end NLAlib
