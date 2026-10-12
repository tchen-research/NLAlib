import NLAlib.Matrix.MatrixPowerBounded

/-!
# The real matrix power toolkit with complex spectral radius

Decay, the inverse Neumann series, the exact power-boundedness criterion,
and spectral-radius-plus-epsilon growth with an explicit prefix constant.
Source: Horn–Johnson (2013), §§3.2 and 5.6.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

/-- The full real matrix power contract uses the complex spectral radius:
powers decay exactly below one, the Neumann series sums to the inverse,
bounded powers are characterized by subunit spectral radius or semisimple
peripheral eigenvalues, and every positive epsilon yields a uniform growth
bound with the defined finite-prefix constant. Source: Horn–Johnson (2013),
Theorems 3.2.5.2, 5.6.12 and 5.6.15, Lemmas 5.6.10–5.6.11 and Corollary
5.6.13; empty matrices are included.
atlas: matrix-power-convergence -/
theorem matrix_power_convergence_properties
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    (Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔
      spectralRadius ℂ (A.map Complex.ofReal) < 1) ∧
    (spectralRadius ℂ (A.map Complex.ofReal) < 1 →
      HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹) ∧
    ((∃ C : ℝ, ∀ k : ℕ, ‖A ^ k‖ ≤ C) ↔
      spectralRadius ℂ (A.map Complex.ofReal) ≤ 1 ∧
      ∀ μ : ℂ, ‖μ‖ = 1 → Module.End.maxGenEigenspace (A.map Complex.ofReal).toEuclideanLin μ =
        Module.End.eigenspace (A.map Complex.ofReal).toEuclideanLin μ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ,
      specNorm (A ^ k) ≤ matrixPowerBoundConstant (A.map Complex.ofReal)
        ((spectralRadius ℂ (A.map Complex.ofReal)).toReal + ε) N *
          ((spectralRadius ℂ (A.map Complex.ofReal)).toReal + ε) ^ k) :=
  ⟨tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one A,
    hasSum_real_matrix_pow_inv_of_complex_spectralRadius_lt_one,
    exists_bound_norm_real_matrix_pow_iff A,
    fun _ hε => exists_prefix_specNorm_real_matrix_pow_le_complex_spectralRadius_add A hε⟩

end NLAlib
