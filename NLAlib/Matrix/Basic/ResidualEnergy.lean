import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Norms.Core
/-!+# Squared residual energy and its midpoint identity

The parallelogram law isolates the strictly convex directions of any
finite least-squares objective, including complex and rank-deficient data.
-/
noncomputable section
open Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The actual squared Euclidean residual. -/
def residualEnergy (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) : ℝ :=
  ‖WithLp.toLp 2 (A *ᵥ x - b)‖ ^ 2

/-- Exact midpoint convexity, with the entire strictness defect shown. -/
theorem residualEnergy_midpoint (A : Matrix m n 𝕜) (b : m → 𝕜) (x y : n → 𝕜) :
    4 * residualEnergy A b ((1 / 2 : 𝕜) • (x + y)) +
      ‖WithLp.toLp 2 (A *ᵥ (x - y))‖ ^ 2 =
        2 * residualEnergy A b x + 2 * residualEnergy A b y := by
  have hr : A *ᵥ ((1 / 2 : 𝕜) • (x + y)) - b =
      (1 / 2 : 𝕜) • ((A *ᵥ x - b) + (A *ᵥ y - b)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add]
    module
  have hd : A *ᵥ (x - y) = (A *ᵥ x - b) - (A *ᵥ y - b) := by
    rw [Matrix.mulVec_sub]; abel
  unfold residualEnergy
  rw [hr, hd, WithLp.toLp_smul, norm_smul, norm_div, norm_one, RCLike.norm_two]
  have he := parallelogram_law_with_norm 𝕜 (WithLp.toLp 2 (A *ᵥ x - b))
    (WithLp.toLp 2 (A *ᵥ y - b))
  rw [← WithLp.toLp_add, ← WithLp.toLp_sub] at he
  nlinarith [he]

/-- Equal globally minimal residual energies have exactly the same fit. -/
theorem mulVec_eq_of_residualEnergy_minimizers (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x y : n → 𝕜) (hx : ∀ z, residualEnergy A b x ≤ residualEnergy A b z)
    (hy : residualEnergy A b y ≤ residualEnergy A b x) : A *ᵥ (x - y) = 0 := by
  have hm := hx ((1 / 2 : 𝕜) • (x + y))
  have he := residualEnergy_midpoint A b x y
  have hn : ‖WithLp.toLp 2 (A *ᵥ (x - y))‖ = 0 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (A *ᵥ (x - y)))]
  exact congrArg WithLp.ofLp (norm_eq_zero.mp hn)

end NLAlib
