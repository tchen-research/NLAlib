import NLAlib.Matrix.Norms
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The real to complex operator norm bridge

Embedding real vectors preserves their Euclidean norm. Restricting the
complex operator to real vectors bounds the real operator norm, supporting
the real classical SRHT conclusion from complex matrix Chernoff.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- Real vectors embedded in complex coordinates have the same Euclidean
norm. Source: entrywise squared norms; supports atlas `srht-ose`. -/
theorem norm_toLp_ofReal_eq {n : Type*} [Fintype n] (x : n → ℝ) :
    ‖(WithLp.toLp 2 (fun j => (x j : ℂ)) : EuclideanSpace ℂ n)‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Complex.norm_real]

/-- The real operator norm is bounded by the norm of its complex extension.
Source: restricting a complex operator to real vectors; supports `srht-ose`. -/
theorem specNorm_le_spectralNorm_map_ofReal
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : specNorm A ≤ ‖A.map Complex.ofReal‖ := by
  rw [specNorm_eq_norm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (A.map Complex.ofReal).l2_opNorm_mulVec
    (WithLp.toLp 2 (fun j => (x.ofLp j : ℂ)) : EuclideanSpace ℂ n)
  have hv : A.map Complex.ofReal *ᵥ (fun j => (x.ofLp j : ℂ)) =
      fun i => ((A *ᵥ x.ofLp) i : ℂ) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum,
      Complex.ofReal_mul]
  rw [hv] at h
  change ‖(WithLp.toLp 2 (fun i => ((A *ᵥ x.ofLp) i : ℂ)) : EuclideanSpace ℂ m)‖ ≤
    ‖A.map Complex.ofReal‖ * ‖(WithLp.toLp 2 (fun j => (x.ofLp j : ℂ)) : EuclideanSpace ℂ n)‖ at h
  rw [norm_toLp_ofReal_eq, norm_toLp_ofReal_eq] at h
  exact h

end NLAlib
