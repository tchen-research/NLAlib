import NLAlib.Matrix.Functions.OrderedExponential
import NLAlib.ForMathlib.Analysis.CStarAlgebra.AbsFirstOrder
import NLAlib.ForMathlib.Analysis.Normed.Algebra.EulerPower
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The first-order modulus of an ordered exponential product

The actual matrix absolute value has the same first-order generator as the
ordered product along positive reciprocal integer times. This is the input
to an Euler-power limit, rather than an assumed Lie--Trotter conclusion.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, (28), Corollary 3.3.
-/

noncomputable section

open Matrix Complex Filter
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Native differentiability gives the genuine rescaled ordered-product
limit along reciprocal integer times. -/
theorem tendsto_natCast_smul_orderedMatrixExp_sub_one (H : List (Matrix n n ℂ)) :
    Tendsto (fun k : ℕ => (k : ℝ) • (orderedMatrixExp H (k : ℂ)⁻¹ - 1)) atTop (𝓝 H.sum) := by
  have hzero : Tendsto (fun k : ℕ => (k : ℂ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hne : ∀ᶠ k : ℕ in atTop, (k : ℂ)⁻¹ ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hparam : Tendsto (fun k : ℕ => (k : ℂ)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hne⟩
  have h := (hasDerivAt_orderedMatrixExp_zero H).tendsto_slope_zero.comp hparam
  simp only [zero_add, orderedMatrixExp_zero, inv_inv, Function.comp_def] at h
  simpa only [← Complex.coe_smul, Complex.ofReal_natCast] using h

/-- The actual CFC absolute values, with the same rescaling, converge to
the Hermitian sum. This discharges the matrix-specific hypothesis in the
subsequent generic Euler-power theorem. -/
theorem tendsto_nsmul_abs_orderedMatrixExp_sub_one (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) :
    Tendsto (fun k : ℕ => k • (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹) - 1)) atTop (𝓝 H.sum) := by
  have hp : Tendsto (fun k : ℕ => orderedMatrixExp H (k : ℂ)⁻¹) atTop (𝓝 1) := by
    have h := (analyticAt_orderedMatrixExp H 0).continuousAt.tendsto.comp
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    simpa only [Function.comp_def, orderedMatrixExp_zero] using h
  have hsum : IsSelfAdjoint H.sum := by
    clear hp
    induction H with
    | nil => change star (0 : Matrix n n ℂ) = 0; simp
    | cons A H ih =>
      exact (hH A (by simp)).isSelfAdjoint.add (ih (fun B hB => hH B (by simp [hB])))
  have h := CFC.tendsto_smul_abs_sub_one_of_tendsto_smul_sub_one hp
    (tendsto_natCast_smul_orderedMatrixExp_sub_one H) hsum
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- The genuine ordered-product modulus powers converge to the exponential
of the Hermitian sum. This is the actual matrix limit used in the
multivariate Golden--Thompson deduction, not an assumed product formula.
atlas: multivariate-golden-thompson (partial) -/
theorem tendsto_abs_orderedMatrixExp_pow
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) :
    Tendsto (fun k : ℕ => (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹)) ^ k) atTop
      (𝓝 (matrixExp H.sum)) := by
  by_cases hn : Nonempty n
  · let := hn
    apply NormedSpace.tendsto_pow_exp_of_tangent
    simpa only [Nat.cast_smul_eq_nsmul] using tendsto_nsmul_abs_orderedMatrixExp_sub_one H hH
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have heq : (fun k : ℕ => (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹)) ^ k) =
        (fun _ : ℕ => matrixExp H.sum) := funext fun _ => Subsingleton.elim _ _
    rw [heq]
    exact tendsto_const_nhds

end NLAlib
