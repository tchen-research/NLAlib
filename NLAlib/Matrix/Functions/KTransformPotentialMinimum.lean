import NLAlib.Matrix.Functions.KTransformStableInverse
import NLAlib.Matrix.Functions.KTransformStableImage
import NLAlib.Matrix.Functions.KTransformPotentialFrechet
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Global minimization of the actual K potential

The actual stable K-image is convex. Its native inverse transports an
affine target segment to a genuine differentiable matrix path. The
original strict Frobenius derivative test makes the potential monotone
along this path, proving the global minimum on the original domain.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- A genuine stable scalar K solution globally minimizes the actual
source potential over its entire original strict stable domain. The
global minimum follows from convexity of the actual K-image, native
inverse differentiation and the original Frobenius stability test.
Source: Montanari--Saeed (2026), Theorem 2 and equation (49).
atlas: block-wishart-log-potential (partial) -/
theorem matrixKPotential_le_of_stable_scalar_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (u : ℝ) (S : M)
    (hS : S ∈ matrixKStableDomain ν α)
    (hKS : matrixKTransform ν α S = (u : ℂ) • 1)
    (Q : M) (hQ : Q ∈ matrixKStableDomain ν α) :
    matrixKPotential ν α u S ≤ matrixKPotential ν α u Q := by
  let U : M := (u : ℂ) • 1
  let H : M := matrixKTransform ν α Q - U
  have hU : U.IsHermitian := by simp [U, Matrix.IsHermitian]
  have hKQ : (matrixKTransform ν α Q).IsHermitian := by
    have hdom : Q ∈ matrixKTransformDomain ν :=
      ⟨hQ.1.isUnit, fun T hT => isUnit_matrixKDenominator Q T.val hQ.1 (hQ.2.1 T hT)⟩
    unfold Matrix.IsHermitian
    rw [← matrixKTransform_conjTranspose ν α Q hdom, hQ.1.isHermitian.eq]
  have hH : H.IsHermitian := hKQ.sub hU
  have hUm : U ∈ (matrixKTransform ν α) '' matrixKStableDomain ν α := ⟨S, hS, hKS⟩
  have heUH : U + H = matrixKTransform ν α Q := by dsimp only [H]; abel
  have hUH : U + H ∈ (matrixKTransform ν α) '' matrixKStableDomain ν α := by
    rw [heUH]; exact mem_image_of_mem (matrixKTransform ν α) hQ
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      U + t • H ∈ (matrixKTransform ν α) '' matrixKStableDomain ν α :=
    (convex_image_matrixKTransform_stableDomain ν hν α hα).add_smul_mem hUm hUH ht
  let P : ℝ → M := fun t => matrixKStableInverse ν α (U + t • H)
  let f : ℝ → ℝ := fun t => matrixKPotential ν α u (P t)
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∃ d : ℝ, HasDerivAt f d t ∧ 0 ≤ d := by
    obtain ⟨B, hB, hPd, hDB⟩ :=
      exists_hasDerivAt_matrixKStableInverse_affine ν hν α hα U H hH t (hpath t ht)
    obtain ⟨hPt, hKPt⟩ := matrixKStableInverse_mem_and_transform_eq ν α (hpath t ht)
    have hp := (hasFDerivAt_matrixKPotential ν hν α u hα.ne' (P t)
      hPt.1 hPt.2.1).comp_hasDerivAt t hPd
    have hdiff : matrixKTransform ν α (P t) - (u : ℂ) • 1 = t • H := by
      rw [hKPt]; change U + t • H - U = t • H; abel
    have hd : HasDerivAt f (α * t * (H * B).trace.re) t := by
      change HasDerivAt (fun r => matrixKPotential ν α u (P r))
        (α * ((matrixKTransform ν α (P t) - (u : ℂ) • 1) * B).trace.re) t at hp
      convert! hp using 1
      rw [hdiff, Matrix.smul_mul, Matrix.trace_smul]
      simp only [Complex.smul_re, smul_eq_mul]
      ring
    have hnonneg : 0 ≤ (H * B).trace.re := by
      by_cases hB0 : B = 0
      · simp only [hB0, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, le_refl]
      · have hpos := hPt.2.2 B hB hB0
        rw [hDB, frobInner_eq_trace, hB.eq, Matrix.trace_mul_comm] at hpos
        exact hpos.le
    exact ⟨_, hd, mul_nonneg (mul_nonneg hα.le ht.1) hnonneg⟩
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := fun t ht =>
    (hD t ht).choose_spec.1.continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) 1)) := fun t ht =>
    (hD t (interior_subset ht)).choose_spec.1.differentiableAt.differentiableWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hc hd fun t ht => by
      obtain ⟨d, hdt, hd0⟩ := hD t (interior_subset ht)
      rwa [hdt.deriv]
  have hend := hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_le_one
  have hP0 : P 0 = S := by
    change matrixKStableInverse ν α (U + (0 : ℝ) • H) = S
    rw [zero_smul, add_zero, show U = matrixKTransform ν α S from hKS.symm]
    exact matrixKStableInverse_matrixKTransform ν hν α hα S hS
  have hP1 : P 1 = Q := by
    change matrixKStableInverse ν α (U + (1 : ℝ) • H) = Q
    rw [one_smul, heUH]
    exact matrixKStableInverse_matrixKTransform ν hν α hα Q hQ
  simpa only [f, hP0, hP1] using hend

end NLAlib
