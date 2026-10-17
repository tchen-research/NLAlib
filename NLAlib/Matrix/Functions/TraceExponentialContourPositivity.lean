import NLAlib.ForMathlib.Analysis.Complex.CircleMomentPositivity
import NLAlib.Matrix.Functions.TraceExponentialInverseContour
import NLAlib.Matrix.Functions.TraceExponentialDensityMeasure
import NLAlib.Matrix.Perturbation.PencilRootSumExtension

/-!
# Nonnegativity of Stahl's contour density

The inverse spectral branches identify the density with an exterior exponential
moment of the actual upper-root sum. That sum is holomorphic through collisions,
has nonnegative imaginary part in the upper half-plane, and is uniformly bounded
on compact parameter sets. Smooth contour flattening proves nonnegativity of
the density away from the finitely many slopes. The existing atom-plus-density
identity then constructs a positive measure for each simple diagonal pencil.
Source: Stahl (2013), Theorem 2, reorganized by the planar root-sum argument.
The associated atlas target is `trace-exponential-stahl`.
-/

noncomputable section

open Complex Set Metric Filter MeasureTheory
open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact fixed-circle density is nonnegative away from the finitely many
slopes. The proof constructs the inverse branches and actual upper-root sum;
neither a positive-density assumption nor a representing measure is used.
Source: Stahl (2013), Theorem 2, planar root-sum proof.
atlas: trace-exponential-stahl (partial) -/
theorem traceExponentialCircleDensity_re_nonneg_of_exterior_branches
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b)
    {R ρ : ℝ} {forward : n → ℂ → ℂ}
    (hforward : ∀ i, DifferentiableOn ℂ (forward i) {z | R < ‖z‖} ∧
      Tendsto (fun z => forward i z + (b i : ℂ) * z)
        (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hρ : 0 < ρ) (hRρ : R < ρ) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    0 ≤ (traceExponentialCircleDensity forward b ρ s).re := by
  classical
  obtain ⟨S, hS, inverse, hinverse, hinverseSpec, _, href, hroot⟩ :=
    exists_exterior_inverse_eigenvalue_branches_root_sum hA b hb s hs
  obtain ⟨h, hdiff, hext, _, hconj, him, hbound⟩ :=
    exists_inversePencilUpperRootSum_extension hA b s hs inverse
      (fun i => (hinverse i).1) (fun u hu => (hinverseSpec u hu).1) hroot href
  have hmoment := eventually_circleDensity_eq_neg_circleIntegral_of_exterior_inverse_branches
    A b hb s hs hforward hforwardSpec hinverse (fun u hu => (hinverseSpec u hu).1) hρ hRρ
  obtain ⟨M, hmoment, hMS, hM⟩ :=
    (hmoment.and ((eventually_gt_atTop S).and (eventually_gt_atTop (0 : ℝ)))).exists
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))
  let C := (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + (M + 1))
  have hball : ∀ z : ℂ, ‖z‖ ≤ M + 1 → ‖h z‖ ≤ C := by
    intro z hz
    exact (hbound z).trans (mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (Nat.cast_nonneg _) (specNorm_nonneg _)))
  have hpositive := Complex.neg_normalized_exp_circleIntegral_re_nonneg hM hMS
    hdiff hconj him hball
  have hdensity : traceExponentialCircleDensity forward b ρ s =
      -(2 * Real.pi * I : ℂ)⁻¹ * (∮ u in C(0, M), exp u * h u) := by
    rw [hmoment]
    congr 1
    apply circleIntegral.integral_congr hM.le
    intro u hu
    have hnorm : ‖u‖ = M := by simpa only [mem_sphere, dist_zero_right] using hu
    dsimp only
    rw [hext u (by rwa [hnorm])]
  rw [hdensity]
  simpa only [neg_mul] using hpositive

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian pencil with distinct real diagonal slopes has a positive finite
exponential representing measure on every closed interval containing those
slopes. Density positivity is proved by the planar root-sum argument, and the
atoms and density give the actual measure.
Source: Stahl (2013), Theorem 2, simple diagonal case.
atlas: trace-exponential-stahl (partial) -/
theorem exists_isCompactExpRepresentation_traceExp_diagonal_of_injective
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b)
    {l u : ℝ} (hlu : l ≤ u) (hbu : ∀ i, b i ∈ Icc l u) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => traceExp (A + (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))) l u := by
  obtain ⟨R, hR, forward, hforward, hspec, _⟩ :=
    exists_exterior_eigenvalue_branches_sub_real_diagonal_conj_eq hA b hb
  have hr : 0 < R + 1 := by linarith
  have hRr : R < R + 1 := by linarith
  obtain ⟨ν, hν, _⟩ :=
    exists_isCompactExpRepresentation_traceExp_of_circleDensity_nonneg_off_slopes
      A b forward (R + 1) l u hlu hbu
      (fun t => integral_exp_mul_re_traceExponentialCircleDensity_eq_traceExp_sub_atoms
        hA b hR hforward hspec hRr hlu hbu t) (by
        intro s _ hs
        exact traceExponentialCircleDensity_re_nonneg_of_exterior_branches hA b hb
          hforward hspec hr hRr s (fun i heq => hs ⟨i, heq.symm⟩))
  exact ⟨ν, hν⟩

end NLAlib
