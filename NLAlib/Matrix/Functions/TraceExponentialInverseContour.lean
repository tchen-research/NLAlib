import NLAlib.Matrix.Perturbation.InverseEigenvalueBranches
import NLAlib.Matrix.Functions.TraceExponentialContour
import NLAlib.ForMathlib.Analysis.Complex.ExteriorCircleChangeVariables

/-!
# The inverse-contour formula for Stahl's density

The inverse eigenvalue branches are constructed from the actual inverse
matrix pencil. Their affine slopes match them to the original branches.
Changing contour variables, replacing the separate image loops by a common
large circle, and integrating by parts gives the exponential moment of the
selected inverse-branch sum. This identifies the already defined density
with the analytic quantity used in the planar positivity route.
-/

noncomputable section

open Set Metric Complex Filter
open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Stahl's circle density equals the negative exponential moment of any
inverse branch family with the actual pencil spectrum and affine asymptotes.
The same-label inverse relation, contour changes, and orientation are derived
from these spectral data. This form permits the same inverse branches to be
used in the upper-root holomorphy and positivity arguments.
atlas: trace-exponential-stahl (partial) -/
theorem eventually_circleDensity_eq_neg_circleIntegral_of_exterior_inverse_branches
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R S ρ : ℝ} {forward inverse : n → ℂ → ℂ}
    (hforward : ∀ i, DifferentiableOn ℂ (forward i) {z | R < ‖z‖} ∧
      Tendsto (fun z => forward i z + (b i : ℂ) * z)
        (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hinverse : ∀ i, DifferentiableOn ℂ (inverse i) {u | S < ‖u‖} ∧
        Tendsto (fun u => inverse i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))))
    (hinverseSpec : ∀ u, S < ‖u‖ → ∀ i,
      u - (s : ℂ) * inverse i u ∈ spectrum ℂ
        (A - inverse i u • Matrix.diagonal (fun i => (b i : ℂ))))
    (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∀ᶠ r : ℝ in atTop,
        traceExponentialCircleDensity forward b ρ s =
          -(2 * Real.pi * I : ℂ)⁻¹ *
            (∮ u in C(0, r), exp u * ∑ i, if b i < s then inverse i u else 0) := by
  classical
  have hcomp := eventually_exterior_inverse_eigenvalue_branches_eq A b hb s hs
    (fun i => (hforward i).2) hforwardSpec (fun i => (hinverse i).2)
    hinverseSpec
  have hmoment : ∀ i, ∀ᶠ r : ℝ in atTop,
      (∮ z in C(0, ρ), exp (forward i z + (s : ℂ) * z)) =
        -(∮ u in C(0, r), exp u * inverse i u) := by
    intro i
    have hlim : Tendsto (fun u => inverse i u - (((s - b i)⁻¹ : ℝ) : ℂ) * u)
        (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))) := by
      simpa only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using (hinverse i).2
    apply Complex.eventually_circleIntegral_exp_eq_neg_circleIntegral_exp_mul_of_inverse
      ((hforward i).1.add (differentiableOn_id.const_mul (s : ℂ))) (hinverse i).1
      (inv_ne_zero (sub_ne_zero.mpr (hs i))) hlim _ hρ hRρ
    exact hcomp.mono (fun u hu => hu i)
  have hmoment' : ∀ᶠ r : ℝ in atTop, ∀ i,
      (∮ z in C(0, ρ), exp (forward i z + (s : ℂ) * z)) =
        -(∮ u in C(0, r), exp u * inverse i u) := by
    simpa only [Filter.eventually_all] using hmoment
  filter_upwards [hmoment', eventually_gt_atTop (0 : ℝ), eventually_gt_atTop S]
    with r hmoment hr hSr
  have hc : sphere (0 : ℂ) r ⊆ {u : ℂ | S < ‖u‖} := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    change S < ‖u‖
    simpa only [hnorm] using hSr
  have hci (i : n) : CircleIntegrable
      (fun u => exp u * (if b i < s then inverse i u else 0)) 0 r := by
    by_cases hi : b i < s
    · simpa only [if_pos hi] using
        (Complex.continuous_exp.continuousOn.fun_mul
          ((hinverse i).1.continuousOn.mono hc)).circleIntegrable hr.le
    · simp only [if_neg hi, mul_zero]
      exact circleIntegrable_const 0 0 r
  have hsum : (∮ u in C(0, r), exp u * ∑ i, if b i < s then inverse i u else 0) =
      ∑ i, ∮ u in C(0, r), exp u * (if b i < s then inverse i u else 0) := by
    simp_rw [Finset.mul_sum]
    simpa using
      circleIntegral.integral_fun_sum (s := Finset.univ) (fun i _ => hci i)
  rw [hsum, Finset.mul_sum]
  unfold traceExponentialCircleDensity
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b i < s
  · simp only [if_pos hi]
    rw [hmoment i]
    ring
  · simp [hi, circleIntegral]

/-- Constructing the inverse pencil branches gives the common-circle
inverse-moment formula for any established exterior family of the original
pencil. No inverse spectral family or contour identity is assumed.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_inverse_branches_circleDensity_eq_neg_circleIntegral
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R ρ : ℝ} {forward : n → ℂ → ℂ}
    (hforward : ∀ i, DifferentiableOn ℂ (forward i) {z | R < ‖z‖} ∧
      Tendsto (fun z => forward i z + (b i : ℂ) * z)
        (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∃ S : ℝ, 0 < S ∧ ∃ inverse : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (inverse i) {u | S < ‖u‖} ∧
        Tendsto (fun u => inverse i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, S < ‖u‖ →
        (∀ i, u - (s : ℂ) * inverse i u ∈ spectrum ℂ
          (A - inverse i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => inverse i u)) ∧
      ∀ᶠ r : ℝ in atTop,
        traceExponentialCircleDensity forward b ρ s =
          -(2 * Real.pi * I : ℂ)⁻¹ *
            (∮ u in C(0, r), exp u * ∑ i, if b i < s then inverse i u else 0) := by
  obtain ⟨S, hS, inverse, hinverse, hinverseSpec⟩ :=
    exists_exterior_inverse_eigenvalue_branches A b hb s hs
  exact ⟨S, hS, inverse, hinverse, hinverseSpec,
    eventually_circleDensity_eq_neg_circleIntegral_of_exterior_inverse_branches
      A b hb s hs hforward hforwardSpec hinverse
      (fun u hu => (hinverseSpec u hu).1) hρ hRρ⟩

end NLAlib
