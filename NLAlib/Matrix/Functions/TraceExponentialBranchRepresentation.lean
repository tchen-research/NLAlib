import NLAlib.Matrix.Functions.TraceExponentialSpectrum
import NLAlib.Matrix.Functions.TraceExponentialContour
import NLAlib.Matrix.Perturbation.ExteriorEigenvalueBranches

/-!
# Stahl's exterior branches and the matrix trace identity

For a real diagonal coefficient with distinct diagonal entries, the exterior
eigenvalue branches are constructed from the characteristic polynomial. They
give the atom-plus-contour-density transform of the matrix exponential.
Neither eigenvalue existence nor the boundary trace identity is assumed.
Density positivity is a separate global spectral-surface problem.
Source: Stahl 2013, Theorem 2 and §§3–4; `trace-exponential-stahl`.
-/

open Complex Filter Metric MeasureTheory
open scoped Interval circleIntegral Topology

noncomputable section

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Distinct real diagonal slopes admit exterior eigenvalue branches
whose contour densities give the atom-plus-density identity for the trace exponential. This holds for every matrix `A`, without a Hermitian
assumption; the resulting densities and atoms can be complex-valued.
Source: Stahl 2013, Theorem 2, representation verification. Positivity of the
density, which uses global spectral geometry, is not asserted here.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_branches_sum_integral_eq_trace_matrixExp_sub_atoms
    (a : n → ℝ) (ha : Function.Injective a) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (a i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ b : ℝ, (∀ i, a i ≤ b) → ∀ t r : ℝ, R < r → |t| < r →
        (∑ i, ∫ s in a i..b, Complex.exp (-(t : ℂ) * s) *
          ((2 * Real.pi * I : ℂ)⁻¹ *
            (∮ z in C(0, r), Complex.exp (branch i z + s * z)))) =
          Matrix.trace (matrixExp (A - (t : ℂ) • Matrix.diagonal (fun i => (a i : ℂ)))) -
            ∑ i, Complex.exp (A i i - (t : ℂ) * a i) := by
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_sub_real_diagonal a ha A
  refine ⟨R, hR, branch, hbranch, ?_⟩
  intro b hab t r hRr htr
  apply sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_trace_matrixExp_sub_atoms
    A (Matrix.diagonal (fun i => (a i : ℂ))) hab (hR.trans hRr) hRr htr
    (fun i => (hbranch i).1) (fun i => (hbranch i).2)
  intro z hz
  have hzr : R < ‖z‖ := by
    have heq : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    simpa only [heq] using hRr
  exact (trace_matrixExp_eq_sum_exp_of_injective_mem_spectrum _ _
    (hspec z hzr).2 (hspec z hzr).1).symm

/-- One exterior circle suffices for every real Laplace parameter in the
matrix atom-plus-density formula. Radius independence removes the
temporary requirement that the evaluation point lie inside that fixed
circle. Source: Stahl 2013, Theorem 2, transform verification.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_branches_sum_integral_eq_trace_matrixExp_sub_atoms_fixed_circle
    (a : n → ℝ) (ha : Function.Injective a) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (a i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ b : ℝ, (∀ i, a i ≤ b) → ∀ t r : ℝ, R < r →
        (∑ i, ∫ s in a i..b, Complex.exp (-(t : ℂ) * s) *
          ((2 * Real.pi * I : ℂ)⁻¹ *
            (∮ z in C(0, r), Complex.exp (branch i z + s * z)))) =
          Matrix.trace (matrixExp (A - (t : ℂ) • Matrix.diagonal (fun i => (a i : ℂ)))) -
            ∑ i, Complex.exp (A i i - (t : ℂ) * a i) := by
  obtain ⟨R, hR, branch, hbranch, hformula⟩ :=
    exists_exterior_branches_sum_integral_eq_trace_matrixExp_sub_atoms a ha A
  refine ⟨R, hR, branch, hbranch, ?_⟩
  intro b hab t r hRr
  let u : ℝ := max r |t| + 1
  have hru : r < u := by dsimp [u]; linarith [le_max_left r |t|]
  have htu : |t| < u := by dsimp [u]; linarith [le_max_right r |t|]
  have hRu : R < u := hRr.trans hru
  have hrad (i : n) (s : ℝ) :
      (∮ z in C(0, r), Complex.exp (branch i z + s * z)) =
        ∮ z in C(0, u), Complex.exp (branch i z + s * z) := by
    apply circleIntegral_eq_of_differentiableOn_exterior
      (Complex.differentiable_exp.comp_differentiableOn
        ((hbranch i).1.add (differentiableOn_id.const_mul (s : ℂ))))
      (hR.trans hRr) (hR.trans hRu) hRr hRu
  calc
    _ = ∑ i, ∫ s in a i..b, Complex.exp (-(t : ℂ) * s) *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          (∮ z in C(0, u), Complex.exp (branch i z + s * z))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [hrad i s]
    _ = _ := hformula b hab t u hRu htu

/-- The exterior branches of a matrix pencil with distinct diagonal
slopes give an integrable circle density on any compact interval containing
the slopes. One fixed circle gives its transform at every real parameter.
The density is complex-valued here, and no nonnegativity claim is made.
Source: Stahl 2013, Theorem 2, representation verification.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_branches_integral_circleDensity_eq_trace_matrixExp_sub_atoms
    (a : n → ℝ) (ha : Function.Injective a) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (a i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ l u : ℝ, l ≤ u → (∀ i, a i ∈ Set.Icc l u) → ∀ r : ℝ, R < r → ∀ t : ℝ,
        IntervalIntegrable (fun s => Complex.exp (-(t : ℂ) * s) *
          traceExponentialCircleDensity branch a r s) volume l u ∧
        (∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
          traceExponentialCircleDensity branch a r s) =
          Matrix.trace (matrixExp (A - (t : ℂ) • Matrix.diagonal (fun i => (a i : ℂ)))) -
            ∑ i, Complex.exp (A i i - (t : ℂ) * a i) := by
  obtain ⟨R, hR, branch, hbranch, hformula⟩ :=
    exists_exterior_branches_sum_integral_eq_trace_matrixExp_sub_atoms_fixed_circle a ha A
  refine ⟨R, hR, branch, hbranch, ?_⟩
  intro l u hlu hau r hRr t
  have hcont (i : n) : ContinuousOn (branch i) (sphere 0 r) := by
    apply (hbranch i).1.continuousOn.mono
    intro z hz
    have heq : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    change R < ‖z‖
    rwa [heq]
  refine ⟨intervalIntegrable_exp_mul_traceExponentialCircleDensity hlu
    (hR.trans hRr).le hcont, ?_⟩
  rw [integral_exp_mul_traceExponentialCircleDensity_eq_sum_integral hlu
    (fun i => (hau i).1) (fun i => (hau i).2) (hR.trans hRr).le hcont]
  exact hformula u (fun i => (hau i).2) t r hRr

end NLAlib
