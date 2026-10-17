import NLAlib.ForMathlib.MeasureTheory.CircleIntegralReflection
import NLAlib.Matrix.Perturbation.ExteriorEigenvalueReflection
import NLAlib.Matrix.Functions.TraceExponentialContour

/-!
# Realness of Stahl's exterior contour density

Schwarz reflection of the exterior eigenvalue branches makes each
normalized exponential circle integral real. Finite sublevel sums therefore
give a real candidate density. This does not prove its nonnegativity.
Source: Stahl (2013), Theorem 2; atlas `trace-exponential-stahl`.
-/

noncomputable section

open Complex Set Metric Filter MeasureTheory
open scoped Matrix Topology ComplexConjugate

namespace NLAlib

/-- A Schwarz-symmetric exterior branch has real normalized exponential
circle integrals for every real density parameter. Source: Stahl (2013),
Theorem 2, realness of the candidate density.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem normalized_circleIntegral_exp_add_mul_im_eq_zero
    {branch : ℂ → ℂ} {R r : ℝ} (hr : 0 ≤ r) (hRr : R < r)
    (href : ∀ z, R < ‖z‖ → branch (conj z) = conj (branch z)) (s : ℝ) :
    ((2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, r), exp (branch z + (s : ℂ) * z))).im = 0 := by
  apply circleIntegral.normalized_im_eq_zero_of_conj_eq
  intro z hz
  have hz' : ‖z‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_nonneg hr] using hz
  rw [href z (hRr.trans_eq hz'.symm), ← Complex.exp_conj]
  congr 1
  simp

/-- Finite sublevel sums of the branch contour contributions are real.
This is precisely the realness assertion for Stahl's candidate density;
nonnegativity requires the separate spectral-surface boundary argument.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem sum_ite_normalized_circleIntegral_exp_add_mul_im_eq_zero
    {n : Type*} [Fintype n] {branch : n → ℂ → ℂ} {R r : ℝ}
    (hr : 0 ≤ r) (hRr : R < r)
    (href : ∀ i z, R < ‖z‖ → branch i (conj z) = conj (branch i z))
    (b : n → ℝ) (s : ℝ) :
    (∑ i, if b i < s then (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, r), exp (branch i z + (s : ℂ) * z)) else 0).im = 0 := by
  classical
  simp only [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · exact normalized_circleIntegral_exp_add_mul_im_eq_zero hr hRr (href i) s
  · rfl

open scoped Matrix.Norms.L2Operator in
/-- exterior eigenvalue branches of a Hermitian pencil with distinct
real slopes yield a real contour candidate density on every sufficiently large
circle, for every real density parameter. No branch-existence, trace-identity,
or realness assumptions are used. Source: Stahl (2013), Theorem 2.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_eigenvalue_branches_real_circle_density
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      (∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
          Function.Injective (fun i => branch i z)) ∧
      ∀ r : ℝ, R < r → ∀ s : ℝ,
        (∑ i, if b i < s then (2 * Real.pi * I : ℂ)⁻¹ *
          (∮ z in C(0, r), exp (branch i z + (s : ℂ) * z)) else 0).im = 0 := by
  obtain ⟨R, hR, branch, hbranch, hspec, href⟩ :=
    exists_exterior_eigenvalue_branches_sub_real_diagonal_conj_eq hA b hb
  refine ⟨R, hR, branch, hbranch, hspec, ?_⟩
  intro r hr s
  exact sum_ite_normalized_circleIntegral_exp_add_mul_im_eq_zero
    (hR.trans hr).le hr href b s

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian pencil with distinct real diagonal slopes has Stahl's real circle density, integrable against every real Laplace weight on each
compact interval containing the slopes. One fixed exterior circle represents
the continuous transform for every real parameter; the missing positivity of
the density is not assumed. Source: Stahl (2013), Theorem 2.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_branches_integral_real_circleDensity_eq_traceExp_sub_atoms
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ r : ℝ, R < r →
        (∀ s : ℝ, (traceExponentialCircleDensity branch b r s).im = 0) ∧
        ∀ l u : ℝ, l ≤ u → (∀ i, b i ∈ Icc l u) → ∀ t : ℝ,
          IntervalIntegrable (fun s => Real.exp (-t * s) *
            (traceExponentialCircleDensity branch b r s).re) volume l u ∧
          (∫ s in l..u, Real.exp (-t * s) *
            (traceExponentialCircleDensity branch b r s).re) =
            traceExp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ))) -
              ∑ i, Real.exp ((A i i).re - t * b i) := by
  obtain ⟨R, hR, branch, hbranch, hspec, hreal⟩ :=
    exists_exterior_eigenvalue_branches_real_circle_density hA b hb
  refine ⟨R, hR, branch, hbranch, ?_⟩
  intro r hRr
  refine ⟨fun s => hreal r hRr s, ?_⟩
  intro l u hlu hbu t
  have hcont (i : n) : ContinuousOn (branch i) (sphere 0 r) := by
    apply (hbranch i).1.continuousOn.mono
    intro z hz
    have heq : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    change R < ‖z‖
    rwa [heq]
  have hint : IntervalIntegrable (fun s => Complex.exp (-(t : ℂ) * s) *
      traceExponentialCircleDensity branch b r s) volume l u :=
    intervalIntegrable_exp_mul_traceExponentialCircleDensity hlu (hR.trans hRr).le hcont
  let v : ℝ := max r |t| + 1
  have hrv : r < v := by dsimp [v]; linarith [le_max_left r |t|]
  have htv : |t| < v := by dsimp [v]; linarith [le_max_right r |t|]
  have hRv : R < v := hRr.trans hrv
  have hrad (s : ℝ) : traceExponentialCircleDensity branch b r s =
      traceExponentialCircleDensity branch b v s :=
    traceExponentialCircleDensity_eq_of_differentiableOn_exterior
      (fun i => (hbranch i).1) (hR.trans hRr) (hR.trans hRv) hRr hRv s
  have hcomplex : (∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
      traceExponentialCircleDensity branch b r s) =
      Matrix.trace (matrixExp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))) -
        ∑ i, Complex.exp (A i i - (t : ℂ) * b i) := by
    calc
      _ = ∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
          traceExponentialCircleDensity branch b v s := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        rw [hrad s]
      _ = _ := by
        apply integral_exp_mul_traceExponentialCircleDensity_eq_trace_matrixExp_sub_atoms
          A (Matrix.diagonal (fun i => (b i : ℂ))) hlu
          (fun i => (hbu i).1) (fun i => (hbu i).2)
          (hR.trans hRv) hRv htv (fun i => (hbranch i).1) (fun i => (hbranch i).2)
        intro z hz
        have heq : ‖z‖ = v := by simpa only [mem_sphere, dist_zero_right] using hz
        have hs := hspec z (hRv.trans_eq heq.symm)
        exact (trace_matrixExp_eq_sum_exp_of_injective_mem_spectrum _ _ hs.2 hs.1).symm
  have hweight (s : ℝ) :
      (Complex.exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch b r s).re =
      Real.exp (-t * s) * (traceExponentialCircleDensity branch b r s).re := by
    have he : Complex.exp (-(t : ℂ) * s) = (Real.exp (-t * s) : ℂ) := by
      simp
    simp only [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hintre : IntervalIntegrable (fun s =>
      (Complex.exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch b r s).re)
      volume l u := ⟨hint.1.re, hint.2.re⟩
  refine ⟨by simpa only [hweight] using hintre, ?_⟩
  have hreInt : (∫ s in l..u,
      (Complex.exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch b r s).re) =
      (∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
        traceExponentialCircleDensity branch b r s).re :=
    intervalIntegral.intervalIntegral_re hint
  have hres := hreInt.trans (congrArg Complex.re hcomplex)
  have hatom (i : n) : (Complex.exp (A i i - (t : ℂ) * b i)).re =
      Real.exp ((A i i).re - t * b i) := by
    have hdiag : ((A i i).re : ℂ) = A i i := Complex.conj_eq_iff_re.mp (hA.apply i i)
    rw [← hdiag]
    simpa using Complex.exp_ofReal_re ((A i i).re - t * b i)
  simpa only [hweight, Complex.sub_re, Complex.re_sum, hatom, traceExp_complex] using hres

end NLAlib
