import NLAlib.ForMathlib.MeasureTheory.ExponentialAtomic
import NLAlib.ForMathlib.MeasureTheory.IntervalDensity
import NLAlib.Matrix.Functions.TraceExponentialContourReal

/-!
# Positive measures from Stahl's contour density

The checked real atom-plus-density identity is converted to an actual positive
finite measure once the exact contour density is known to be nonnegative
almost everywhere. The measure is explicitly the existing exponential atomic
measure plus restricted Lebesgue measure weighted by the density.

The final theorem constructs the exterior branches and transform identity;
its only remaining condition is density nonnegativity. A finite exceptional
set of slope values is harmless for this construction.
Source: Stahl (2013), Theorem 2; atlas `trace-exponential-stahl` (partial).
-/

noncomputable section

open Complex Set Metric Filter MeasureTheory
open scoped Matrix Topology

namespace NLAlib

/-- The real atom-plus-density identity and almost everywhere nonnegativity
of its exact circle density construct a finite positive representing measure.
The underlying measure is displayed explicitly, so no measure-existence or
Laplace-transform conclusion is assumed. Positive exponential parameters here
are equivalent to the Laplace convention by substituting `-t`.
Source: Stahl (2013), Theorem 2 (measure assembly). -/
theorem exists_isCompactExpRepresentation_traceExp_of_circleDensity_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : n → ℝ) (branch : n → ℂ → ℂ) (r l u : ℝ)
    (hlu : l ≤ u) (hbu : ∀ i, b i ∈ Icc l u)
    (htransform : ∀ t : ℝ,
      IntervalIntegrable (fun s => Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) volume l u ∧
      (∫ s in l..u, Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) =
        traceExp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ))) -
          ∑ i, Real.exp ((A i i).re - t * b i))
    (hpos : ∀ᵐ s ∂volume.restrict (Icc l u),
      0 ≤ (traceExponentialCircleDensity branch b r s).re) :
    ∃ ν : FiniteMeasure ℝ,
      IsCompactExpRepresentation ν
        (fun t : ℝ => traceExp (A + (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))) l u ∧
      (ν : Measure ℝ) =
        (volume.restrict (Icc l u)).withDensity
          (fun s => ENNReal.ofReal (traceExponentialCircleDensity branch b r s).re) +
          (exponentialAtomicMeasure (fun i => (A i i).re) b : Measure ℝ) := by
  let ρ : ℝ → ℝ := fun s => (traceExponentialCircleDensity branch b r s).re
  have hρint : IntervalIntegrable ρ volume l u := by
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using (htransform 0).1
  have hρ : IntegrableOn ρ (Icc l u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlu).mp hρint
  let νc : FiniteMeasure ℝ := intervalDensityMeasure ρ l u hρ
  let νa : FiniteMeasure ℝ := exponentialAtomicMeasure (fun i => (A i i).re) b
  have hrep := (isCompactExpRepresentation_intervalDensityMeasure hlu hρ hpos).add
    (isCompactExpRepresentation_exponentialAtomicMeasure (fun i => (A i i).re) b hbu)
  refine ⟨νc + νa, ?_, rfl⟩
  convert hrep using 1
  funext t
  have ht := (htransform (-t)).2
  simp only [neg_neg, neg_mul, sub_neg_eq_add, Complex.ofReal_neg, neg_smul] at ht
  dsimp only [ρ]
  linarith

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian pencil with distinct diagonal slopes supplies actual exterior
branches such that nonnegativity of their real circle density almost everywhere
on the chosen spectral interval constructs a positive finite measure there.
The branch existence, real density and transform identity are proved; only the
positivity condition is left for the planar root-sum argument.
Source: Stahl (2013), Theorem 2 (conditional measure assembly).
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_branches_isCompactExpRepresentation_of_circleDensity_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ r : ℝ, R < r →
        (∀ s : ℝ, (traceExponentialCircleDensity branch b r s).im = 0) ∧
        ∀ l u : ℝ, l ≤ u → (∀ i, b i ∈ Icc l u) →
          (∀ᵐ s ∂volume.restrict (Icc l u),
            0 ≤ (traceExponentialCircleDensity branch b r s).re) →
          ∃ ν : FiniteMeasure ℝ,
            IsCompactExpRepresentation ν
              (fun t : ℝ => traceExp (A + (t : ℂ) •
                Matrix.diagonal (fun i => (b i : ℂ)))) l u ∧
            (ν : Measure ℝ) =
              (volume.restrict (Icc l u)).withDensity
                (fun s => ENNReal.ofReal (traceExponentialCircleDensity branch b r s).re) +
                (exponentialAtomicMeasure (fun i => (A i i).re) b : Measure ℝ) := by
  obtain ⟨R, hR, branch, hbranch, hrep⟩ :=
    exists_exterior_branches_integral_real_circleDensity_eq_traceExp_sub_atoms hA b hb
  refine ⟨R, hR, branch, hbranch, ?_⟩
  intro r hr
  obtain ⟨hreal, htransform⟩ := hrep r hr
  refine ⟨hreal, ?_⟩
  intro l u hlu hbu hpos
  exact exists_isCompactExpRepresentation_traceExp_of_circleDensity_nonneg
    A b branch r l u hlu hbu (htransform l u hlu hbu) hpos

/-- Nonnegativity away from the finitely many slope values already suffices
for assembling the positive measure; values at those exceptional points do not
change the density measure. The transform premise is the previously proved
real atom-plus-density formula for these exact branches.
Source: Stahl (2013), Theorem 2 (finite exceptional set). -/
theorem exists_isCompactExpRepresentation_traceExp_of_circleDensity_nonneg_off_slopes
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : n → ℝ) (branch : n → ℂ → ℂ) (r l u : ℝ)
    (hlu : l ≤ u) (hbu : ∀ i, b i ∈ Icc l u)
    (htransform : ∀ t : ℝ,
      IntervalIntegrable (fun s => Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) volume l u ∧
      (∫ s in l..u, Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) =
        traceExp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ))) -
          ∑ i, Real.exp ((A i i).re - t * b i))
    (hpos : ∀ s ∈ Icc l u, s ∉ Set.range b →
      0 ≤ (traceExponentialCircleDensity branch b r s).re) :
    ∃ ν : FiniteMeasure ℝ,
      IsCompactExpRepresentation ν
        (fun t : ℝ => traceExp (A + (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))) l u ∧
      (ν : Measure ℝ) =
        (volume.restrict (Icc l u)).withDensity
          (fun s => ENNReal.ofReal (traceExponentialCircleDensity branch b r s).re) +
          (exponentialAtomicMeasure (fun i => (A i i).re) b : Measure ℝ) := by
  apply exists_isCompactExpRepresentation_traceExp_of_circleDensity_nonneg
    A b branch r l u hlu hbu htransform
  have hoff : ∀ᵐ s : ℝ, s ∉ Set.range b := by
    rw [ae_iff]
    convert (Set.finite_range b).measure_zero volume using 1
    congr 1
    ext s
    simp
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hoff] with s hs hsb
  exact hpos s hs hsb

end NLAlib
