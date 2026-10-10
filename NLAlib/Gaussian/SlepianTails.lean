import NLAlib.Gaussian.Comparison.Slepian

/-!
# Slepian comparison for nonstrict upper tails

The base theorem compares strict tails. Continuity from above also gives the catalogue's
nonstrict tails, including Gaussian vectors with atoms caused by degenerate coordinates.
Equal coordinate variances remain essential. Atlas: `slepian`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace NLAlib

private def approachingThreshold (τ : ℝ) (k : ℕ) : ℝ := τ - 1 / ((k : ℝ) + 1)

private theorem approachingThreshold_tendsto (τ : ℝ) :
    Tendsto (approachingThreshold τ) atTop (𝓝 τ) := by
  change Tendsto (fun k : ℕ => τ - 1 / ((k : ℝ) + 1)) atTop (𝓝 τ)
  simpa only [one_div, sub_zero] using
    (tendsto_const_nhds (x := τ)).sub tendsto_one_div_add_atTop_nhds_zero_nat

private theorem ge_tail_eq_iInter {Ω : Type*} (f : Ω → ℝ) (τ : ℝ) :
    {ω | τ ≤ f ω} = ⋂ k : ℕ, {ω | approachingThreshold τ k < f ω} := by
  ext ω
  constructor
  · intro h
    change τ ≤ f ω at h
    apply Set.mem_iInter.mpr
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    change τ - 1 / ((k : ℝ) + 1) < f ω
    linarith
  · intro h
    exact le_of_tendsto' (approachingThreshold_tendsto τ)
      (fun k => (Set.mem_iInter.mp h k).le)

private theorem strict_tail_antitone {Ω : Type*} (f : Ω → ℝ) (τ : ℝ) :
    Antitone (fun k : ℕ => {ω | approachingThreshold τ k < f ω}) := by
  intro m n hmn ω hω
  have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  change τ - 1 / ((m : ℝ) + 1) < f ω
  change τ - 1 / ((n : ℝ) + 1) < f ω at hω
  linarith

/-- Strict stochastic upper-tail comparison implies nonstrict comparison, for finite
measures and a.e.-measurable random variables. This uses continuity from above and does
not assume an atomless law. Atlas `slepian` (tail convention bridge). -/
theorem measure_ge_le_of_measure_gt_le {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hcomp : ∀ τ : ℝ, P {ω | τ < X ω} ≤ Q {ω | τ < Y ω}) (τ : ℝ) :
    P {ω | τ ≤ X ω} ≤ Q {ω | τ ≤ Y ω} := by
  rw [ge_tail_eq_iInter X τ, ge_tail_eq_iInter Y τ,
    (strict_tail_antitone X τ).measure_iInter
      (fun _ => nullMeasurableSet_lt aemeasurable_const hX) ⟨0, measure_ne_top _ _⟩,
    (strict_tail_antitone Y τ).measure_iInter
      (fun _ => nullMeasurableSet_lt aemeasurable_const hY) ⟨0, measure_ne_top _ _⟩]
  exact iInf_mono fun k => hcomp (approachingThreshold τ k)

/-- **Slepian's nonstrict tail comparison.** For finite centred Gaussian vectors with
equal coordinate variances and dominated increments, `P(max X ≥ τ) ≤ Q(max Y ≥ τ)`.
Degenerate Gaussian laws are included. Slepian 1962; Vershynin 2018, Theorem 7.2.1;
atlas `slepian`.
atlas: slepian -/
theorem slepian_inequality_ge {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P)
    (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hvar : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Y t ω ^ 2 ∂Q)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤
      ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) (τ : ℝ) :
    P {ω | τ ≤ ⨆ t, X t ω} ≤ Q {ω | τ ≤ ⨆ t, Y t ω} := by
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  apply measure_ge_le_of_measure_gt_le
    (AEMeasurable.iSup fun t => (hX.eval t).aemeasurable)
    (AEMeasurable.iSup fun t => (hY.eval t).aemeasurable)
  exact slepian_inequality X Y hX hY hX0 hY0 hvar hinc

end NLAlib
