import TroppMatrixConcentration.Defs.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Order.Compact

/-!
# Integrability of extreme eigenvalues

Lean name: `TroppMatrixConcentration.ch3_expect_extrema_integrable`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary regularity lemma for Proposition 3.2.2, printed p. 33; uses spectral norm relation (2.1.22), printed p. 24, and the standing regularity convention of Section 2.2.1, printed p. 25.
-/
open MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator Topology
set_option autoImplicit false

namespace TroppMatrixConcentration

private lemma extrema_mem {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    lambdaMax A ∈ spectrum ℝ A ∧ lambdaMin A ∈ spectrum ℝ A := by
  have hn : (spectrum ℝ A).Nonempty :=
    ContinuousFunctionalCalculus.spectrum_nonempty A hA
  exact ⟨(spectrum.isCompact (𝕜 := ℝ) A).sSup_mem hn, (spectrum.isCompact (𝕜 := ℝ) A).sInf_mem hn⟩

private lemma max_measurable_projection {d : ℕ} [NeZero d] :
    Measurable (fun A : Matrix (Fin d) (Fin d) ℂ =>
      lambdaMax (selfAdjointPart ℝ A : Matrix (Fin d) (Fin d) ℂ)) := by
  let p := fun A : Matrix (Fin d) (Fin d) ℂ =>
    (selfAdjointPart ℝ A : Matrix (Fin d) (Fin d) ℂ)
  have hp : Continuous p := by
    simp only [p, selfAdjointPart_apply_coe]
    fun_prop
  have hsp := (upperHemicontinuous_spectrum ℝ (Matrix (Fin d) (Fin d) ℂ)).comp hp
  have hupper : UpperSemicontinuous (fun A => lambdaMax (p A)) := by
    intro A y hy
    have hsub : spectrum ℝ (p A) ⊆ Iio y := fun z hz =>
      (le_csSup (spectrum.isCompact (p A)).bddAbove hz).trans_lt hy
    have hev := hsp A (Iio y) (isOpen_Iio.mem_nhdsSet.mpr hsub)
    filter_upwards [hev] with B hB
    exact subset_of_mem_nhdsSet hB (extrema_mem (p B) (selfAdjointPart ℝ B).property).1
  exact hupper.measurable

private lemma min_measurable_projection {d : ℕ} [NeZero d] :
    Measurable (fun A : Matrix (Fin d) (Fin d) ℂ =>
      lambdaMin (selfAdjointPart ℝ A : Matrix (Fin d) (Fin d) ℂ)) := by
  let p := fun A : Matrix (Fin d) (Fin d) ℂ =>
    (selfAdjointPart ℝ A : Matrix (Fin d) (Fin d) ℂ)
  have hp : Continuous p := by
    simp only [p, selfAdjointPart_apply_coe]
    fun_prop
  have hsp := (upperHemicontinuous_spectrum ℝ (Matrix (Fin d) (Fin d) ℂ)).comp hp
  have hlower : LowerSemicontinuous (fun A => lambdaMin (p A)) := by
    intro A y hy
    have hsub : spectrum ℝ (p A) ⊆ Ioi y := fun z hz =>
      hy.trans_le (csInf_le (spectrum.isCompact (p A)).bddBelow hz)
    have hev := hsp A (Ioi y) (isOpen_Ioi.mem_nhdsSet.mpr hsub)
    filter_upwards [hev] with B hB
    exact subset_of_mem_nhdsSet hB (extrema_mem (p B) (selfAdjointPart ℝ B).property).2
  exact hlower.measurable

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem TroppMatrixConcentration.ch3_expect_extrema_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hInt : Integrable Y μ) :
    Integrable (fun ω => lambdaMax (Y ω)) μ ∧
    Integrable (fun ω => lambdaMin (Y ω)) μ := by
  have heq : (fun ω => (selfAdjointPart ℝ (Y ω) : Matrix (Fin d) (Fin d) ℂ)) =ᵐ[μ] Y := by
    filter_upwards [hHerm] with ω hω
    exact IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hω
  constructor
  · apply hInt.norm.mono'
    · exact (max_measurable_projection.comp hMeas).aestronglyMeasurable.congr
        (heq.mono fun ω hω => congrArg lambdaMax hω)
    · filter_upwards [hHerm] with ω hω
      exact spectrum.norm_le_norm_of_mem (extrema_mem (Y ω) hω).1
  · apply hInt.norm.mono'
    · exact (min_measurable_projection.comp hMeas).aestronglyMeasurable.congr
        (heq.mono fun ω hω => congrArg lambdaMin hω)
    · filter_upwards [hHerm] with ω hω
      exact spectrum.norm_le_norm_of_mem (extrema_mem (Y ω) hω).2
