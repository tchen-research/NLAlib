import NLAlib.ForMathlib.MeasureTheory.Coupling
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Primal one-Wasserstein transport cost

The extended one-Wasserstein distance is the infimum of actual transport costs
over measures with the specified marginals. Explicit couplings therefore give
upper bounds. The Lipschitz integral inequality is proved in the other direction;
it does not assume Kantorovich duality.

These generic foundations support `tensor-chebyshev-kernel-measure` and
`chebyshev-moment-wasserstein`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

variable {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]

/-- Extended one-Wasserstein distance, defined by actual couplings and their
expected metric cost. Incompatible masses give the infimum of an empty set. -/
def wassersteinEDistOne (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ π : Measure (X × X), ⨅ _ : π.IsCoupling μ ν, ∫⁻ p, edist p.1 p.2 ∂π

theorem wassersteinEDistOne_le_lintegral {μ ν : Measure X} {π : Measure (X × X)}
    (hπ : π.IsCoupling μ ν) :
    wassersteinEDistOne μ ν ≤ ∫⁻ p, edist p.1 p.2 ∂π :=
  iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

@[simp]
theorem wassersteinEDistOne_self (μ : Measure X) : wassersteinEDistOne μ μ = 0 := by
  apply le_antisymm _ bot_le
  refine (wassersteinEDistOne_le_lintegral (Measure.isCoupling_map_diag μ)).trans ?_
  exact (lintegral_map_le (fun p : X × X => edist p.1 p.2)
    (fun x : X => (x, x))).trans_eq (by simp)

variable [BorelSpace X] [SecondCountableTopology X]

/-- The composition-product measure is an explicit coupling of a law and its
Markov-kernel smoothing. -/
theorem wassersteinEDistOne_le_lintegral_compProd (μ : Measure X) [SFinite μ]
    (κ : Kernel X X) [IsMarkovKernel κ] :
    wassersteinEDistOne μ (κ ∘ₘ μ) ≤ ∫⁻ x, ∫⁻ y, edist x y ∂κ x ∂μ := by
  convert wassersteinEDistOne_le_lintegral (Measure.isCoupling_compProd μ κ) using 1
  exact (Measure.lintegral_compProd (measurable_fst.edist measurable_snd)).symm

/-- An almost-everywhere displacement bound on a Markov smoothing bounds the
actual primal distance for every probability input law. -/
theorem wassersteinEDistOne_comp_le_of_lintegral_le (μ : Measure X)
    [IsProbabilityMeasure μ] (κ : Kernel X X) [IsMarkovKernel κ] {C : ℝ≥0∞}
    (hC : ∀ᵐ x ∂μ, ∫⁻ y, edist x y ∂κ x ≤ C) :
    wassersteinEDistOne μ (κ ∘ₘ μ) ≤ C := by
  apply (wassersteinEDistOne_le_lintegral_compProd μ κ).trans
  exact (lintegral_mono_ae hC).trans_eq (by simp)

omit [SecondCountableTopology X] in
/-- Measurable nonexpanding maps push actual couplings forward and cannot
increase their optimal metric cost. This includes subtype-to-ambient
inclusions when the subtype has the inherited metric. -/
theorem wassersteinEDistOne_map_le {Y : Type*} [MeasurableSpace Y]
    [PseudoEMetricSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ ν : Measure X) {f : X → Y} (hf : LipschitzWith 1 f) :
    wassersteinEDistOne (μ.map f) (ν.map f) ≤ wassersteinEDistOne μ ν := by
  refine le_iInf fun π => le_iInf fun hπ => ?_
  have hfm := hf.continuous.measurable
  apply (wassersteinEDistOne_le_lintegral (hπ.map hfm hfm)).trans
  rw [lintegral_map (g := fun p : X × X => (f p.1, f p.2))
    (measurable_fst.edist measurable_snd) (by fun_prop)]
  apply lintegral_mono
  intro p
  simpa only [ENNReal.coe_one, one_mul] using hf p.1 p.2

private theorem wassersteinEDistOne_le_swap (μ ν : Measure X) :
    wassersteinEDistOne μ ν ≤ wassersteinEDistOne ν μ := by
  refine le_iInf fun π => le_iInf fun hπ => ?_
  apply (wassersteinEDistOne_le_lintegral hπ.swap).trans
  rw [lintegral_map (measurable_fst.edist measurable_snd) measurable_swap]
  exact le_of_eq (lintegral_congr fun p => edist_comm p.2 p.1)

theorem wassersteinEDistOne_comm (μ ν : Measure X) :
    wassersteinEDistOne μ ν = wassersteinEDistOne ν μ :=
  le_antisymm (wassersteinEDistOne_le_swap μ ν) (wassersteinEDistOne_le_swap ν μ)

/-- A coupling on a measurable common support pushes to a coupling of the
ambient measures with the same metric cost. -/
theorem wassersteinEDistOne_le_comap_subtype_val (μ ν : Measure X) {K : Set X}
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K) :
    wassersteinEDistOne μ ν ≤
      wassersteinEDistOne (μ.comap (Subtype.val : K → X)) (ν.comap (Subtype.val : K → X)) := by
  have hmapμ : (μ.comap (Subtype.val : K → X)).map Subtype.val = μ := by
    rw [map_comap_subtype_coe hK, Measure.restrict_eq_self_of_ae_mem hμ]
  have hmapν : (ν.comap (Subtype.val : K → X)).map Subtype.val = ν := by
    rw [map_comap_subtype_coe hK, Measure.restrict_eq_self_of_ae_mem hν]
  simpa only [hmapμ, hmapν] using wassersteinEDistOne_map_le
    (μ.comap (Subtype.val : K → X)) (ν.comap (Subtype.val : K → X))
    (f := Subtype.val) isometry_subtype_coe.lipschitz

omit [BorelSpace X] [SecondCountableTopology X] in
/-- Every integrable real one-Lipschitz observable gives a lower bound on the
primal transport cost. No dual representation is used here. -/
theorem enorm_integral_sub_le_wassersteinEDistOne {μ ν : Measure X} {f : X → ℝ}
    (hf : LipschitzWith 1 f) (hμ : Integrable f μ) (hν : Integrable f ν) :
    ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ₑ ≤ wassersteinEDistOne μ ν := by
  refine le_iInf fun π => le_iInf fun hπ => ?_
  have hfst : Integrable (fun p : X × X => f p.1) π :=
    hπ.measurePreserving_fst.integrable_comp_of_integrable hμ
  have hsnd : Integrable (fun p : X × X => f p.2) π :=
    hπ.measurePreserving_snd.integrable_comp_of_integrable hν
  rw [← hπ.integral_fst hμ.aestronglyMeasurable,
    ← hπ.integral_snd hν.aestronglyMeasurable, ← integral_sub hfst hsnd]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro p
  simpa only [← edist_eq_enorm_sub, ENNReal.coe_one, one_mul] using hf p.1 p.2

end NLAlib
