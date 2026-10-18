import NLAlib.ForMathlib.MeasureTheory.CompactTransportDuality
import NLAlib.ForMathlib.MeasureTheory.WassersteinOne
import NLAlib.ForMathlib.Analysis.MetricInfTransform

/-! # The compact Kantorovich--Rubinstein bridge

Bounds on all one-Lipschitz observables yield actual couplings with bounded
metric cost. Together with the primal Lipschitz inequality this connects the
dual moment-comparison estimates to the coupling definition of Wasserstein
distance, including atomic input laws.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NLAlib

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Compact Kantorovich--Rubinstein duality in its useful bound form. A bound
for every real one-Lipschitz observable produces an actual probability
coupling with at most that expected distance. -/
theorem exists_isCoupling_integral_dist_le_of_lipschitz_integral_sub_le
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (C : ℝ)
    (hdual : ∀ f : C(X, ℝ), LipschitzWith 1 f →
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ C) :
    ∃ π : Measure (X × X), π.IsCoupling μ ν ∧
      IsProbabilityMeasure π ∧ (∫ p, dist p.1 p.2 ∂π) ≤ C := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let cost : C(X × X, ℝ) := ⟨fun p => dist p.1 p.2, continuous_fst.dist continuous_snd⟩
  apply exists_isCoupling_integral_le_of_potentials_le μ ν cost C
  intro f g hfg
  obtain ⟨u, hu, hfu, hgu⟩ := exists_lipschitz_dominate_of_add_le_dist f g hfg
  have hI (m : Measure X) [IsFiniteMeasure m] (F : C(X, ℝ)) : Integrable F m :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hf := integral_mono (hI μ f) (hI μ u) hfu
  have hg := integral_mono (hI ν g) (hI ν (-u)) hgu
  have he : (∫ x, (-u) x ∂ν) = -(∫ x, u x ∂ν) := integral_neg _
  have hb := hdual u hu
  linarith

/-- A proved dual Lipschitz bound controls the genuine infimum over
couplings. The conclusion uses an extended distance, so finiteness is never
hidden behind `ENNReal.toReal`. -/
theorem wassersteinEDistOne_le_of_lipschitz_integral_sub_le
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (C : ℝ)
    (hdual : ∀ f : C(X, ℝ), LipschitzWith 1 f →
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ C) :
    wassersteinEDistOne μ ν ≤ ENNReal.ofReal C := by
  obtain ⟨π, hπ, hprob, hcost⟩ :=
    exists_isCoupling_integral_dist_le_of_lipschitz_integral_sub_le μ ν C hdual
  have : IsProbabilityMeasure π := hprob
  apply (wassersteinEDistOne_le_lintegral hπ).trans
  have hI : Integrable (fun p : X × X => dist p.1 p.2) π :=
    (continuous_fst.dist continuous_snd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫⁻ p, edist p.1 p.2 ∂π) = ENNReal.ofReal (∫ p, dist p.1 p.2 ∂π) := by
      simp_rw [edist_dist]
      exact (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (fun _ => dist_nonneg))).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hcost

omit [CompactSpace X] in
/-- The compact Kantorovich bound for ambient measures supported on a compact
set, with observables required to be Lipschitz only on that set. Atoms and
endpoint masses are allowed. -/
theorem wassersteinEDistOne_le_of_ae_mem_compact_of_lipschitzOn_integral_sub_le
    [SecondCountableTopology X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K) (C : ℝ)
    (hdual : ∀ f : X → ℝ, LipschitzOnWith 1 f K →
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ C) :
    wassersteinEDistOne μ ν ≤ ENNReal.ofReal C := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μK : Measure K := μ.comap Subtype.val
  let νK : Measure K := ν.comap Subtype.val
  have : IsProbabilityMeasure μK :=
    (MeasurableEmbedding.subtype_coe hK.measurableSet).isProbabilityMeasure_comap
      (by simpa using hμ)
  have : IsProbabilityMeasure νK :=
    (MeasurableEmbedding.subtype_coe hK.measurableSet).isProbabilityMeasure_comap
      (by simpa using hν)
  apply (wassersteinEDistOne_le_comap_subtype_val μ ν hK.measurableSet hμ hν).trans
  apply wassersteinEDistOne_le_of_lipschitz_integral_sub_le μK νK C
  intro u hu
  let F : X → ℝ := fun x => if hx : x ∈ K then u ⟨x, hx⟩ else 0
  have hFu (x : K) : F x = u x := by simp [F, x.property]
  have hF : LipschitzOnWith 1 F K := by
    intro x hx y hy
    simpa only [F, dif_pos hx, dif_pos hy, Subtype.edist_mk_mk] using hu ⟨x, hx⟩ ⟨y, hy⟩
  have hEq (m : Measure X) (hm : ∀ᵐ x ∂m, x ∈ K) :
      (∫ x : K, u x ∂m.comap Subtype.val) = ∫ x, F x ∂m := by
    calc
      _ = ∫ x : K, F x ∂m.comap Subtype.val :=
        integral_congr_ae (ae_of_all _ (fun x => (hFu x).symm))
      _ = ∫ x in K, F x ∂m := integral_subtype_comap hK.measurableSet F
      _ = _ := by rw [Measure.restrict_eq_self_of_ae_mem hm]
  rw [hEq μ hμ, hEq ν hν]
  exact hdual F hF

end NLAlib
