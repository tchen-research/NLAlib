import NLAlib.ForMathlib.MeasureTheory.WeakDensity

/-!
# Weak densities for measures locally finite on a half-line

The Gamma-reweighted hard-edge law may have infinite mass in every neighborhood
of zero. This file localizes the proved Radon weak-density theorem and patches
the resulting antitone representatives. Source: operator rederivations, Section 5,
atlas wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace NLAlib

/-- Locally antitone almost-everywhere representatives patch to a single antitone
representative on an open half-line. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_antitoneOn_ae_eq_of_locally_antitoneOn_ae_eq
    (ℓ : ℝ) (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hlocal : ∀ a : ℝ, ℓ < a → ∃ h : ℝ → ℝ, AntitoneOn h (Ioi a) ∧
      h =ᵐ[volume.restrict (Ioi a)] f) :
    ∃ h : ℝ → ℝ, AntitoneOn h (Ioi ℓ) ∧ (∀ x ∈ Ioi ℓ, 0 ≤ h x) ∧
      h =ᵐ[volume.restrict (Ioi ℓ)] f := by
  let a : ℕ → ℝ := fun n => ℓ + 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : ℓ < a n := by
    dsimp [a]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose h hanti heq using fun n => hlocal (a n) (ha n)
  have heqall : ∀ᵐ x, ∀ n, a n < x → h n x = f x := by
    rw [ae_all_iff]
    intro n
    exact (ae_restrict_iff' measurableSet_Ioi).mp (heq n)
  let D : Set ℝ := {x | ℓ < x ∧ ∀ n, a n < x → h n x = f x}
  have hD : D ⊆ Ioi ℓ := fun _ hx => hx.1
  have hantiD : AntitoneOn f D := by
    intro x hx y hy hxy
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx.1)
    have hax : a n < x := by dsimp [a]; linarith
    have hay : a n < y := hax.trans_le hxy
    simpa [hx.2 n hax, hy.2 n hay] using hanti n hax hay hxy
  have hdense : Dense (D ∪ Iic ℓ) := by
    apply volume.dense_of_ae
    filter_upwards [heqall] with x hx
    by_cases hxl : ℓ < x
    · exact Or.inl ⟨hxl, hx⟩
    · exact Or.inr (le_of_not_gt hxl)
  have hleft : ∀ x ∈ Ioi ℓ, ∃ y ∈ D, y ≤ x := by
    intro x hx
    obtain ⟨y, hy, hyD⟩ := hdense.inter_open_nonempty (Ioo ℓ x) isOpen_Ioo
      (nonempty_Ioo.mpr hx)
    refine ⟨y, ?_, hy.2.le⟩
    rcases hyD with h | h
    · exact h
    · exact False.elim (not_le.mpr hy.1 h)
  have hright : ∀ x ∈ Ioi ℓ, ∃ y ∈ D, x ≤ y := by
    intro x hx
    obtain ⟨y, hy, hyD⟩ := hdense.inter_open_nonempty (Ioo x (x + 1)) isOpen_Ioo
      (nonempty_Ioo.mpr (by linarith))
    refine ⟨y, ?_, hy.1.le⟩
    rcases hyD with h | h
    · exact h
    · exact False.elim (not_le.mpr (hx.trans hy.1) h)
  obtain ⟨h', hh', hh'0, hh'eq⟩ := exists_antitoneOn_nonneg_extension_Ioi ℓ D f hD
    hantiD (fun x _ => hf0 x) hleft hright
  refine ⟨h', hh', hh'0, ?_⟩
  filter_upwards [ae_restrict_of_ae heqall, ae_restrict_mem measurableSet_Ioi] with x hx hxl
  exact hh'eq ⟨hxl, hx⟩

/-- The weak derivative sign gives a genuine antitone density when the measure is
only Radon after restriction to smaller half-lines. This includes weights with
infinite mass near the excluded boundary. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper).
atlas: weak-derivative-antitone-density -/
theorem exists_antitoneOn_withDensity_eq_of_locally_regular_weak_deriv_nonneg
    (μ : Measure ℝ) (ℓ : ℝ) [SigmaFinite (μ.restrict (Ioi ℓ))]
    (hloc : ∀ a : ℝ, ℓ < a → (μ.restrict (Ioi a)).Regular)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, deriv ψ x ∂μ) :
    ∃ h : ℝ → ℝ, AntitoneOn h (Ioi ℓ) ∧ (∀ x ∈ Ioi ℓ, 0 ≤ h x) ∧
      μ.restrict (Ioi ℓ) =
        (volume.restrict (Ioi ℓ)).withDensity (fun x => ENNReal.ofReal (h x)) := by
  have hwa (a : ℝ) (ha : ℓ < a) :
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioi a → (∀ x, 0 ≤ ψ x) →
        0 ≤ ∫ x, deriv ψ x ∂μ.restrict (Ioi a) := by
    intro ψ hψ hψc hψs hψ0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hweak ψ hψ hψc (hψs.trans (Ioi_subset_Ioi ha.le)) hψ0
    · intro x hx
      exact deriv_of_notMem_tsupport fun h => hx (hψs h)
  have haca (a : ℝ) (ha : ℓ < a) : μ.restrict (Ioi a) ≪ volume := by
    let := hloc a ha
    have hh := measure_restrict_absolutelyContinuous_of_weak_deriv_nonneg
      (μ.restrict (Ioi a)) a (hwa a ha)
    simpa [Measure.restrict_restrict measurableSet_Ioi, inter_self] using hh
  let ν : Measure ℝ := μ.restrict (Ioi ℓ)
  have hac : ν ≪ volume := by
    let a : ℕ → ℝ := fun n => ℓ + 1 / ((n : ℝ) + 1)
    have ha (n : ℕ) : ℓ < a n := by
      dsimp [a]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hcover : Ioi ℓ = ⋃ n, Ioi (a n) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        refine ⟨n, ?_⟩
        dsimp [a]
        linarith
      · rintro ⟨n, hn⟩
        exact (ha n).trans hn
    intro s hs
    change μ.restrict (Ioi ℓ) s = 0
    rw [Measure.restrict_apply' measurableSet_Ioi, hcover, inter_iUnion]
    apply measure_iUnion_null
    intro n
    have hh := haca (a n) (ha n) hs
    simpa [Measure.restrict_apply' measurableSet_Ioi] using hh
  let f : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal
  have hRN : volume.withDensity (ν.rnDeriv volume) = ν :=
    Measure.withDensity_rnDeriv_eq ν volume hac
  have hlocal : ∀ a : ℝ, ℓ < a → ∃ h : ℝ → ℝ, AntitoneOn h (Ioi a) ∧
      h =ᵐ[volume.restrict (Ioi a)] f := by
    intro a ha
    let := hloc a ha
    obtain ⟨h, hh, hh0, hheq⟩ := exists_antitoneOn_withDensity_eq_of_weak_deriv_nonneg
      (μ.restrict (Ioi a)) a (hwa a ha)
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self] at hheq
    have hRNa : (volume.restrict (Ioi a)).withDensity (ν.rnDeriv volume) =
        μ.restrict (Ioi a) := by
      rw [← restrict_withDensity measurableSet_Ioi, hRN]
      exact Measure.restrict_restrict_of_subset (Ioi_subset_Ioi ha.le)
    have hweights := (withDensity_eq_iff_of_sigmaFinite
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hh).ennreal_ofReal
      (Measure.measurable_rnDeriv ν volume).aemeasurable.restrict).mp
      (hheq.symm.trans hRNa.symm)
    refine ⟨h, hh, ?_⟩
    filter_upwards [hweights, ae_restrict_mem measurableSet_Ioi] with x hx hxa
    have ht := congrArg ENNReal.toReal hx
    simpa [f, ENNReal.toReal_ofReal (hh0 x hxa)] using ht
  obtain ⟨h, hh, hh0, heq⟩ := exists_antitoneOn_ae_eq_of_locally_antitoneOn_ae_eq ℓ f
    (fun _ => ENNReal.toReal_nonneg) hlocal
  refine ⟨h, hh, hh0, ?_⟩
  have hRNU : (volume.restrict (Ioi ℓ)).withDensity (ν.rnDeriv volume) = ν := by
    rw [← restrict_withDensity measurableSet_Ioi, hRN]
    dsimp [ν]
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have hweights : (fun x => ENNReal.ofReal (h x)) =ᵐ[volume.restrict (Ioi ℓ)]
      ν.rnDeriv volume := by
    filter_upwards [heq, ae_restrict_of_ae (Measure.rnDeriv_lt_top ν volume)] with x hx htop
    rw [hx]
    exact ENNReal.ofReal_toReal htop.ne
  exact hRNU.symm.trans (withDensity_congr_ae hweights.symm)

end NLAlib
