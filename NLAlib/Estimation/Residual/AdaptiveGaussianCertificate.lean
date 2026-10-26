import NLAlib.Estimation.Residual.GaussianCertificate
import NLAlib.ForMathlib.Probability.IndependentKernel
import NLAlib.Matrix.Measurability.SpectralMeasurable

/-!
# Fresh Gaussian residual certificates under adaptive selection

Each stage may depend on its own history. The fresh probe family has the product
Gaussian law and is independent of that history; no independence between stages
is assumed. A countable union bound certifies every finite selected output stage.

Source: the fresh-probe extension of Halko--Martinsson--Tropp (2011), Sections
4.3--4.4, derived by conditioning and countable subadditivity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Matrix

namespace NLAlib

variable {m n κ Ω : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype κ] [Nonempty κ] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq m] [DecidableEq n] in
private theorem measurable_gaussianResidualMaximum :
    Measurable (fun p : Matrix m n ℝ × (κ → n → ℝ) => gaussianResidualMaximum p.1 p.2) := by
  unfold gaussianResidualMaximum
  have hf (j : κ) : Measurable (fun p : Matrix m n ℝ × (κ → n → ℝ) =>
      ‖WithLp.toLp 2 (p.1 *ᵥ p.2 j)‖) := by
    change Measurable (fun p : Matrix m n ℝ × (κ → n → ℝ) =>
      ‖WithLp.toLp 2 (fun i => ∑ k, p.1 i k * p.2 j k)‖)
    fun_prop
  have hm := Finset.measurable_sup' Finset.univ_nonempty (fun j _ => hf j)
  change Measurable (fun p => (Finset.univ.sup' Finset.univ_nonempty
    (fun j (p : Matrix m n ℝ × (κ → n → ℝ)) => ‖WithLp.toLp 2 (p.1 *ᵥ p.2 j)‖)) p) at hm
  simpa only [Finset.sup'_apply] using hm

/-- A random rectangular residual independent of a fresh Gaussian probe family
obeys the same certificate as a deterministic residual. No integrability or
boundedness assumption on the residual is required. -/
theorem measure_specNorm_gt_gaussianResidualMaximum_le_of_indepFun
    {R : Ω → Matrix m n ℝ} {G : Ω → κ → n → ℝ}
    (hR : AEMeasurable R μ)
    (hG : HasLaw G (Measure.pi fun _ : κ => gaussianVector n) μ)
    (hind : IndepFun R G μ) {α : ℝ} (hα : 1 < α) :
    μ {ω | α * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum (R ω) (G ω) <
      specNorm (R ω)} ≤ ENNReal.ofReal ((α⁻¹) ^ Fintype.card κ) := by
  let E : Set (Matrix m n ℝ × (κ → n → ℝ)) :=
    {p | α * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum p.1 p.2 < specNorm p.1}
  have hE : MeasurableSet E := by
    apply measurableSet_lt
      ((measurable_gaussianResidualMaximum (m := m) (n := n) (κ := κ)).const_mul _)
    exact measurable_specNorm_of_entries fun i j => (Matrix.measurable_entry i j).comp measurable_fst
  have hfixed (A : Matrix m n ℝ) :
      (Measure.pi fun _ : κ => gaussianVector n) {g | (A, g) ∈ E} ≤
        ENNReal.ofReal ((α⁻¹) ^ Fintype.card κ) :=
    measure_specNorm_gt_gaussianResidualMaximum_le A hα
      (fun j => (measurePreserving_eval (fun _ : κ => gaussianVector n) j).hasLaw)
      (iIndepFun_pi fun _ => aemeasurable_id)
  exact hind.measure_mem_le_of_forall hR hG hE hfixed

omit [Fintype κ] [Nonempty κ] in
/-- History-measurable residuals and fresh Gaussian families satisfy a simultaneous
certificate at every stage and at every finite selected stage. The history spaces
need not be increasing and the selector need not be a stopping time (or even
measurable); the stronger outer-measure conclusion covers measurable selectors.

Freshness is expressed by the joint product Gaussian law and independence from
the history sigma-algebra, equivalently a fixed conditional iid Gaussian law.
The budget is a sum of nonnegative probabilities in `ENNReal`, so it does not use
the totalized real infinite-sum convention for divergent series.
Source: HMT (2011), Sections 4.3--4.4, fresh-probe extension by a countable union bound.
atlas: adaptive-gaussian-residual-certification -/
theorem measure_exists_specNorm_gt_freshGaussianResidualMaximum_le
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (R : ℕ → Ω → Matrix m n ℝ) (hR : ∀ t, Measurable[F t] (R t))
    (s : ℕ → ℕ) (hs : ∀ t, 0 < s t)
    (G : ∀ t, Ω → Fin (s t) → n → ℝ)
    (hG : ∀ t, HasLaw (G t) (Measure.pi fun _ : Fin (s t) => gaussianVector n) μ)
    (hfresh : ∀ t, Indep (F t) (MeasurableSpace.comap (G t) inferInstance) μ)
    (α : ℕ → ℝ) (hα : ∀ t, 1 < α t) {δ : ℝ}
    (hbudget : (∑' t, ENNReal.ofReal (((α t)⁻¹) ^ s t)) ≤ ENNReal.ofReal δ)
    (τ : Ω → WithTop ℕ) :
    letI : ∀ t, Nonempty (Fin (s t)) := fun t => Fin.pos_iff_nonempty.mp (hs t)
    μ {ω | ∃ t, α t * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum (R t ω) (G t ω) <
      specNorm (R t ω)} ≤ ENNReal.ofReal δ ∧
    μ {ω | ∃ t : ℕ, τ ω = (t : WithTop ℕ) ∧
      α t * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum (R t ω) (G t ω) <
        specNorm (R t ω)} ≤ ENNReal.ofReal δ := by
  let : ∀ t, Nonempty (Fin (s t)) := fun t => Fin.pos_iff_nonempty.mp (hs t)
  let E : ℕ → Set Ω := fun t => {ω |
    α t * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum (R t ω) (G t ω) < specNorm (R t ω)}
  have hstage (t : ℕ) : μ (E t) ≤ ENNReal.ofReal (((α t)⁻¹) ^ s t) := by
    have hind : IndepFun (R t) (G t) μ := by
      rw [IndepFun_iff_Indep, Indep_iff]
      intro u v hu hv
      exact (Indep_iff _ _ _).mp (hfresh t) u v ((hR t).comap_le u hu) hv
    simpa only [Fintype.card_fin] using
      measure_specNorm_gt_gaussianResidualMaximum_le_of_indepFun
        ((hR t).mono (hF t) le_rfl).aemeasurable (hG t) hind (hα t)
  have hall : μ (⋃ t, E t) ≤ ENNReal.ofReal δ :=
    (measure_iUnion_le E).trans ((ENNReal.tsum_le_tsum hstage).trans hbudget)
  have he : {ω | ∃ t, α t * Real.sqrt (2 / Real.pi) *
      gaussianResidualMaximum (R t ω) (G t ω) < specNorm (R t ω)} = ⋃ t, E t := by
    ext ω
    simp [E]
  refine ⟨he ▸ hall, ?_⟩
  apply (measure_mono (show {ω | ∃ t : ℕ, τ ω = (t : WithTop ℕ) ∧
      α t * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum (R t ω) (G t ω) <
        specNorm (R t ω)} ⊆ ⋃ t, E t from ?_)).trans hall
  rintro ω ⟨t, _, ht⟩
  exact Set.mem_iUnion.mpr ⟨t, ht⟩

end NLAlib
