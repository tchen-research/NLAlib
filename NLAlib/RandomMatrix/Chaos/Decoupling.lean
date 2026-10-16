import NLAlib.RandomMatrix.Chaos.Integrability

/-!
# One-sided decoupling by finite coloring

The actual product laws, centered coordinate expectations, and integrability
are explicit. Matching color classes give a selected-coordinate product law;
averaging the other coordinates produces the retained chaos exactly.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, Theorem 2.1, upper direction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

variable {τ ι m n : Type*} [Fintype τ] [Fintype ι]
  [Fintype m] [Fintype n] [DecidableEq τ] [DecidableEq ι]
  [DecidableEq m] [DecidableEq n]

/-- Read coordinate `i` from the independent group bearing its color. -/
def chaosRetainedVector (c : ι → τ) (x : τ × ι → ℝ) (i : ι) : ℝ := x (c i, i)

/-- Keep matching color coordinates of the first sample and take every other
coordinate from the independent second sample. -/
def chaosMix (c : ι → τ) (x y : τ × ι → ℝ) (ti : τ × ι) : ℝ :=
  if c ti.2 = ti.1 then x ti else y ti

variable (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

/-- The retained coordinates form exactly one copy of the original coordinate
product law, since their positions `(c i,i)` are distinct. -/
theorem hasLaw_chaosRetainedVector (c : ι → τ) :
    HasLaw (chaosRetainedVector c) (Measure.pi ν)
      (Measure.pi (fun ti : τ × ι => ν ti.2)) := by
  apply hasLaw_pi_select (fun ti : τ × ι => ν ti.2) (fun i => (c i, i))
  intro i j hij
  exact congrArg Prod.snd hij

/-- Mixing matching-color coordinates of two independent product samples does
not change their complete coordinate law. -/
theorem hasLaw_chaosMix (c : ι → τ) :
    HasLaw (fun xy : (τ × ι → ℝ) × (τ × ι → ℝ) => chaosMix c xy.1 xy.2)
      (Measure.pi (fun ti : τ × ι => ν ti.2))
      ((Measure.pi (fun ti : τ × ι => ν ti.2)).prod
        (Measure.pi (fun ti : τ × ι => ν ti.2))) :=
  hasLaw_pi_mix _ (fun ti : τ × ι => c ti.2 = ti.1)

open scoped Matrix.Norms.L2Operator in
/-- Averaging nonretained coordinates kills exactly those monomials that do not
match the coloring. This is the finite conditional-expectation identity used by
decoupling; no abstract conditional expectation is assumed.
atlas: matrix-chaos-decoupling-upper (partial) -/
theorem integral_decoupledMatrixChaos_mix (A : (τ → ι) → Matrix m n ℝ)
    (hν : ∀ i, Integrable id (ν i)) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (c : ι → τ) (x : τ × ι → ℝ) :
    (∫ y : τ × ι → ℝ,
      decoupledMatrixChaos A (fun t i => chaosMix c x y (t, i))
        ∂Measure.pi (fun ti : τ × ι => ν ti.2)) =
      coloredMatrixChaos A c (chaosRetainedVector c x) := by
  have hi (z : τ → ι) : Function.Injective (fun t => (t, z t)) := by
    intro t u htu
    exact congrArg Prod.fst htu
  have hf (z : τ → ι) (t : τ) :
      Integrable (fun u : ℝ => if c (z t) = t then x (t, z t) else u) (ν (z t)) := by
    split_ifs
    · exact integrable_const _
    · exact hν (z t)
  have hint (z : τ → ι) : Integrable
      (fun y : τ × ι → ℝ => (∏ t, chaosMix c x y (t, z t)) • A z)
      (Measure.pi (fun ti : τ × ι => ν ti.2)) :=
    (integrable_prod_pi_select (fun ti : τ × ι => ν ti.2)
      (fun t => (t, z t)) (hi z)
      (fun t u => if c (z t) = t then x (t, z t) else u) (hf z)).smul_const _
  unfold decoupledMatrixChaos coloredMatrixChaos
  rw [integral_finset_sum _ (fun z _ => hint z)]
  apply Finset.sum_congr rfl
  intro z _
  rw [integral_smul_const]
  change (∫ y : τ × ι → ℝ,
    ∏ t, (if c (z t) = t then x (t, z t) else y (t, z t))
      ∂Measure.pi (fun ti : τ × ι => ν ti.2)) • A z = _
  rw [integral_prod_pi_select (fun ti : τ × ι => ν ti.2)
    (fun t => (t, z t)) (hi z)
    (fun t u => if c (z t) = t then x (t, z t) else u) (hf z)]
  have hm (t : τ) :
      (∫ u : ℝ, (if c (z t) = t then x (t, z t) else u) ∂ν (z t)) =
        if c (z t) = t then x (t, z t) else 0 := by
    split_ifs <;> simp [hcenter]
  simp_rw [hm]
  by_cases hz : ∀ t, c (z t) = t
  · simp [hz, chaosRetainedVector]
  · simp only [if_neg hz]
    obtain ⟨t, ht⟩ := not_forall.mp hz
    have hp : (∏ u : τ, if c (z u) = u then x (u, z u) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [ht]
    rw [hp, zero_smul]

open scoped Matrix.Norms.L2Operator in
/-- Every retained-color chaos has expected spectral norm at most the fully
decoupled chaos, by norm Jensen and the exact mixed-coordinate product law.
atlas: matrix-chaos-decoupling-upper (partial) -/
theorem integral_specNorm_coloredMatrixChaos_le (A : (τ → ι) → Matrix m n ℝ)
    (hν : ∀ i, Integrable id (ν i)) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (c : ι → τ) :
    (∫ h, specNorm (coloredMatrixChaos A c h) ∂Measure.pi ν) ≤
      ∫ x : τ × ι → ℝ, specNorm (decoupledMatrixChaos A (fun t i => x (t, i)))
        ∂Measure.pi (fun ti : τ × ι => ν ti.2) := by
  let ρ := Measure.pi (fun ti : τ × ι => ν ti.2)
  let Y : (τ × ι → ℝ) → Matrix m n ℝ :=
    fun x => decoupledMatrixChaos A (fun t i => x (t, i))
  have hY : Integrable Y ρ := integrable_decoupledMatrixChaos ν A hν
  have hcol := integrable_coloredMatrixChaos ν A c hν
  have hret := (hasLaw_chaosRetainedVector ν c).measurePreserving (by
    unfold chaosRetainedVector
    fun_prop)
  have hcolret := hret.integrable_comp_of_integrable hcol
  have hmix := (hasLaw_chaosMix ν c).measurePreserving (by
    apply measurable_pi_lambda
    intro ti
    unfold chaosMix
    split_ifs <;> fun_prop)
  have hjoint : Integrable (fun xy : (τ × ι → ℝ) × (τ × ι → ℝ) =>
      Y (chaosMix c xy.1 xy.2)) (ρ.prod ρ) := hmix.integrable_comp_of_integrable hY
  have hpoint (x : τ × ι → ℝ) :
      ‖coloredMatrixChaos A c (chaosRetainedVector c x)‖ ≤
        ∫ y, ‖Y (chaosMix c x y)‖ ∂ρ := by
    rw [← integral_decoupledMatrixChaos_mix ν A hν hcenter c x]
    exact norm_integral_le_integral_norm _
  have hstep := integral_mono hcolret.norm hjoint.norm.integral_prod_left hpoint
  change (∫ x, ‖coloredMatrixChaos A c (chaosRetainedVector c x)‖ ∂ρ) ≤
    ∫ x, ∫ y, ‖Y (chaosMix c x y)‖ ∂ρ ∂ρ at hstep
  have hleft : (∫ x, ‖coloredMatrixChaos A c (chaosRetainedVector c x)‖ ∂ρ) =
      ∫ h, ‖coloredMatrixChaos A c h‖ ∂Measure.pi ν := by
    simpa only [Function.comp_apply] using
      (hasLaw_chaosRetainedVector ν c).integral_comp hcol.norm.aestronglyMeasurable
  have hright : (∫ x, ∫ y, ‖Y (chaosMix c x y)‖ ∂ρ ∂ρ) = ∫ x, ‖Y x‖ ∂ρ := by
    rw [← integral_prod _ hjoint.norm]
    simpa only [Function.comp_apply] using
      (hasLaw_chaosMix ν c).integral_comp hY.norm.aestronglyMeasurable
  rw [hleft, hright] at hstep
  simpa only [specNorm_eq_norm] using hstep

open scoped Matrix.Norms.L2Operator in
set_option maxHeartbeats 800000 in
/-- A diagonal-free coupled chaos is bounded by its fully decoupled version with
the numerical factor `q^q`. Independent coordinates may have different centered
integrable laws; neither identical distribution nor coefficient permutation
symmetry is needed. The empty coefficient family and `q > m` are included.
Source: the finite coloring proof of Bandeira–Lucca–Nizić-Nikolac–van Handel,
Theorem 2.1, upper direction.
atlas: matrix-chaos-decoupling-upper -/
theorem integral_specNorm_coupledMatrixChaos_le [Nonempty τ]
    (A : (τ → ι) → Matrix m n ℝ) (hA : HasDistinctIndexSupport A)
    (hν : ∀ i, Integrable id (ν i)) (hcenter : ∀ i, ∫ x, x ∂ν i = 0) :
    (∫ h, specNorm (coupledMatrixChaos A h) ∂Measure.pi ν) ≤
      (Fintype.card τ : ℝ) ^ Fintype.card τ *
        ∫ x : τ × ι → ℝ, specNorm (decoupledMatrixChaos A (fun t i => x (t, i)))
          ∂Measure.pi (fun ti : τ × ι => ν ti.2) := by
  let b := (Fintype.card τ : ℝ) ^ Fintype.card τ / Fintype.card (ι → τ)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : (Fintype.card (ι → τ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ι → τ) ≠ 0)
  have hcol (c : ι → τ) :
      Integrable (fun h => specNorm (coloredMatrixChaos A c h)) (Measure.pi ν) := by
    simpa only [specNorm_eq_norm] using (integrable_coloredMatrixChaos ν A c hν).norm
  have hsum : Integrable (fun h => b * ∑ c, specNorm (coloredMatrixChaos A c h))
      (Measure.pi ν) := (integrable_finset_sum _ (fun c _ => hcol c)).const_mul b
  have hstep := integral_mono (integrable_specNorm_coupledMatrixChaos ν A hA hν) hsum
    (fun h => specNorm_coupledMatrixChaos_le_coloring_average A hA h)
  rw [integral_const_mul, integral_finset_sum _ (fun c _ => hcol c)] at hstep
  refine hstep.trans ?_
  calc
    b * ∑ c, ∫ h, specNorm (coloredMatrixChaos A c h) ∂Measure.pi ν ≤
        b * ∑ _ : ι → τ,
          ∫ x : τ × ι → ℝ, specNorm (decoupledMatrixChaos A (fun t i => x (t, i)))
            ∂Measure.pi (fun ti : τ × ι => ν ti.2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun c _ => integral_specNorm_coloredMatrixChaos_le ν A hν hcenter c)) hb
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [b]
      field_simp

open scoped Matrix.Norms.L2Operator in
/-- One-sided matrix-chaos decoupling transports to arbitrary probability spaces
through the actual coupled and decoupled joint laws.
atlas: matrix-chaos-decoupling-upper -/
theorem integral_specNorm_coupledMatrixChaos_le_of_hasLaw [Nonempty τ]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    {h : Ω → ι → ℝ} {g : Ω' → τ × ι → ℝ}
    (hh : HasLaw h (Measure.pi ν) μ)
    (hg : HasLaw g (Measure.pi (fun ti : τ × ι => ν ti.2)) μ')
    (A : (τ → ι) → Matrix m n ℝ) (hA : HasDistinctIndexSupport A)
    (hν : ∀ i, Integrable id (ν i)) (hcenter : ∀ i, ∫ x, x ∂ν i = 0) :
    (∫ ω, specNorm (coupledMatrixChaos A (h ω)) ∂μ) ≤
      (Fintype.card τ : ℝ) ^ Fintype.card τ *
        ∫ ω, specNorm (decoupledMatrixChaos A (fun t i => g ω (t, i))) ∂μ' := by
  have hleft := hh.integral_comp
    (integrable_specNorm_coupledMatrixChaos ν A hA hν).aestronglyMeasurable
  have hright := hg.integral_comp
    (integrable_specNorm_decoupledMatrixChaos ν A hν).aestronglyMeasurable
  simp only [Function.comp_apply] at hleft hright
  rw [hleft, hright]
  exact integral_specNorm_coupledMatrixChaos_le ν A hA hν hcenter

end NLAlib
