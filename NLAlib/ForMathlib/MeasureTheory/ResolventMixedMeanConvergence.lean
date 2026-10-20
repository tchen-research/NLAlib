import NLAlib.ForMathlib.MeasureTheory.ResolventPowerConvergence
import NLAlib.ForMathlib.Algebra.ResolventMixedPowers

/-!
# Actual mixed resolvent means follow from positive-power means

The true two-parameter resolvent identity reduces every mixed power of
positive total degree to pure powers at its two distinct nonreal parameters.
The integral identity and convergence theorem use genuine Bochner means and
allow varying sample spaces and C*-algebras, including trivial algebras.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace MeasureTheory
variable {Ω A E : Type*} [MeasurableSpace Ω] [CStarAlgebra A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

private theorem norm_pow_cstar_le (a : A) (n : ℕ) : ‖a^n‖≤‖a‖^n := by
  cases subsingleton_or_nontrivial A with
  | inl h =>
    let := h
    simpa only [Subsingleton.elim (a^n) 0,norm_zero] using pow_nonneg (norm_nonneg a) n
  | inr h =>
    let := h
    exact norm_pow_le a n

/-- Every mixed power of two nonreal self-adjoint resolvents is genuinely integrable under a finite measure. -/
theorem integrable_resolvent_selfAdjoint_mixed_powers
    (X : Ω → selfAdjoint A) (hX : AEStronglyMeasurable X μ)
    {z w : ℂ} (hz : z.im≠0) (hw : w.im≠0) (p q : ℕ) :
    Integrable (fun ω => resolvent (X ω : A) z^p*resolvent (X ω : A) w^q) μ := by
  apply Integrable.of_bound
    ((((selfAdjoint.continuous_resolvent hz).pow p).mul
      ((selfAdjoint.continuous_resolvent hw).pow q)).comp_aestronglyMeasurable hX)
    (|z.im|⁻¹^p*|w.im|⁻¹^q)
  apply Filter.Eventually.of_forall
  intro ω
  apply (norm_mul_le _ _).trans
  apply mul_le_mul
    ((norm_pow_cstar_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _)
      ((X ω).property.norm_resolvent_le hz) p))
    ((norm_pow_cstar_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _)
      ((X ω).property.norm_resolvent_le hw) q)) (norm_nonneg _) (by positivity)

/-- A genuine continuous linear observable of the Bochner mean of a mixed resolvent power. -/
def resolventMixedMean (μ : Measure Ω) (X : Ω → selfAdjoint A)
    (L : A →L[ℂ] E) (p q : ℕ) (z w : ℂ) : E :=
  L (∫ ω, resolvent (X ω : A) z^p*resolvent (X ω : A) w^q ∂μ)

/-- The actual mixed-power Bochner mean satisfies the finite lower-degree resolvent recursion. -/
theorem sub_smul_resolventMixedMean
    (X : Ω → selfAdjoint A) (hX : AEStronglyMeasurable X μ)
    (L : A →L[ℂ] E) {z w : ℂ} (hz : z.im≠0) (hw : w.im≠0) (p q : ℕ) :
    (w-z)•resolventMixedMean μ X L (p+1) (q+1) z w=
      resolventMixedMean μ X L (p+1) q z w-resolventMixedMean μ X L p (q+1) z w := by
  unfold resolventMixedMean
  rw [← L.map_smul, ← integral_smul]
  have he : (fun ω => (w-z)•(resolvent (X ω : A) z^(p+1)*resolvent (X ω : A) w^(q+1)))=
      (fun ω => resolvent (X ω : A) z^(p+1)*resolvent (X ω : A) w^q-
        resolvent (X ω : A) z^p*resolvent (X ω : A) w^(q+1)) := by
    funext ω
    exact spectrum.sub_smul_resolvent_pow_mul_pow (X ω : A)
      ((X ω).property.isUnit_algebraMap_sub_of_im_ne_zero hz)
      ((X ω).property.isUnit_algebraMap_sub_of_im_ne_zero hw) p q
  rw [he,integral_sub (integrable_resolvent_selfAdjoint_mixed_powers X hX hz hw (p+1) q)
    (integrable_resolvent_selfAdjoint_mixed_powers X hX hz hw p (q+1)),L.map_sub]

section Convergence
variable {ι A₀ : Type*} [CStarAlgebra A₀]
  {Ω' B : ι → Type*} [∀ i, MeasurableSpace (Ω' i)] [∀ i, CStarAlgebra (B i)]

/-- Convergence of every genuine positive-power mean at two distinct nonreal parameters implies convergence of every genuine mixed mean of positive total degree. -/
theorem tendsto_resolventMixedMean_of_powers
    (μ' : (i : ι) → Measure (Ω' i)) [∀ i, IsFiniteMeasure (μ' i)]
    (X : (i : ι) → Ω' i → selfAdjoint (B i))
    (hX : ∀ i, AEStronglyMeasurable (X i) (μ' i))
    (L : (i : ι) → B i →L[ℂ] E) (a : selfAdjoint A₀) (L₀ : A₀ →L[ℂ] E)
    (f : Filter ι) {z w : ℂ} (hz : z.im≠0) (hw : w.im≠0) (hzw : z≠w)
    (hzlim : ∀ k : ℕ, Tendsto (fun i => resolventPowerMean (μ' i) (X i) (L i) (k+1) z)
      f (𝓝 (L₀ (resolvent (a : A₀) z^(k+1)))))
    (hwlim : ∀ k : ℕ, Tendsto (fun i => resolventPowerMean (μ' i) (X i) (L i) (k+1) w)
      f (𝓝 (L₀ (resolvent (a : A₀) w^(k+1)))))
    (p q : ℕ) (hpq : 0<p+q) :
    Tendsto (fun i => resolventMixedMean (μ' i) (X i) (L i) p q z w)
      f (𝓝 (L₀ (resolvent (a : A₀) z^p*resolvent (a : A₀) w^q))) := by
  have hc : w-z≠0 := sub_ne_zero.mpr hzw.symm
  have hall (n : ℕ) : ∀ p q : ℕ, p+q=n → 0<n →
      Tendsto (fun i => resolventMixedMean (μ' i) (X i) (L i) p q z w)
        f (𝓝 (L₀ (resolvent (a : A₀) z^p*resolvent (a : A₀) w^q))) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q he hn
      cases p with
      | zero =>
        cases q with
        | zero => omega
        | succ q => simpa only [resolventMixedMean,resolventPowerMean,pow_zero,one_mul] using hwlim q
      | succ p =>
        cases q with
        | zero => simpa only [resolventMixedMean,resolventPowerMean,pow_zero,mul_one] using hzlim p
        | succ q =>
          have h₁ := ih (p+1+q) (by omega) (p+1) q rfl (by omega)
          have h₂ := ih (p+(q+1)) (by omega) p (q+1) rfl (by omega)
          have ht := (h₁.sub h₂).const_smul (w-z)⁻¹
          have hi (i : ι) := sub_smul_resolventMixedMean (X i) (hX i) (L i) hz hw p q
          have h₀ := congrArg L₀ (spectrum.sub_smul_resolvent_pow_mul_pow (a : A₀)
            (a.property.isUnit_algebraMap_sub_of_im_ne_zero hz)
            (a.property.isUnit_algebraMap_sub_of_im_ne_zero hw) p q)
          simp only [map_smul,map_sub] at h₀
          simp_rw [← hi,← h₀,inv_smul_smul₀ hc] at ht
          exact ht
  exact hall (p+q) p q rfl hpq

end Convergence
end MeasureTheory
