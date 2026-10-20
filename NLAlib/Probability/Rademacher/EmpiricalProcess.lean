import NLAlib.ForMathlib.Probability.EmpiricalProcessCentering
import NLAlib.ForMathlib.Probability.IndependentCopySwaps
import NLAlib.Probability.Rademacher.Contraction
import Mathlib.Tactic.NormNum

/-!
# Actual symmetrization of bounded continuous empirical processes

The parameter type is arbitrary and nonempty. All laws are the literal
finite products of the given coordinate marginals and the native
`rademacherVector`. Supremum measurability follows from continuity in
actual samples, with no countability or maximizing-parameter premise.

This is a prerequisite for independent-sum spectral universality; it does
not assume or prove that full spectral comparison.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical

namespace NLAlib

variable {ι T : Type*} [Fintype ι] [Nonempty T]

omit [Nonempty T] in
private theorem abs_sum_mul_le_sum_abs (Y : ι → T → ℝ) {R : ℝ}
    (hY : ∀ i t, |Y i t| ≤ R) (r : ι → ℝ) (t : T) :
    |∑ i, r i * Y i t| ≤ ∑ i, |r i| * |R| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hY i t).trans (le_abs_self R)) (abs_nonneg _)

private theorem integrable_signed_sup_fixed
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (Y : ι → S → T → ℝ)
    (hYc : ∀ i t, Continuous (fun x => Y i x t)) {R : ℝ}
    (hY : ∀ i x t, |Y i x t| ≤ R) (r : ι → ℝ) :
    Integrable (fun x => ⨆ t, ∑ i, r i * Y i x t) μ := by
  apply integrable_ciSup_of_continuous_of_abs_le μ
    (fun x t => ∑ i, r i * Y i x t)
  · intro t
    exact continuous_finsetSum _ fun i _ => (hYc i t).const_mul (r i)
  · intro x t
    exact abs_sum_mul_le_sum_abs (fun i t => Y i x t) (fun i t => hY i x t) r t

/-- The actual joint sample/sign supremum is integrable. The sample
tests are continuous and bounded, while the coefficient vector has the
genuine product Rademacher law. The parameter class can be uncountable. -/
theorem integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous
    {S : Type*} [TopologicalSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : ι → S → T → ℝ) (hYc : ∀ i t, Continuous (fun x => Y i x t))
    {R : ℝ} (hY : ∀ i x t, |Y i x t| ≤ R) :
    Integrable (fun p : S × (ι → ℝ) => ⨆ t, ∑ i, p.2 i * Y i p.1 t)
      (μ.prod (rademacherVector ι)) := by
  have hm : Measurable (fun p : S × (ι → ℝ) => ⨆ t, ∑ i, p.2 i * Y i p.1 t) := by
    apply measurable_ciSup_of_continuous_of_bddAbove
    · intro t
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_snd).mul ((hYc i t).comp continuous_fst)
    · intro p
      exact ⟨∑ i, |p.2 i| * |R|, by
        rintro _ ⟨t, rfl⟩
        exact (le_abs_self _).trans
          (abs_sum_mul_le_sum_abs (fun i t => Y i p.1 t) (fun i t => hY i p.1 t) p.2 t)⟩
  apply Integrable.of_bound hm.aestronglyMeasurable ((Fintype.card ι : ℝ) * |R|)
  have hr : ∀ᵐ p : S × (ι → ℝ) ∂μ.prod (rademacherVector ι), ‖p.2‖ ≤ 1 :=
    (measurePreserving_snd (μ := μ) (ν := rademacherVector ι)).quasiMeasurePreserving.ae
      (ae_norm_le_one_rademacherVector (κ := ι))
  filter_upwards [hr] with p hp
  rw [Real.norm_eq_abs]
  apply Real.abs_ciSup_le_of_abs_le
  intro t
  apply (abs_sum_mul_le_sum_abs (fun i t => Y i p.1 t) (fun i t => hY i p.1 t) p.2 t).trans
  calc
    _ ≤ ∑ _i : ι, |R| := by
      apply Finset.sum_le_sum
      intro i _
      have hi : |p.2 i| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm p.2 i).trans hp
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (abs_nonneg R)
    _ = _ := by simp

section ProductSamples

variable {Ω : Type*} [TopologicalSpace Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]

private theorem integral_signed_copy_sub_eq
    (X : ι → Ω → T → ℝ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R : ℝ} (hX : ∀ i ω t, |X i ω t| ≤ R)
    (r : ι → ℝ) (hr : ∀ i, r i = 1 ∨ r i = -1) :
    (∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
      ∑ i, r i * (X i (p.1 i) t - X i (p.2 i) t)
        ∂(Measure.pi ν).prod (Measure.pi ν)) =
      ∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
        ∑ i, (X i (p.1 i) t - X i (p.2 i) t)
          ∂(Measure.pi ν).prod (Measure.pi ν) := by
  let pairLaw := Measure.pi fun i => (ν i).prod (ν i)
  let U (q : ι → Ω × Ω) := ⨆ t, ∑ i, (X i (q i).1 t - X i (q i).2 t)
  let V (q : ι → Ω × Ω) := ⨆ t, ∑ i, r i * (X i (q i).1 t - X i (q i).2 t)
  have hUc (t : T) : Continuous (fun q : ι → Ω × Ω =>
      ∑ i, (X i (q i).1 t - X i (q i).2 t)) := by
    exact continuous_finsetSum _ fun i _ =>
      ((hXc i t).comp (continuous_fst.comp (continuous_apply i))).sub
        ((hXc i t).comp (continuous_snd.comp (continuous_apply i)))
  have hUb (q : ι → Ω × Ω) (t : T) :
      |∑ i, (X i (q i).1 t - X i (q i).2 t)| ≤
        (Fintype.card ι : ℝ) * (2 * |R|) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : ι, (2 * |R|) := by
        apply Finset.sum_le_sum
        intro i _
        have hs : |X i (q i).1 t - X i (q i).2 t| ≤
            |X i (q i).1 t| + |X i (q i).2 t| := abs_sub _ _
        exact hs.trans (by linarith [hX i (q i).1 t, hX i (q i).2 t, le_abs_self R])
      _ = _ := by simp
  have hUi : Integrable U pairLaw := integrable_ciSup_of_continuous_of_abs_le pairLaw _ hUc hUb
  have hswap (q : ι → Ω × Ω) :
      U (fun i => if r i = -1 then (q i).swap else q i) = V q := by
    dsimp only [U, V]
    congr 1
    funext t
    apply Finset.sum_congr rfl
    intro i _
    rcases hr i with hi | hi
    · norm_num [hi]
    · simp only [hi, if_true, Prod.swap, neg_one_mul]
      ring
  have hMP := measurePreserving_arrowProdEquivProdArrow Ω Ω ι ν ν
  have hU := hMP.integral_comp' (fun p : (ι → Ω) × (ι → Ω) =>
    ⨆ t, ∑ i, (X i (p.1 i) t - X i (p.2 i) t))
  have hV := hMP.integral_comp' (fun p : (ι → Ω) × (ι → Ω) =>
    ⨆ t, ∑ i, r i * (X i (p.1 i) t - X i (p.2 i) t))
  change (∫ q, U q ∂pairLaw) = _ at hU
  change (∫ q, V q ∂pairLaw) = _ at hV
  calc
    _ = ∫ q, V q ∂pairLaw := hV.symm
    _ = ∫ q, U (fun i => if r i = -1 then (q i).swap else q i) ∂pairLaw := by
      apply integral_congr_ae
      exact ae_of_all _ fun q => (hswap q).symm
    _ = ∫ q, U q ∂pairLaw :=
      integral_pi_prod_swap_if ν (fun i => r i = -1) U hUi.aestronglyMeasurable
    _ = _ := hU

private theorem integral_signed_copy_sub_le_add
    (X : ι → Ω → T → ℝ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R : ℝ} (hX : ∀ i ω t, |X i ω t| ≤ R) (r : ι → ℝ) :
    (∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
      ∑ i, r i * (X i (p.1 i) t - X i (p.2 i) t)
        ∂(Measure.pi ν).prod (Measure.pi ν)) ≤
      (∫ x : ι → Ω, ⨆ t, ∑ i, r i * X i (x i) t ∂Measure.pi ν) +
        ∫ x : ι → Ω, ⨆ t, ∑ i, r i * (-X i (x i) t) ∂Measure.pi ν := by
  let μ := Measure.pi ν
  have hDc (i : ι) (t : T) : Continuous (fun p : (ι → Ω) × (ι → Ω) =>
      X i (p.1 i) t - X i (p.2 i) t) :=
    ((hXc i t).comp ((continuous_apply i).comp continuous_fst)).sub
      ((hXc i t).comp ((continuous_apply i).comp continuous_snd))
  have hDb (i : ι) (p : (ι → Ω) × (ι → Ω)) (t : T) :
      |X i (p.1 i) t - X i (p.2 i) t| ≤ 2 * |R| :=
    (abs_sub _ _).trans
      (by linarith [hX i (p.1 i) t, hX i (p.2 i) t, le_abs_self R])
  have hD := integrable_signed_sup_fixed (μ.prod μ)
    (fun i p t => X i (p.1 i) t - X i (p.2 i) t) hDc hDb r
  have hF := integrable_signed_sup_fixed μ (fun i x t => X i (x i) t)
    (fun i t => (hXc i t).comp (continuous_apply i)) (fun i x t => hX i (x i) t) r
  have hN := integrable_signed_sup_fixed μ (fun i x t => -X i (x i) t)
    (fun i t => ((hXc i t).comp (continuous_apply i)).neg)
    (fun i x t => by simpa only [abs_neg] using hX i (x i) t) r
  have hle := integral_mono hD ((hF.comp_fst μ).add (hN.comp_snd μ)) (fun p => by
    apply ciSup_le
    intro t
    have h1 := le_ciSup (Real.bddAbove_range_sum_mul_of_abs_le
      (fun i t => X i (p.1 i) t) (fun i t => hX i (p.1 i) t) r) t
    have h2 := le_ciSup (Real.bddAbove_range_sum_mul_of_abs_le
      (fun i t => -X i (p.2 i) t)
        (fun i t => by simpa only [abs_neg] using hX i (p.2 i) t) r) t
    calc
      _ = (∑ i, r i * X i (p.1 i) t) + ∑ i, r i * (-X i (p.2 i) t) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := add_le_add h1 h2)
  simp only [Pi.add_apply] at hle
  rw [integral_add (hF.comp_fst μ) (hN.comp_snd μ),
    integral_prod _ (hF.comp_fst μ), integral_prod _ (hN.comp_snd μ)] at hle
  simpa only [integral_const, probReal_univ, one_smul] using hle

/-- Actual independent-copy differences are bounded by twice the expected
one-sided Rademacher supremum. This uses coordinate-copy swaps, not an
outer-absolute contraction principle or any countability of the class. -/
theorem integral_ciSup_sum_copy_sub_le_two_mul_integral_rademacherVector
    (X : ι → Ω → T → ℝ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R : ℝ} (hX : ∀ i ω t, |X i ω t| ≤ R) :
    (∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
      ∑ i, (X i (p.1 i) t - X i (p.2 i) t)
        ∂(Measure.pi ν).prod (Measure.pi ν)) ≤
      2 * ∫ x : ι → Ω, ∫ r : ι → ℝ, ⨆ t,
        ∑ i, r i * X i (x i) t ∂rademacherVector ι ∂Measure.pi ν := by
  let μ := Measure.pi ν
  let F (x : ι → Ω) (r : ι → ℝ) := ⨆ t, ∑ i, r i * X i (x i) t
  let N (x : ι → Ω) (r : ι → ℝ) := ⨆ t, ∑ i, r i * (-X i (x i) t)
  let G (p : (ι → Ω) × (ι → Ω)) (r : ι → ℝ) :=
    ⨆ t, ∑ i, r i * (X i (p.1 i) t - X i (p.2 i) t)
  let d := ∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
    ∑ i, (X i (p.1 i) t - X i (p.2 i) t) ∂μ.prod μ
  have hF : Integrable (fun p : (ι → Ω) × (ι → ℝ) => F p.1 p.2)
      (μ.prod (rademacherVector ι)) :=
    integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous μ
      (fun i x t => X i (x i) t)
      (fun i t => (hXc i t).comp (continuous_apply i)) (fun i x t => hX i (x i) t)
  have hN : Integrable (fun p : (ι → Ω) × (ι → ℝ) => N p.1 p.2)
      (μ.prod (rademacherVector ι)) :=
    integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous μ
      (fun i x t => -X i (x i) t)
      (fun i t => ((hXc i t).comp (continuous_apply i)).neg)
      (fun i x t => by simpa only [abs_neg] using hX i (x i) t)
  have hDc (i : ι) (t : T) : Continuous (fun p : (ι → Ω) × (ι → Ω) =>
      X i (p.1 i) t - X i (p.2 i) t) :=
    ((hXc i t).comp ((continuous_apply i).comp continuous_fst)).sub
      ((hXc i t).comp ((continuous_apply i).comp continuous_snd))
  have hDb (i : ι) (p : (ι → Ω) × (ι → Ω)) (t : T) :
      |X i (p.1 i) t - X i (p.2 i) t| ≤ 2 * |R| :=
    (abs_sub _ _).trans
      (by linarith [hX i (p.1 i) t, hX i (p.2 i) t, le_abs_self R])
  have hG : Integrable (fun q : ((ι → Ω) × (ι → Ω)) × (ι → ℝ) => G q.1 q.2)
      ((μ.prod μ).prod (rademacherVector ι)) :=
    integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous (μ.prod μ)
      (fun i p t => X i (p.1 i) t - X i (p.2 i) t) hDc hDb
  have hsign : ∀ᵐ r : ι → ℝ ∂rademacherVector ι, ∀ i, r i = 1 ∨ r i = -1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i)
  have hconst : (fun r : ι → ℝ => ∫ p, G p r ∂μ.prod μ) =ᵐ[rademacherVector ι]
      fun _ => d := hsign.mono fun r hr => integral_signed_copy_sub_eq ν X hXc hX r hr
  have hle := integral_mono hG.integral_prod_right
    (hF.integral_prod_right.add hN.integral_prod_right)
    (fun r => integral_signed_copy_sub_le_add ν X hXc hX r)
  simp only [Pi.add_apply] at hle
  rw [integral_congr_ae hconst, integral_const, probReal_univ, one_smul,
    integral_add hF.integral_prod_right hN.integral_prod_right] at hle
  have hswapF : (∫ r, ∫ x, F x r ∂μ ∂rademacherVector ι) =
      ∫ x, ∫ r, F x r ∂rademacherVector ι ∂μ :=
    (integral_integral_swap hF).symm
  have hswapN : (∫ r, ∫ x, N x r ∂μ ∂rademacherVector ι) =
      ∫ x, ∫ r, N x r ∂rademacherVector ι ∂μ :=
    (integral_integral_swap hN).symm
  rw [hswapF, hswapN] at hle
  have hneg : (∫ x, ∫ r, N x r ∂rademacherVector ι ∂μ) ≤
      ∫ x, ∫ r, F x r ∂rademacherVector ι ∂μ := by
    apply integral_mono hN.integral_prod_left hF.integral_prod_left
    intro x
    apply integral_ciSup_sum_mul_rademacherVector_le_of_abs_sub_le
      (fun i t => X i (x i) t) (fun i t => -X i (x i) t)
      (fun i t => hX i (x i) t)
      (fun i t => by simpa only [abs_neg] using hX i (x i) t)
    intro i t u
    rw [neg_sub_neg, abs_sub_comm]
  change d ≤ 2 * ∫ x, ∫ r, F x r ∂rademacherVector ι ∂μ
  linarith

omit [TopologicalSpace Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
private theorem ciSup_sum_neg_eq_of_sign_closed
    (X : ι → Ω → T → ℝ) {R : ℝ} (hX : ∀ i ω t, |X i ω t| ≤ R)
    (hneg : ∀ t, ∃ u, ∀ i ω, X i ω u = -X i ω t) (x : ι → Ω) :
    (⨆ t, ∑ i, -X i (x i) t) = ⨆ t, ∑ i, X i (x i) t := by
  have hb : BddAbove (Set.range fun t => ∑ i, X i (x i) t) := by
    simpa only [one_mul] using Real.bddAbove_range_sum_mul_of_abs_le
      (fun i t => X i (x i) t) (fun i t => hX i (x i) t) (fun _ => 1)
  have hn : BddAbove (Set.range fun t => ∑ i, -X i (x i) t) := by
    simpa only [one_mul] using Real.bddAbove_range_sum_mul_of_abs_le
      (fun i t => -X i (x i) t)
      (fun i t => by simpa only [abs_neg] using hX i (x i) t) (fun _ => 1)
  apply le_antisymm
  · apply ciSup_le
    intro t
    obtain ⟨u, hu⟩ := hneg t
    calc
      _ = ∑ i, X i (x i) u := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hu i (x i)).symm
      _ ≤ _ := le_ciSup hb u
  · apply ciSup_le
    intro t
    obtain ⟨u, hu⟩ := hneg t
    calc
      _ = ∑ i, -X i (x i) u := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hu i (x i), neg_neg]
      _ ≤ _ := le_ciSup hn u

/-- For centered coordinate tests and a genuinely sign-closed parameter
class, the expected one-sided Rademacher supremum is bounded by twice the
actual empirical supremum. Means and signs are native scalar operations. -/
theorem integral_ciSup_sum_mul_rademacherVector_le_two_mul_of_centered
    (X : ι → Ω → T → ℝ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R : ℝ} (hX : ∀ i ω t, |X i ω t| ≤ R)
    (hmean : ∀ i t, ∫ ω, X i ω t ∂ν i = 0)
    (hneg : ∀ t, ∃ u, ∀ i ω, X i ω u = -X i ω t) :
    (∫ x : ι → Ω, ∫ r : ι → ℝ, ⨆ t,
      ∑ i, r i * X i (x i) t ∂rademacherVector ι ∂Measure.pi ν) ≤
      2 * ∫ x : ι → Ω, ⨆ t, ∑ i, X i (x i) t ∂Measure.pi ν := by
  let μ := Measure.pi ν
  let F (x : ι → Ω) (r : ι → ℝ) := ⨆ t, ∑ i, r i * X i (x i) t
  let d := ∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
    ∑ i, (X i (p.1 i) t - X i (p.2 i) t) ∂μ.prod μ
  have hF : Integrable (fun p : (ι → Ω) × (ι → ℝ) => F p.1 p.2)
      (μ.prod (rademacherVector ι)) :=
    integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous μ
      (fun i x t => X i (x i) t)
      (fun i t => (hXc i t).comp (continuous_apply i)) (fun i x t => hX i (x i) t)
  have hsign : ∀ᵐ r : ι → ℝ ∂rademacherVector ι, ∀ i, r i = 1 ∨ r i = -1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i)
  have hpoint (r : ι → ℝ) (hr : ∀ i, r i = 1 ∨ r i = -1) :
      (∫ x, F x r ∂μ) ≤ d := by
    have hY (i : ι) (ω : Ω) (t : T) : |r i * X i ω t| ≤ |R| := by
      have hi : |r i| = 1 := by rcases hr i with hi | hi <;> simp [hi]
      rw [abs_mul, hi, one_mul]
      exact (hX i ω t).trans (le_abs_self R)
    have hYmean (t : T) : (∑ i, ∫ ω, r i * X i ω t ∂ν i) ≤ 0 := by
      simp_rw [integral_const_mul, hmean, mul_zero]
      simp
    have h := integral_ciSup_sum_pi_le_mean_add_integral_copy_sub ν
      (fun i ω t => r i * X i ω t)
      (fun i t => (hXc i t).const_mul (r i)) hY hYmean
    have he : (∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
        ∑ i, (r i * X i (p.1 i) t - r i * X i (p.2 i) t) ∂μ.prod μ) =
        ∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
          ∑ i, r i * (X i (p.1 i) t - X i (p.2 i) t) ∂μ.prod μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro p
      dsimp only
      congr 1
      funext t
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [zero_add, he, integral_signed_copy_sub_eq ν X hXc hX r hr] at h
    exact h
  have hle := integral_mono_ae hF.integral_prod_right (integrable_const d)
    (hsign.mono fun r hr => hpoint r hr)
  simp only [integral_const, probReal_univ, one_smul] at hle
  rw [← integral_integral_swap hF] at hle
  have htri := integral_signed_copy_sub_le_add ν X hXc hX (fun _ => 1)
  simp only [one_mul] at htri
  simp_rw [ciSup_sum_neg_eq_of_sign_closed X hX hneg] at htri
  change (∫ x, ∫ r, F x r ∂rademacherVector ι ∂μ) ≤ _
  change d ≤ _ at htri
  linarith

/-- Actual bounded centered tests satisfy the empirical square-supremum
estimate with coefficient `8 * R`. The proof combines copy centering,
actual symmetrization, the checked `2 * R` square contraction, and the
reverse symmetrization for a sign-closed class. No outer absolute value,
countability assumption, or supplied expectation comparison is used. -/
theorem integral_ciSup_sum_sq_le_mean_add_eight_mul_of_centered
    (X : ι → Ω → T → ℝ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R v : ℝ} (hR : 0 ≤ R) (hX : ∀ i ω t, |X i ω t| ≤ R)
    (hmean : ∀ i t, ∫ ω, X i ω t ∂ν i = 0)
    (hneg : ∀ t, ∃ u, ∀ i ω, X i ω u = -X i ω t)
    (hvariance : ∀ t, (∑ i, ∫ ω, X i ω t ^ 2 ∂ν i) ≤ v) :
    (∫ x : ι → Ω, ⨆ t, ∑ i, X i (x i) t ^ 2 ∂Measure.pi ν) ≤
      v + 8 * R * ∫ x : ι → Ω, ⨆ t, ∑ i, X i (x i) t ∂Measure.pi ν := by
  let μ := Measure.pi ν
  have hSq (i : ι) (ω : Ω) (t : T) : |X i ω t ^ 2| ≤ R ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hX i ω t)
  have hcenter := integral_ciSup_sum_pi_le_mean_add_integral_copy_sub ν
    (fun i ω t => X i ω t ^ 2) (fun i t => (hXc i t).pow 2) hSq hvariance
  have hcopy := integral_ciSup_sum_copy_sub_le_two_mul_integral_rademacherVector ν
    (fun i ω t => X i ω t ^ 2) (fun i t => (hXc i t).pow 2) hSq
  have hF := integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous μ
    (fun i x t => X i (x i) t)
    (fun i t => (hXc i t).comp (continuous_apply i)) (fun i x t => hX i (x i) t)
  have hQ := integrable_ciSup_sum_mul_prod_rademacherVector_of_continuous μ
    (fun i x t => X i (x i) t ^ 2)
    (fun i t => ((hXc i t).comp (continuous_apply i)).pow 2) (fun i x t => hSq i (x i) t)
  have hcontract := integral_mono hQ.integral_prod_left
    (hF.integral_prod_left.const_mul (2 * R)) (fun x =>
      integral_ciSup_sum_mul_sq_rademacherVector_le (fun i t => X i (x i) t)
        hR (fun i t => hX i (x i) t))
  rw [integral_const_mul] at hcontract
  have hreverse := integral_ciSup_sum_mul_rademacherVector_le_two_mul_of_centered ν
    X hXc hX hmean hneg
  have hc := mul_le_mul_of_nonneg_left hcontract (by norm_num : (0 : ℝ) ≤ 2)
  have hr := mul_le_mul_of_nonneg_left hreverse (by positivity : 0 ≤ 4 * R)
  nlinarith

end ProductSamples
end NLAlib
