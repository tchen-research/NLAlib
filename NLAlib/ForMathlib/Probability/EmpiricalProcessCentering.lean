import NLAlib.ForMathlib.MeasureTheory.ContinuousSupremum
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Independent-copy centering for bounded continuous parameter tests

The parameter class may be uncountable. Continuity in the actual sample
variable proves supremum measurability, while uniform bounds prove every
displayed integrability statement. No desired expectation comparison is
assumed.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace MeasureTheory

variable {ι T Ω : Type*} [Fintype ι] [Nonempty T]
  [TopologicalSpace Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]

/-- Actual independent copies bound the expected supremum of bounded
continuous finite-coordinate tests by the uniform mean budget plus the
expected supremum of their copy differences. Marginals may differ and
the parameter class may be uncountable; no integrability premise is needed. -/
theorem integral_ciSup_sum_pi_le_mean_add_integral_copy_sub
    (X : ι → Ω → T → ℝ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R v : ℝ} (hX : ∀ i ω t, |X i ω t| ≤ R)
    (hmean : ∀ t, (∑ i, ∫ ω, X i ω t ∂ν i) ≤ v) :
    (∫ x : ι → Ω, ⨆ t, ∑ i, X i (x i) t ∂Measure.pi ν) ≤
      v + ∫ p : (ι → Ω) × (ι → Ω), ⨆ t,
        ∑ i, (X i (p.1 i) t - X i (p.2 i) t)
          ∂(Measure.pi ν).prod (Measure.pi ν) := by
  let μ := Measure.pi ν
  let F (x : ι → Ω) (t : T) := ∑ i, X i (x i) t
  let D (p : (ι → Ω) × (ι → Ω)) (t : T) :=
    ∑ i, (X i (p.1 i) t - X i (p.2 i) t)
  have hFc (t : T) : Continuous (fun x => F x t) := by
    dsimp [F]
    exact continuous_finsetSum _ fun i _ => (hXc i t).comp (continuous_apply i)
  have hDc (t : T) : Continuous (fun p => D p t) := by
    dsimp [D]
    apply continuous_finsetSum
    intro i _
    exact ((hXc i t).comp ((continuous_apply i).comp continuous_fst)).sub
      ((hXc i t).comp ((continuous_apply i).comp continuous_snd))
  have hFb (x : ι → Ω) (t : T) : |F x t| ≤ (Fintype.card ι : ℝ) * R := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans <|
      (Finset.sum_le_sum fun i _ => hX i (x i) t).trans_eq (by simp)
  have hDb (p : (ι → Ω) × (ι → Ω)) (t : T) :
      |D p t| ≤ (Fintype.card ι : ℝ) * (2 * R) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : ι, (2 * R) := by
        apply Finset.sum_le_sum
        intro i _
        have hsub : |X i (p.1 i) t - X i (p.2 i) t| ≤
            |X i (p.1 i) t| + |X i (p.2 i) t| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (X i (p.1 i) t) (-(X i (p.2 i) t))
        exact hsub.trans (by linarith [hX i (p.1 i) t, hX i (p.2 i) t])
      _ = _ := by simp
  have hFi := integrable_ciSup_of_continuous_of_abs_le μ F hFc hFb
  have hDi := integrable_ciSup_of_continuous_of_abs_le (μ.prod μ) D hDc hDb
  have hsection (x : ι → Ω) : Integrable (fun y => ⨆ t, D (x, y) t) μ := by
    apply integrable_ciSup_of_continuous_of_abs_le μ
      (fun y t => D (x, y) t) (fun t => (hDc t).comp (continuous_const.prodMk continuous_id))
    exact fun y t => hDb (x, y) t
  have hpoint (x : ι → Ω) : (⨆ t, F x t) ≤ v + ∫ y, ⨆ t, D (x, y) t ∂μ := by
    apply ciSup_le
    intro t
    have hXi (i : ι) : Integrable (fun ω => X i ω t) (ν i) := by
      apply Integrable.of_bound (hXc i t).measurable.aestronglyMeasurable R
      exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hX i ω t
    have hY (i : ι) : Integrable (fun y : ι → Ω => X i (y i) t) μ :=
      integrable_comp_eval (μ := ν) (i := i) (hXi i)
    have hsubi (i : ι) : Integrable (fun y : ι → Ω => X i (x i) t - X i (y i) t) μ := by
      convert! (integrable_const (X i (x i) t)).sub (hY i) using 1
    have htest : Integrable (fun y => D (x, y) t) μ := by
      exact integrable_finsetSum Finset.univ (fun i _ => hsubi i)
    have heach (i : ι) : (∫ y : ι → Ω, X i (x i) t - X i (y i) t ∂μ) =
        X i (x i) t - ∫ ω, X i ω t ∂ν i := by
      rw [integral_sub (integrable_const (X i (x i) t)) (hY i)]
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      exact integral_comp_eval (μ := ν) (hXi i).aestronglyMeasurable
    have he : (∫ y, D (x, y) t ∂μ) = F x t - ∑ i, ∫ ω, X i ω t ∂ν i := by
      dsimp only [D, F]
      rw [integral_finsetSum _ (fun i _ => hsubi i)]
      simp_rw [heach]
      exact Finset.sum_sub_distrib _ _
    have hle := integral_mono htest (hsection x) (fun y =>
      le_ciSup (⟨(Fintype.card ι : ℝ) * (2 * R), by
        rintro _ ⟨u, rfl⟩
        exact (le_abs_self _).trans (hDb (x, y) u)⟩) t)
    rw [he] at hle
    linarith [hmean t]
  have hle := integral_mono hFi ((integrable_const v).add hDi.integral_prod_left) hpoint
  change (∫ x, ⨆ t, F x t ∂μ) ≤ ∫ x, v + ∫ y, ⨆ t, D (x, y) t ∂μ ∂μ at hle
  rw [integral_add (integrable_const _) hDi.integral_prod_left,
    integral_const, probReal_univ, one_smul, ← integral_prod _ hDi] at hle
  exact hle

end MeasureTheory
