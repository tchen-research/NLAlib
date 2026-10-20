import NLAlib.Probability.Rademacher.ComplexEmpiricalProcess
import NLAlib.Matrix.Norms.BilinearProbes
import NLAlib.ForMathlib.Analysis.Matrix.BilinearFunctional
import NLAlib.ForMathlib.Analysis.Normed.Module.RadialProjection

/-!
# The expectation of actual bilinear square energy

The probes are the genuine complex Euclidean closed unit balls, including
empty matrix dimension. Centering follows by commuting a native continuous
linear probe with Bochner expectation. The empirical-process estimate then
controls the actual matrix quantity without a net or a dimension factor.

This is an independent-sum spectral universality prerequisite, from
arXiv:2201.05142v3, proof of Lemma 5.8.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Classical Matrix.Norms.L2Operator

namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [TopologicalSpace Ω] [SecondCountableTopology Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]

/-- A second-moment budget for genuine bilinear probes controls the expected
native bilinear square mass of bounded centered independent matrix samples.
The square energy and the norm expectation are both evaluated under the
literal product of the coordinate laws. -/
theorem integral_bilinearSquareMass_pi_le
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZc : ∀ i, Continuous (Z i))
    {R v : ℝ} (hR : 0 ≤ R) (hZ : ∀ i ω, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v) :
    (∫ x : ι → Ω, bilinearSquareMass (fun i => Z i (x i)) Finset.univ ∂Measure.pi ν) ≤
      2 * v + 16 * R * ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν := by
  let T := {p : EuclideanSpace ℂ n × EuclideanSpace ℂ n // ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1}
  let : Nonempty T := ⟨⟨(0, 0), by simp⟩⟩
  let X (i : ι) (ω : Ω) (t : T) : ℂ :=
    Matrix.bilinearCLM t.val.1.ofLp t.val.2.ofLp (Z i ω)
  have hXc (i : ι) (t : T) : Continuous (fun ω => X i ω t) :=
    (Matrix.bilinearCLM t.val.1.ofLp t.val.2.ofLp).continuous.comp (hZc i)
  have hX (i : ι) (ω : Ω) (t : T) : ‖X i ω t‖ ≤ R :=
    (norm_star_dotProduct_mulVec_le_specNorm (Z i ω) t.val.1 t.val.2
      t.prop.1 t.prop.2).trans (hZ i ω)
  have hZi (i : ι) : Integrable (Z i) (ν i) :=
    Integrable.of_bound (hZc i).measurable.aestronglyMeasurable R
      (ae_of_all _ fun ω => hZ i ω)
  have hXm (i : ι) (t : T) : ∫ ω, X i ω t ∂ν i = 0 := by
    change (∫ ω, Matrix.bilinearCLM t.val.1.ofLp t.val.2.ofLp (Z i ω) ∂ν i) = 0
    rw [(Matrix.bilinearCLM t.val.1.ofLp t.val.2.ofLp).integral_comp_comm (hZi i),
      hmean i, map_zero]
  have hXn (t : T) : ∃ u, ∀ i ω, X i ω u = -X i ω t := by
    refine ⟨⟨(-t.val.1, t.val.2), by simpa using t.prop⟩, fun i ω => ?_⟩
    simp [X, Matrix.bilinearCLM_apply, star_neg, neg_dotProduct]
  have hXv (t : T) : (∑ i, ∫ ω, ‖X i ω t‖ ^ 2 ∂ν i) ≤ v :=
    hvariance t.val.1 t.val.2 t.prop.1 t.prop.2
  have heq (x : ι → Ω) :
      bilinearSquareMass (fun i => Z i (x i)) Finset.univ =
        ⨆ t, ∑ i, ‖X i (x i) t‖ ^ 2 := by
    have hb : BddAbove (Set.range fun t => ∑ i, ‖X i (x i) t‖ ^ 2) := by
      refine ⟨∑ _i : ι, R ^ 2, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) hR).mpr (hX i (x i) t)
    apply le_antisymm
    · obtain ⟨a, b, ha, hb', he⟩ := exists_bilinearSquareMass_eq (fun i => Z i (x i)) Finset.univ
      rw [he]
      simpa [X, Matrix.bilinearCLM_apply] using le_ciSup hb (⟨(a, b), ha, hb'⟩ : T)
    · apply ciSup_le
      intro t
      simpa [X, Matrix.bilinearCLM_apply] using
        sum_bilinear_sq_le_bilinearSquareMass (fun i => Z i (x i)) Finset.univ
          t.val.1 t.val.2 t.prop.1 t.prop.2
  have hnorm (x : ι → Ω) (t : T) : ‖∑ i, X i (x i) t‖ ≤ specNorm (∑ i, Z i (x i)) := by
    rw [show (∑ i, X i (x i) t) =
        Matrix.bilinearCLM t.val.1.ofLp t.val.2.ofLp (∑ i, Z i (x i)) by
      simp only [X, map_sum]]
    exact norm_star_dotProduct_mulVec_le_specNorm _ t.val.1 t.val.2 t.prop.1 t.prop.2
  have hNi : Integrable (fun x : ι → Ω => specNorm (∑ i, Z i (x i))) (Measure.pi ν) := by
    have hm : Measurable (fun x : ι → Ω => specNorm (∑ i, Z i (x i))) := by
      simpa only [specNorm_eq_norm, Function.comp_def] using
        (continuous_finsetSum _ fun i _ => (hZc i).comp (continuous_apply i)).norm.measurable
    apply Integrable.of_bound hm.aestronglyMeasurable (∑ _i : ι, R)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (specNorm_nonneg _)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hZ i (x i))
  have hSi : Integrable (fun x : ι → Ω => ⨆ t, ‖∑ i, X i (x i) t‖) (Measure.pi ν) := by
    apply integrable_ciSup_of_continuous_of_abs_le (Measure.pi ν)
      (fun x t => ‖∑ i, X i (x i) t‖)
    · intro t
      exact (continuous_finsetSum _ fun i _ => (hXc i t).comp (continuous_apply i)).norm
    · intro x t
      rw [abs_of_nonneg (norm_nonneg _)]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hX i (x i) t)
  have hle : (∫ x : ι → Ω, ⨆ t, ‖∑ i, X i (x i) t‖ ∂Measure.pi ν) ≤
      ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν :=
    integral_mono hSi hNi (fun x => ciSup_le (hnorm x))
  simp_rw [heq]
  have h := integral_ciSup_sum_norm_sq_le_mean_add_sixteen_mul_of_centered
    ν X hXc hR hX hXm hXn hXv
  nlinarith

/-- The same native expectation estimate for merely measurable,
almost-everywhere bounded matrix samples. Radial projection fixes the
actual samples almost everywhere and provides continuous bounded tests on
their matrix-valued laws, so continuity is not a premise of this theorem.
atlas: independent-sum-spectrum-universality (partial) -/
theorem integral_bilinearSquareMass_pi_le_of_ae_bound
    {S : Type*} [MeasurableSpace S]
    (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → S → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R v : ℝ} (hR : 0 ≤ R) (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v) :
    (∫ x : ι → S, bilinearSquareMass (fun i => Z i (x i)) Finset.univ ∂Measure.pi ν) ≤
      2 * v + 16 * R * ∫ x : ι → S, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let ρ (i : ι) : Measure (Matrix n n ℂ) := (ν i).map (Z i)
  let : ∀ i, IsProbabilityMeasure (ρ i) := fun i =>
    Measure.isProbabilityMeasure_map (hZm i).aemeasurable
  let P : Matrix n n ℂ → Matrix n n ℂ := NormedSpace.radialProj R
  have hPc : Continuous P := NormedSpace.continuous_radialProj hR
  have hPB (A : Matrix n n ℂ) : specNorm (P A) ≤ R :=
    NormedSpace.norm_radialProj_le hR A
  have hfix (i : ι) : ∀ᵐ ω ∂ν i, P (Z i ω) = Z i ω :=
    (hZ i).mono fun ω hω => NormedSpace.radialProj_eq_self hR hω
  have hPm (i : ι) : ∫ A, P A ∂ρ i = 0 := by
    rw [integral_map (hZm i).aemeasurable hPc.measurable.aestronglyMeasurable]
    exact (integral_congr_ae (hfix i)).trans (hmean i)
  have hPv (a b : EuclideanSpace ℂ n) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
      (∑ i, ∫ A, ‖star a.ofLp ⬝ᵥ (P A *ᵥ b.ofLp)‖ ^ 2 ∂ρ i) ≤ v := by
    have hc : Continuous (fun A => ‖star a.ofLp ⬝ᵥ (P A *ᵥ b.ofLp)‖ ^ 2) :=
      ((Matrix.bilinearCLM a.ofLp b.ofLp).continuous.comp hPc).norm.pow 2
    calc
      _ = ∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_map (hZm i).aemeasurable hc.measurable.aestronglyMeasurable]
        exact integral_congr_ae ((hfix i).mono fun ω hω => congrArg
          (fun A => ‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖ ^ 2) hω)
      _ ≤ v := hvariance a b ha hb
  let U (x : ι → S) (i : ι) := Z i (x i)
  have hUm : Measurable U := measurable_pi_lambda _ fun i =>
    (hZm i).comp (measurable_pi_apply i)
  have hmap : (Measure.pi ν).map U = Measure.pi ρ :=
    Measure.pi_map_pi (fun i => (hZm i).aemeasurable)
  have hfixPi : ∀ᵐ x : ι → S ∂Measure.pi ν, ∀ i, P (Z i (x i)) = Z i (x i) :=
    ae_all_iff.mpr fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hfix i)
  let F (x : ι → Matrix n n ℂ) := bilinearSquareMass (fun i => P (x i)) Finset.univ
  let G (x : ι → Matrix n n ℂ) := specNorm (∑ i, P (x i))
  have hFc : Continuous F := (continuous_bilinearSquareMass Finset.univ).comp
    (continuous_pi fun i => hPc.comp (continuous_apply i))
  have hGc : Continuous G :=
    (continuous_finsetSum _ fun i _ => hPc.comp (continuous_apply i)).norm
  have hFeq : (∫ x, F x ∂Measure.pi ρ) =
      ∫ x : ι → S, bilinearSquareMass (fun i => Z i (x i)) Finset.univ ∂Measure.pi ν := by
    rw [← hmap, integral_map hUm.aemeasurable hFc.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hfixPi] with x hx
    simp only [F, U, hx]
  have hGeq : (∫ x, G x ∂Measure.pi ρ) =
      ∫ x : ι → S, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν := by
    rw [← hmap, integral_map hUm.aemeasurable hGc.measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hfixPi] with x hx
    simp only [G, U, hx]
  have h := integral_bilinearSquareMass_pi_le ρ (fun _ => P) (fun _ => hPc)
    hR (fun _ => hPB) hPm hPv
  change (∫ x, F x ∂Measure.pi ρ) ≤ 2 * v + 16 * R * ∫ x, G x ∂Measure.pi ρ at h
  rw [hFeq, hGeq] at h
  exact h

end NLAlib
