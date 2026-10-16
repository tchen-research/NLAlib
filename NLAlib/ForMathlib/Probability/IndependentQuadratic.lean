import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Algebra.BigOperators.Pi

/-!
# Independent quadratic contractions

A square-integrable real vector and an independent bounded random operator
factor through the vector's full coordinate second-moment tensor. The product
integrability follows from the second moment and the operator bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {κ Ω V F : Type*} [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem bilin_quadratic_pi_expansion
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) (L : (κ → ℝ) →L[ℝ] F) (x : κ → ℝ) :
    B x (L x) = ∑ i, ∑ j, (x i * x j) • B (Pi.single i 1) (L (Pi.single j 1)) := by
  have hx : B x (L x) = ∑ i, x i • B (Pi.single i 1) (L x) := by
    simpa only [map_sum, map_smul, sum_apply, smul_apply] using
      congrArg (fun v : κ → ℝ => B v (L x)) (pi_eq_sum_univ' x)
  have hL : L x = ∑ j, x j • L (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [hx, hL]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]

omit [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] in
private theorem quadratic_coefficient_bound
    (T : V → (κ → ℝ) →L[ℝ] F) (C : ℝ) (hT : ∀ v, ‖T v‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) (i j : κ) (v : V) :
    ‖B (Pi.single i 1) (T v (Pi.single j 1))‖ ≤
      ‖B (Pi.single i 1)‖ * (C * ‖(Pi.single j (1 : ℝ) : κ → ℝ)‖) := by
  exact ((B (Pi.single i 1)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left ((T v).le_opNorm _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hT v) (norm_nonneg _)) (norm_nonneg _)))

/-- A bounded continuous operator-valued random coefficient can be contracted
quadratically with any L² finite real vector. No independence is needed for
this integrability statement.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integrable_bilin_quadratic_of_memLp
    (D : Ω → κ → ℝ) (hD : MemLp D 2 P) (W : Ω → V) (hW : AEMeasurable W P)
    (T : V → (κ → ℝ) →L[ℝ] F) (hTc : Continuous T)
    (C : ℝ) (hT : ∀ v, ‖T v‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    Integrable (fun ω => B (D ω) (T (W ω) (D ω))) P := by
  have hi (i j : κ) : Integrable
      (fun ω => (D ω i * D ω j) • B (Pi.single i 1) (T (W ω) (Pi.single j 1))) P := by
    have hprod : Integrable (fun ω => D ω i * D ω j) P :=
      ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 (hD.eval i) (hD.eval j)).integrable le_rfl
    have hGc : Continuous (fun v => B (Pi.single i 1) (T v (Pi.single j 1))) :=
      (B _).continuous.comp (hTc.clm_apply continuous_const)
    exact hprod.smul_bdd _ (hGc.measurable.comp_aemeasurable hW).aestronglyMeasurable
      (ae_of_all _ fun ω => quadratic_coefficient_bound T C hT B i j (W ω))
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  exact hs.congr (ae_of_all _ fun ω =>
    (bilin_quadratic_pi_expansion B (T (W ω)) (D ω)).symm)

/-- Independence factors a quadratic contraction into the actual second-moment
tensor and the independent operator coefficient. Every integral is genuine:
the vector is L² and the continuous operator field is uniformly bounded.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_quadratic_eq_sum_of_indepFun
    (D : Ω → κ → ℝ) (hD : MemLp D 2 P) (W : Ω → V) (hW : AEMeasurable W P)
    (hDW : IndepFun D W P)
    (T : V → (κ → ℝ) →L[ℝ] F) (hTc : Continuous T)
    (C : ℝ) (hT : ∀ v, ‖T v‖ ≤ C)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    (∫ ω, B (D ω) (T (W ω) (D ω)) ∂P) =
      ∑ i, ∑ j, (∫ ω, D ω i * D ω j ∂P) •
        ∫ ω, B (Pi.single i 1) (T (W ω) (Pi.single j 1)) ∂P := by
  have hprod (i j : κ) : Integrable (fun ω => D ω i * D ω j) P :=
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1 (hD.eval i) (hD.eval j)).integrable le_rfl
  have hGc (i j : κ) : Continuous (fun v => B (Pi.single i 1) (T v (Pi.single j 1))) :=
    (B _).continuous.comp (hTc.clm_apply continuous_const)
  have hG (i j : κ) : Integrable
      (fun ω => B (Pi.single i 1) (T (W ω) (Pi.single j 1))) P :=
    Integrable.of_bound ((hGc i j).measurable.comp_aemeasurable hW).aestronglyMeasurable _
      (ae_of_all _ fun ω => quadratic_coefficient_bound T C hT B i j (W ω))
  have hind (i j : κ) : IndepFun (fun ω => D ω i * D ω j)
      (fun ω => B (Pi.single i 1) (T (W ω) (Pi.single j 1))) P :=
    hDW.comp (show Measurable (fun x : κ → ℝ => x i * x j) by fun_prop)
      (hGc i j).measurable
  have hi (i j : κ) := (hind i j).integrable_smul (hprod i j) (hG i j)
  have he : (fun ω => B (D ω) (T (W ω) (D ω))) =
      fun ω => ∑ i, ∑ j, (D ω i * D ω j) • B (Pi.single i 1) (T (W ω) (Pi.single j 1)) := by
    funext ω
    exact bilin_quadratic_pi_expansion B (T (W ω)) (D ω)
  rw [he, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  exact (hind i j).integral_fun_smul_eq_smul_integral
    (hprod i j).aestronglyMeasurable (hG i j).aestronglyMeasurable

end NLAlib
