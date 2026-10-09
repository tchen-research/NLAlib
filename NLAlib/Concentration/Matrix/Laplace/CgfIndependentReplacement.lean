import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Laplace.ProbabilisticLieb
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lieb replacement for an independent random matrix offset

Main declaration: `NLAlib.integral_traceExp_add_le_integral_traceExp_add_matrixLog`.

Atlas: `matrix-laplace` (step of Lemma 3.5.1).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Proof of Lemma 3.5.1, printed pp. 35–36, applying Corollary 3.4.2.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
open NLAlib

/-- For independent Hermitian random matrices `H`, `X`, replacing `X` by `matrixLog 𝔼 matrixExp X`
does not decrease `𝔼 traceExp (H + X)`.

Tropp 2015, proof of Lemma 3.5.1 (via Corollary 3.4.2). Atlas: `matrix-laplace`. Ported from the
Prove2me mission *An Introduction to Matrix Concentration Inequalities, Ch 3*. -/
theorem NLAlib.integral_traceExp_add_le_integral_traceExp_add_matrixLog {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeasH : Measurable H) (hMeasX : Measurable X)
    (hHermH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hHermX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hIndep : IndepFun H X μ)
    (hExpX : Integrable (fun ω => matrixExp (X ω)) μ)
    (hIntTotal : Integrable (fun ω => traceExp (H ω + X ω)) μ)
    (hIntReplaced : Integrable (fun ω =>
      traceExp (H ω + matrixLog (∫ u, matrixExp (X u) ∂μ))) μ) :
    (∫ ω, traceExp (H ω + X ω) ∂μ) ≤
      ∫ ω, traceExp (H ω + matrixLog (∫ u, matrixExp (X u) ∂μ)) ∂μ := by
  let M := Matrix (Fin d) (Fin d) ℂ
  let : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M
  have hc : Continuous (fun p : M × M => traceExp (p.1 + p.2)) := by
    dsimp [traceExp, matrixExp]
    fun_prop
  have hec : Continuous (fun A : M => matrixExp A) := by
    dsimp [matrixExp]
    fun_prop
  have hrc : Continuous (fun A : M =>
      traceExp (A + matrixLog (∫ u, matrixExp (X u) ∂μ))) := by
    dsimp [traceExp, matrixExp]
    fun_prop
  have hclosed : MeasurableSet {A : M | A.IsHermitian} := by
    exact (isClosed_eq continuous_star continuous_id).measurableSet
  have hmap := hIndep.map_prod_eq_prod_map_map hMeasH.aemeasurable hMeasX.aemeasurable
  have hp : Integrable (fun p : M × M => traceExp (p.1 + p.2))
      ((μ.map H).prod (μ.map X)) := by
    rw [← hmap]
    exact (integrable_map_measure hc.aestronglyMeasurable
      (hMeasH.prodMk hMeasX).aemeasurable).2 hIntTotal
  have hr : Integrable (fun A : M =>
      traceExp (A + matrixLog (∫ u, matrixExp (X u) ∂μ))) (μ.map H) :=
    (integrable_map_measure hrc.aestronglyMeasurable hMeasH.aemeasurable).2 hIntReplaced
  have he : Integrable (fun A : M => matrixExp A) (μ.map X) :=
    (integrable_map_measure hec.aestronglyMeasurable hMeasX.aemeasurable).2 hExpX
  have hmx : ∀ᵐ A ∂μ.map X, A.IsHermitian :=
    (ae_map_iff hMeasX.aemeasurable hclosed).2 hHermX
  have hmh : ∀ᵐ A ∂μ.map H, A.IsHermitian :=
    (ae_map_iff hMeasH.aemeasurable hclosed).2 hHermH
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hMeasX.aemeasurable
  calc
    (∫ ω, traceExp (H ω + X ω) ∂μ) =
        ∫ p : M × M, traceExp (p.1 + p.2) ∂((μ.map H).prod (μ.map X)) := by
      rw [← hmap, integral_map (hMeasH.prodMk hMeasX).aemeasurable hc.aestronglyMeasurable]
    _ = ∫ A : M, ∫ B : M, traceExp (A + B) ∂μ.map X ∂μ.map H := integral_prod _ hp
    _ ≤ ∫ A : M, traceExp (A + matrixLog (∫ u, matrixExp (X u) ∂μ)) ∂μ.map H := by
      apply integral_mono_ae hp.integral_prod_left hr
      filter_upwards [hmh] with A hA
      have h := integral_traceExp_add_le_traceExp_add_matrixLog (μ.map X) A hA id measurable_id hmx he
      simpa only [id_eq, integral_map hMeasX.aemeasurable hec.aestronglyMeasurable] using h
    _ = _ := integral_map hMeasH.aemeasurable hrc.aestronglyMeasurable

