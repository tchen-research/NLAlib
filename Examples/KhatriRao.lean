import NLAlib.Sketching.Structured.KhatriRaoGrowth
import NLAlib.Sketching.Structured.KhatriRaoSigns
import NLAlib.Sketching.Structured.KhatriRaoLowerGrowth

/-!
# Applying the sharp Khatri--Rao embedding bounds

The upper example combines fixed-parameter rank growth with an actual
independent-sign law. The lower example uses the explicit order-two
tensor witness, with the same concrete law and no hypothetical moment
or concentration certificate.
-/

noncomputable section
open MeasureTheory Matrix
open NLAlib

example {d r m : ℕ} {n : Fin d → ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hwidth : khatriRaoFixedParameterConstant d (khatriRaoSharpEmbeddingConstant d 10) ε δ *
      r * (1 + Real.log r) ^ (d - 1) ≤ m) :
    (khatriRaoSampleLaw (fun j : Fin d => rademacherVector (Fin (n j))) m).real
      {g | ¬ IsSubspaceEmbedding (khatriRaoSketch g) U ε} ≤ δ := by
  apply measureReal_not_isSubspaceEmbedding_khatriRaoSketch_rademacher_le
    hd hr hm U hU hε hδ hδ1.le
  exact (khatriRao_budget_le_fixedParameterConstant_mul_rank_log_pow hd
    (khatriRaoSharpEmbeddingConstant_pos d 10).le
    (by exact_mod_cast hr) hε hδ hδ1).trans hwidth

example {r m : ℕ} (hr : 16 ≤ r) (hm : 0 < m)
    (hwidth : (m : ℝ) ≤ khatriRaoLowerConstant 1 * r * Real.log r)
    {ε : ℝ} (hε : ε < 1) :
    1 - Real.exp (-Real.sqrt (r : ℝ)) ≤
      (khatriRaoCommonSignLaw r (khatriRaoLowerMode r 1) 1 m).real
        {z | ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
          (khatriRaoCommonIsometry r (khatriRaoLowerMode r 1) 1) ε} := by
  apply one_sub_exp_neg_sqrt_le_measureReal_not_isSubspaceEmbedding_of_le_lower_growth
    (by decide : 0 < 1) (by simpa using hr) hm _ hε
  simpa only [pow_one] using hwidth
