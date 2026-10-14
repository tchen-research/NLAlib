import NLAlib.Sketching.Structured.KhatriRaoUpper
import NLAlib.Probability.Rademacher.DirectionalExpSquare
import NLAlib.Probability.Rademacher.RademacherSymmetry

/-!
# Sharp Khatri–Rao embeddings from independent signs

The abstract factor-law upper theorem specializes to actual independent-coordinate Rademacher
vectors with no remaining isotropy or directional-moment assumptions. Together with the explicit
bounded-entry witnesses in `KhatriRaoLowerGrowth`, this gives matching rank orders within one
concrete factor law.

Source: Heidary, *The Sharp Logarithmic Cost of Khatri–Rao Subspace Embeddings*,
Theorem 2.1 and Proposition `lower:prop:rademacher`.
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

/-- Independent-coordinate Rademacher factors satisfy the sharp embedding upper budget with
the fixed admissible square-exponential parameter `10`. There are no distributional hypotheses
left for the caller to prove. The numerical constant is deliberately unoptimized.
Source: Heidary, Theorem 2.1, specialized to the law in Proposition `lower:prop:rademacher`.
atlas: khatri-rao-sharp-growth (partial) -/
theorem measureReal_not_isSubspaceEmbedding_khatriRaoSketch_rademacher_le
    {d r m : ℕ} {n : Fin d → ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : khatriRaoSharpEmbeddingConstant d 10 *
      ((r : ℝ) * Real.log (4 * r / δ) / ε ^ 2 +
        ((r : ℝ) * Real.log (4 * r / δ) ^ (d - 1) +
          Real.log (4 * r / δ) ^ d) / ε) ≤ m) :
    (khatriRaoSampleLaw (fun j : Fin d => rademacherVector (Fin (n j))) m).real
      {g | ¬ IsSubspaceEmbedding (khatriRaoSketch g) U ε} ≤ δ := by
  apply measureReal_not_isSubspaceEmbedding_khatriRaoSketch_le hd hr hm
    (fun j : Fin d => rademacherVector (Fin (n j))) (by norm_num : (0 : ℝ) < 10)
    _ _ U hU hε hδ hδ1 hbudget
  · intro j u hu
    simpa only [div_pow] using lintegral_exp_sq_dotProduct_rademacherVector_le_two u hu
  · intro j a b
    exact integral_coordinate_mul_coordinate_rademacherVector a b

end NLAlib
