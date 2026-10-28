import NLAlib.Probability.Gaussian.Basic.CircularComplex

/-!
# Conjugation invariance of the native complex Gaussian product law

Conjugation leaves the real coordinates fixed and negates the independent
imaginary Gaussian coordinates. The proof preserves their complete joint law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- Entrywise conjugation preserves the actual circular complex Gaussian
vector product law, including independence of its coordinates. -/
theorem hasLaw_star_circularComplexGaussianVector {n : Type*} [Fintype n] :
    HasLaw (fun z : n → ℂ => star z) (circularComplexGaussianVector n)
      (circularComplexGaussianVector n) := by
  let T : n ⊕ n → ℝ → ℝ := fun i => Sum.elim (fun _ => id) (fun _ => Neg.neg) i
  have hp (i : n ⊕ n) : MeasurePreserving (T i) (gaussianReal 0 1) (gaussianReal 0 1) := by
    cases i with
    | inl i => exact MeasurePreserving.id _
    | inr i =>
      refine ⟨measurable_neg, ?_⟩
      change (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1
      simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hT := measurePreserving_pi (fun _ : n ⊕ n => gaussianReal 0 1)
    (fun _ : n ⊕ n => gaussianReal 0 1) hp
  have h := hasLaw_complexifyVector_gaussianVector.comp
    (hT.hasLaw.comp hasLaw_realifyVector_circularComplexGaussianVector)
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  funext i
  apply Complex.ext <;> simp [T, complexifyVector, realifyVector]

end NLAlib
