import NLAlib.Matrix.Perturbation.PseudoinverseSpectralPerturbation
import NLAlib.Matrix.Perturbation.PseudoinverseFrobeniusPerturbation
import NLAlib.Matrix.Perturbation.PseudoinverseNormControl
/-!
# Complete Moore–Penrose perturbation toolkit

The exact difference identity, general-rank golden-ratio bound, equal-rank
golden-ratio and square-root-two bounds, sharp minimum range-projector
coefficients, and small-perturbation reciprocal denominator.
Sources: Wedin (1973), Stewart–Sun §III.3.
Atlas: `pseudoinverse-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Every advertised Moore–Penrose perturbation assertion, with the exact
golden ratio and `sqrt(2)` constants. Wedin (1973), Stewart–Sun §III.3; the proof
uses the orthogonal block argument in the supplied operator derivations.
Rank equality is imposed only on the branches that require it. All ranks and
arbitrary finite row/column types, including empty ones, are covered.
atlas: pseudoinverse-perturbation -/
theorem pseudoinverse_perturbation_bounds (A B : Matrix m n ℝ) :
    (moorePenroseInverse B-moorePenroseInverse A =
      -moorePenroseInverse B*(B-A)*moorePenroseInverse A +
      moorePenroseInverse B*(moorePenroseInverse B)ᵀ*(B-A)ᵀ*(1-A*moorePenroseInverse A) +
      (1-moorePenroseInverse B*B)*(B-A)ᵀ*(moorePenroseInverse A)ᵀ*moorePenroseInverse A) ∧
    (specNorm (moorePenroseInverse B-moorePenroseInverse A) ≤
      Real.goldenRatio*max (specNorm (moorePenroseInverse A)^2)
        (specNorm (moorePenroseInverse B)^2)*specNorm (B-A)) ∧
    (A.rank=B.rank →
      (specNorm (moorePenroseInverse B-moorePenroseInverse A) ≤
        Real.goldenRatio*specNorm (moorePenroseInverse A)*specNorm (moorePenroseInverse B)*specNorm (B-A)) ∧
      (frobNorm (moorePenroseInverse B-moorePenroseInverse A) ≤
        Real.sqrt 2*specNorm (moorePenroseInverse A)*specNorm (moorePenroseInverse B)*frobNorm (B-A)) ∧
      (specNorm (A*moorePenroseInverse A-B*moorePenroseInverse B) ≤
        min (specNorm (moorePenroseInverse A)) (specNorm (moorePenroseInverse B))*specNorm (B-A)) ∧
      (specNorm (moorePenroseInverse A*A-moorePenroseInverse B*B) ≤
        min (specNorm (moorePenroseInverse A)) (specNorm (moorePenroseInverse B))*specNorm (B-A)) ∧
      (specNorm (moorePenroseInverse A)*specNorm (B-A) < 1 →
        specNorm (moorePenroseInverse B) ≤ specNorm (moorePenroseInverse A)/
          (1-specNorm (moorePenroseInverse A)*specNorm (B-A)))) := by
  refine ⟨moorePenroseInverse_sub_eq A B,
    specNorm_moorePenroseInverse_sub_le_goldenRatio_max_sq A B, ?_⟩
  intro hr
  exact ⟨specNorm_moorePenroseInverse_sub_le_goldenRatio_mul_of_rank_eq hr,
    frobNorm_moorePenroseInverse_sub_le_sqrt_two_mul_of_rank_eq hr,
    specNorm_sub_columnProjector_le_min_pinv_mul_specNorm hr,
    specNorm_sub_rowProjector_le_min_pinv_mul_specNorm hr,
    fun hsmall => specNorm_moorePenroseInverse_le_div_of_rank_eq hr hsmall⟩

end NLAlib
