import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Spectral.Weyl

/-!
# Continuity of finite Schatten norms

Every singular value is spectral-norm Lipschitz. Finite positive-exponent
power sums and roots are therefore continuous over real or complex scalars.
-/

noncomputable section
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every singular value is one-Lipschitz for the spectral matrix norm. -/
theorem lipschitzWith_singularValues (i : ℕ) :
    LipschitzWith 1 (fun A : Matrix m n 𝕜 => singularValues A i) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq,dist_eq_norm,one_mul,NNReal.coe_one,specNorm_eq_norm,Real.norm_eq_abs] using
    abs_singularValues_sub_le_specNorm A B i

open scoped Matrix.Norms.L2Operator in
/-- Positive-exponent Schatten power sums and their positive roots are continuous. -/
theorem continuous_schattenNormReal {p : ℝ} (hp : 0 < p) :
    Continuous (fun A : Matrix m n 𝕜 => schattenNormReal A p) := by
  unfold schattenNormReal
  apply Continuous.rpow_const
  · apply continuous_finset_sum
    intro i hi
    exact (lipschitzWith_singularValues i).continuous.rpow_const (fun _ => Or.inr hp.le)
  · intro A
    exact Or.inr (one_div_nonneg.mpr hp.le)

end NLAlib
