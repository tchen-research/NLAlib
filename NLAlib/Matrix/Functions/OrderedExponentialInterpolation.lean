import NLAlib.Matrix.Functions.SchattenInterpolation
import NLAlib.Matrix.Functions.OrderedExponentialBounds

/-! # Exact interpolation of ordered Hermitian exponential products

The actual product is entire, is unitary on the left boundary, and has
bounded continuous logarithmic Schatten norms on the right boundary. The
checked matrix Stein--Hirschman theorem therefore applies with no supplied
analytic or boundary-norm premises beyond Hermitian generators.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Theorem 3.2.
-/

noncomputable section
open Matrix Complex Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact finite-parameter interpolation estimate for an actual ordered
product of Hermitian exponentials. All finite matrix shapes are included.
This supplies the exponential-product component of multivariate ALT.
atlas: multivariate-araki-lieb-thirring (partial)
atlas: multivariate-golden-thompson (partial) -/
theorem schattenNormReal_orderedMatrixExp_le_exp_hirschman
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    schattenNormReal (orderedMatrixExp H (r : ℂ)) (p / r) ≤
      Real.exp (r * ∫ t : ℝ, Real.hirschmanDensity r t *
        Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hn : Nonempty n
  · let := hn
    have hcont : Continuous (orderedMatrixExp H) :=
      continuous_iff_continuousAt.mpr (fun z => (analyticAt_orderedMatrixExp H z).continuousAt)
    have hdiff : DiffContOnCl ℂ (orderedMatrixExp H)
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      ⟨fun z _ => (analyticAt_orderedMatrixExp H z).differentiableAt.differentiableWithinAt,
        hcont.continuousOn⟩
    have hb (z : ℂ) (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
        specNorm (orderedMatrixExp H z) ≤ Real.exp ((H.map (fun A => ‖A‖)).sum) := by
      rw [specNorm_eq_norm]
      apply norm_orderedMatrixExp_le_exp_sum_norm H hH
      exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    have hl (t : ℝ) : specNorm (orderedMatrixExp H ((t : ℂ) * I)) ≤ 1 := by
      simpa only [specNorm_eq_norm] using norm_orderedMatrixExp_imaginary_le_one H hH t
    have hright (t : ℝ) :
        schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p ≤
          Real.exp (Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)) := by
      rw [Real.exp_log ((Real.exp_pos _).trans_le
        (exp_neg_sum_norm_le_schattenNormReal_orderedMatrixExp_right H hH hp0 t))]
    have h := schattenNormReal_le_exp_hirschman_of_left_contractions hr hp hdiff hb
      (fun t => Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p))
      (continuous_log_schattenNormReal_orderedMatrixExp_right H hH hp0).measurable
      (abs_log_schattenNormReal_orderedMatrixExp_right_le H hH hp0) hl hright
    simpa only [mul_assoc, integral_const_mul] using h
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz : orderedMatrixExp H (r : ℂ) = 0 := Subsingleton.elim _ _
    rw [hz, schattenNormReal_zero (div_pos hp0 hr.1)]
    exact (Real.exp_pos _).le

end NLAlib
