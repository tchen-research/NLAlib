import NLAlib.Matrix.Functions.OrderedExponential
import NLAlib.Matrix.Norms.SchattenComparison
import NLAlib.Matrix.Norms.SchattenContinuity

/-!
# Schatten boundary bounds for ordered exponential products

Both the positive and negative logarithmic parts have actual uniform bounds.
This supplies the integrability needed for the explicit interpolation kernels.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Theorems 3.1--3.2.
-/

noncomputable section

open Matrix Complex Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Uniform Schatten upper bound on the right boundary, in the original
factor order and for every imaginary time. -/
theorem schattenNormReal_orderedMatrixExp_right_le (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) {p : ℝ} (hp : 0 < p) (t : ℝ) :
    schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p ≤
      (Fintype.card n : ℝ) ^ (1 / p) * Real.exp ((H.map (fun A => ‖A‖)).sum) := by
  apply (schattenNormReal_le_card_rpow_mul_specNorm _ hp).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa only [specNorm_eq_norm] using norm_orderedMatrixExp_le_exp_sum_norm H hH
    (z := 1 + (t : ℂ) * I) (by simp)

/-- The reverse product controls the genuine lower Schatten bound. -/
theorem exp_neg_sum_norm_le_schattenNormReal_orderedMatrixExp_right [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 0 < p) (t : ℝ) :
    Real.exp (-(H.map (fun A => ‖A‖)).sum) ≤
      schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p := by
  have h := specNorm_le_schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) hp
  rw [specNorm_eq_norm] at h
  exact (exp_neg_sum_norm_le_norm_orderedMatrixExp_right H hH t).trans h

/-- The right-boundary logarithm is bounded on both sides by an explicit
finite constant. In particular, no negative logarithmic part is discarded. -/
theorem abs_log_schattenNormReal_orderedMatrixExp_right_le [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 0 < p) (t : ℝ) :
    |Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)| ≤
      (H.map (fun A => ‖A‖)).sum + |Real.log ((Fintype.card n : ℝ) ^ (1 / p))| := by
  have hl := exp_neg_sum_norm_le_schattenNormReal_orderedMatrixExp_right H hH hp t
  have hu := schattenNormReal_orderedMatrixExp_right_le H hH hp t
  have hpos : 0 < schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p :=
    (Real.exp_pos _).trans_le hl
  have hdim : 0 < (Fintype.card n : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos (by
    exact_mod_cast Fintype.card_pos) _
  have hlogl := Real.log_le_log (Real.exp_pos _) hl
  rw [Real.log_exp] at hlogl
  have hlogu := Real.log_le_log hpos hu
  rw [Real.log_mul (ne_of_gt hdim) (Real.exp_ne_zero _), Real.log_exp] at hlogu
  rw [abs_le]
  constructor
  · linarith [abs_nonneg (Real.log ((Fintype.card n : ℝ) ^ (1 / p)))]
  · linarith [le_abs_self (Real.log ((Fintype.card n : ℝ) ^ (1 / p)))]

/-- The actual right-boundary Schatten logarithm is continuous, so the
explicit normalized kernels can integrate it without a measurability premise. -/
theorem continuous_log_schattenNormReal_orderedMatrixExp_right [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 0 < p) :
    Continuous (fun t : ℝ =>
      Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)) := by
  have hc : Continuous (orderedMatrixExp H) :=
    continuous_iff_continuousAt.mpr (fun z => (analyticAt_orderedMatrixExp H z).continuousAt)
  apply ((continuous_schattenNormReal hp).comp (hc.comp (by fun_prop))).log
  intro t
  exact ne_of_gt ((Real.exp_pos _).trans_le
    (exp_neg_sum_norm_le_schattenNormReal_orderedMatrixExp_right H hH hp t))

end NLAlib
