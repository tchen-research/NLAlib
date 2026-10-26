import NLAlib.Matrix.Norms.RowMixedNorm
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurability of native mixed row norms

The finite power-sum and maximum-row formulas give measurability without
changing the matrix norm or topology instances.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NLAlib

/-- Every native real mixed row norm of exponent at least one is measurable
for the ordinary entrywise matrix measurable space, including infinity. -/
theorem measurable_rowMixedNorm {m n : Type*} [Fintype m] [Fintype n]
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    Measurable (fun A : Matrix m n ℝ => rowMixedNorm A p) := by
  have hrow (i : m) : Measurable (fun A : Matrix m n ℝ => Real.sqrt (rowSq A i)) := by
    unfold rowSq
    fun_prop
  by_cases hpt : p = ⊤
  · subst p
    simp_rw [rowMixedNorm_top]
    exact Measurable.iSup hrow
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt
    simp_rw [rowMixedNorm_eq_sum _ hpr]
    fun_prop

end NLAlib
