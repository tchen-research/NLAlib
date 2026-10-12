import NLAlib.Matrix.MinkowskiDeterminant
import NLAlib.Matrix.TraceInverseConvexity

/-!
# Complete determinant and inverse-trace convexity

Strict log-determinant concavity, determinant-root concavity and Minkowski's
inequality, and strict inverse-trace convexity, all with exact equality.
Source: Horn--Johnson (2013), Theorem 7.6.6, Corollary 7.6.8,
Theorems 7.6.10 and 7.8.21; atlas `log-det-concavity`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complete determinant-convexity contract with all equality cases.
Log determinant and inverse trace are respectively strictly concave and
strictly convex on the entire PD cone. Only determinant roots require
positive dimension; equality there is exactly positive proportionality.
Horn--Johnson (2013), Theorem 7.6.6, Corollary 7.6.8, and Theorems 7.6.10
and 7.8.21. The positive-dimension requirement repairs the original
dimension-free determinant-root wording.
atlas: log-det-concavity -/
theorem determinant_concavity_and_inverse_trace_convexity
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    StrictConcaveOn ℝ {M : Matrix n n ℝ | M.PosDef} (fun M => Real.log M.det) ∧
    StrictConvexOn ℝ {M : Matrix n n ℝ | M.PosDef} (fun M => M⁻¹.trace) ∧
    (A.det ^ a * B.det ^ b ≤ (a • A + b • B).det) ∧
    ((a • A + b • B).det = A.det ^ a * B.det ^ b ↔ A = B) ∧
    ((a • A + b • B)⁻¹.trace ≤ a * A⁻¹.trace + b * B⁻¹.trace) ∧
    ((a • A + b • B)⁻¹.trace = a * A⁻¹.trace + b * B⁻¹.trace ↔ A = B) ∧
    (0 < Fintype.card n →
      ConcaveOn ℝ {M : Matrix n n ℝ | M.PosDef}
        (fun M => M.det ^ (1 / (Fintype.card n : ℝ))) ∧
      (A.det ^ (1 / (Fintype.card n : ℝ)) + B.det ^ (1 / (Fintype.card n : ℝ)) ≤
        (A + B).det ^ (1 / (Fintype.card n : ℝ))) ∧
      ((A + B).det ^ (1 / (Fintype.card n : ℝ)) =
        A.det ^ (1 / (Fintype.card n : ℝ)) + B.det ^ (1 / (Fintype.card n : ℝ)) ↔
        ∃ c : ℝ, 0 < c ∧ A = c • B) ∧
      ((a • A + b • B).det ^ (1 / (Fintype.card n : ℝ)) =
        a * A.det ^ (1 / (Fintype.card n : ℝ)) + b * B.det ^ (1 / (Fintype.card n : ℝ)) ↔
        ∃ c : ℝ, 0 < c ∧ A = c • B)) := by
  have hdet := det_smul_add_ge_rpow_mul_and_eq_iff hA hB ha hb hab
  refine ⟨strictConcaveOn_log_det, strictConvexOn_trace_inv, hdet.1, hdet.2,
    trace_inv_smul_add_le hA hB ha.le hb.le hab,
    trace_inv_smul_add_eq_iff hA hB ha hb hab, fun hN => ?_⟩
  have hm := det_add_rpow_inv_card_ge_and_eq_iff hA hB hN
  exact ⟨concaveOn_det_rpow_inv_card hN, hm.1, hm.2,
    det_smul_add_rpow_inv_card_eq_iff hA hB hN ha hb⟩

end NLAlib
