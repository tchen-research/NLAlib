import NLAlib.Matrix.Functions.HermitianCalculus
import NLAlib.Matrix.Spectral.Complexification

/-!
# Spectral detection of lower Loewner-bound failure

A lower bound by a scalar identity fails only when the largest eigenvalue of
the identity defect exceeds the corresponding scalar. Real matrices are
transported through the order-reflecting complexification.
-/

noncomputable section
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Failure of the lower Loewner bound is detected by a strict largest
eigenvalue deviation of the identity defect. No positivity assumption or
restriction on the real threshold is necessary. -/
theorem lt_lambdaMax_one_sub_of_not_smul_one_le
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hfail : ¬ (1 - ε) • (1 : Matrix n n ℂ) ≤ A) :
    ε < lambdaMax (1 - A) := by
  by_contra hnot
  have hdef : 1 - A ≤ ε • (1 : Matrix n n ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact le_algebraMap_of_spectrum_le
      (le_of_mem_spectrum_of_lambdaMax_le _ (Matrix.isHermitian_one.sub hA)
        (le_of_not_gt hnot))
  apply hfail
  rw [sub_smul, one_smul]
  apply (sub_le_iff_le_add).mpr
  have h := add_le_add_right hdef A
  have he : A + (1 - A) = (1 : Matrix n n ℂ) := by abel
  rwa [he] at h

open scoped Matrix.Norms.L2Operator in
/-- Failure of a real symmetric lower Loewner bound is detected by the
largest eigenvalue of its complexified identity defect. This is the event
bridge used for relative sample-covariance lower bounds. -/
theorem lt_lambdaMax_complexification_one_sub_of_not_smul_one_le
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {ε : ℝ}
    (hfail : ¬ (1 - ε) • (1 : Matrix n n ℝ) ≤ A) :
    ε < lambdaMax (realMatrixComplexification (1 - A) : Matrix n n ℂ) := by
  have hAc : (realMatrixComplexification A : Matrix n n ℂ).IsHermitian :=
    hA.map (algebraMap ℝ ℂ) (fun x => by simp)
  have hfailc : ¬ (1 - ε) • (1 : Matrix n n ℂ) ≤ realMatrixComplexification A := by
    intro h
    apply hfail
    apply (realMatrixComplexification_le_iff (𝕜 := ℂ) _ _).mp
    simpa only [map_smul, map_one] using h
  simpa only [map_sub, map_one] using
    lt_lambdaMax_one_sub_of_not_smul_one_le hAc hfailc

open scoped Matrix.Norms.L2Operator in
/-- A fixed lower Loewner bound defines a closed set of real matrices.
The order reflection by complexification gives this fact without requiring
a separate real-matrix closed-order instance. -/
theorem isClosed_setOf_le_realMatrix (A : Matrix n n ℝ) :
    IsClosed {B : Matrix n n ℝ | A ≤ B} := by
  have hc : IsClosed {B : Matrix n n ℂ |
      (realMatrixComplexification A : Matrix n n ℂ) ≤ B} :=
    isClosed_le continuous_const continuous_id
  have hp := hc.preimage (continuous_realMatrixComplexification (𝕜 := ℂ) (n := n))
  simpa only [Set.preimage_ofPred_eq, realMatrixComplexification_le_iff] using hp

end NLAlib
