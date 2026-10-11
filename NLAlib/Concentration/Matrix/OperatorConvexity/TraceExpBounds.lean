import NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpMonotone
import NLAlib.Concentration.Matrix.OperatorConvexity.LiebReindex

/-!
# Finite-label trace exponential bounds and scalar shifts

Exact scalar-shift identities and trace monotonicity control changes in a predictable
Hermitian offset without imposing a lower spectral bound.
-/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The existing monotonicity of the trace exponential, transported to arbitrary nonempty
finite labels. Source: Tropp 2015, Example 8.3.4; exact reindexing of `traceExp_le_traceExp`.
Atlas `matrix-freedman` (partial). -/
theorem traceExp_le_traceExp_finite [Nonempty n] (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B) : traceExp A ≤ traceExp B := by
  let e := Fintype.equivFin n
  let E := reindexStarAlgEquiv e
  have hE : LoewnerLE (E A) (E B) := by
    change (E B - E A).PosSemidef
    rw [← map_sub E]
    exact (Matrix.le_iff.mp hAB).submatrix e.symm
  have h := traceExp_le_traceExp (E A) (E B) (hA.reindex e) (hB.reindex e) hE
  change traceExp (Matrix.reindex e e A) ≤ traceExp (Matrix.reindex e e B) at h
  simpa only [traceExp_reindex] using h

/-- A real scalar identity exponentiates exactly as a scalar identity for any finite labels.
Source: scalar continuous functional calculus; helper for `matrix-freedman` (partial). -/
theorem matrixExp_smul_one_eq_exp_smul_one (t : ℝ) :
    matrixExp (t • (1 : Matrix n n ℂ)) = Real.exp t • (1 : Matrix n n ℂ) := by
  have ht : (t • (1 : Matrix n n ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp ht]
  have heq : t • (1 : Matrix n n ℂ) = algebraMap ℝ (Matrix n n ℂ) t := by
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [heq, cfc_algebraMap]
  simp only [Algebra.algebraMap_eq_smul_one]

/-- Adding a real scalar identity multiplies the trace exponential by its scalar
exponential. No Hermitian premise is needed.
Source: the commuting exponential identity; helper for `matrix-freedman` (partial). -/
theorem traceExp_add_smul_one_eq_exp_mul (A : Matrix n n ℂ) (t : ℝ) :
    traceExp (A + t • (1 : Matrix n n ℂ)) = Real.exp t * traceExp A := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hc : Commute A (t • (1 : Matrix n n ℂ)) := (Commute.one_right A).smul_right t
  have he : matrixExp (A + t • (1 : Matrix n n ℂ)) =
      matrixExp A * matrixExp (t • (1 : Matrix n n ℂ)) := NormedSpace.exp_add_of_commute hc
  unfold traceExp
  rw [he, matrixExp_smul_one_eq_exp_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]

/-- The trace exponential changes by at most the multiplicative factor `exp δ` when
Hermitian inputs differ in operator norm by at most `δ`.
Source: Loewner norm comparison and the exact scalar shift; helper for the predictable
offset passage in operator rederivations `eq:condlieb`. Atlas `matrix-freedman` (partial). -/
theorem traceExp_le_exp_mul_traceExp_of_norm_sub_le [Nonempty n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) {δ : ℝ}
    (hδ : ‖A - B‖ ≤ δ) : traceExp A ≤ Real.exp δ * traceExp B := by
  have hd : A - B ≤ algebraMap ℝ (Matrix n n ℂ) δ := by
    apply le_algebraMap_of_spectrum_le _ (hA.sub hB)
    intro x hx
    have hnorm : |x| ≤ ‖A - B‖ := by
      simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
    exact (le_abs_self x).trans (hnorm.trans hδ)
  have hle : A ≤ B + δ • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, add_comm] using sub_le_iff_le_add.mp hd
  have hh : (B + δ • (1 : Matrix n n ℂ)).IsHermitian :=
    hB.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  exact (traceExp_le_traceExp_finite A _ hA hh hle).trans_eq
    (traceExp_add_smul_one_eq_exp_mul B δ)

end NLAlib
