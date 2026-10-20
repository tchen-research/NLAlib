import NLAlib.Probability.Free.WordMatrixDegreeMoments
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Genuine degree bounds for real polynomial compositions

A real polynomial of degree at most `r`, evaluated at an actual amplified
word operator of degree at most `k`, has actual entry degree at most `r*k`.
The proof uses the native polynomial evaluation formula and the already
proved degree formula for genuine matrix powers. This supplies the degree
bridge for Jackson approximation of self-adjoint resolvents.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

/-- Native real polynomial evaluation multiplies the actual entry degree
by at most its polynomial degree. Constants and empty dimensions are included. -/
theorem aeval_entries_mem_wordWickDegreeSpan {k r : ℕ} {T : M}
    (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k)
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ r) :
    ∀ i j, (Polynomial.aeval T Q) i j ∈ wordWickDegreeSpan (ι := ι) (r * k) := by
  intro i j
  let E : M →ₗ[ℝ] B :=
    { toFun S := S i j
      map_add' S U := CStarMatrix.add_apply S U i j
      map_smul' c S := CStarMatrix.smul_apply c S i j }
  rw [Polynomial.aeval_eq_sum_range]
  change E (∑ n ∈ Finset.range (Q.natDegree + 1), Q.coeff n • T ^ n) ∈ _
  rw [map_sum]
  simp only [map_smul]
  apply Submodule.sum_mem
  intro n hn
  change Q.coeff n • (T ^ n) i j ∈ wordWickDegreeSpan (ι := ι) (r * k)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  apply Submodule.smul_mem
  apply wordWickDegreeSpan_mono _ (pow_entries_mem_wordWickDegreeSpan hT n i j)
  exact Nat.mul_le_mul_right k ((Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hQ)

end NLAlib

end
