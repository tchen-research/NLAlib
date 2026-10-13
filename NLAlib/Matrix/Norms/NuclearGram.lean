import NLAlib.Matrix.Norms.NuclearPSD
import NLAlib.Matrix.Norms.NuclearNorm
import NLAlib.Matrix.Spectral.GramSingularValues

/-!
# The nuclear norm through the Gram matrix

The nuclear norm depends on `A` only through its Gram matrix `AᵀA`, and for a square matrix it is
the trace of the positive polar factor: `‖A‖_* = tr √(AᵀA) = tr √(AAᵀ)`, including singular and
empty matrices. These identities feed the orthogonal Procrustes results of
`NLAlib.Matrix.Factorizations.Procrustes`.

Source: Horn–Johnson 2013, §§7.3–7.4. Atlas: helpers of `orthogonal-procrustes`.
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Equal Gram matrices on the same matrix shape have equal nuclear norms.
Horn–Johnson §7.3; supports orthogonal-procrustes. -/
theorem nuclearNorm_eq_of_gram_eq (A B : Matrix m n ℝ) (hGram : Aᵀ * A = Bᵀ * B) :
    nuclearNorm A = nuclearNorm B := by
  simp only [nuclearNorm_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  exact singularValues_eq_of_gram_eq A B
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hGram) i

/-- The trace of the positive polar factor is the nuclear norm, including
singular and empty matrices. Horn–Johnson 2013, §7.4.4. -/
theorem nuclearNorm_eq_trace_sqrt_gram (M : Matrix n n ℝ) :
    nuclearNorm M = (CFC.sqrt (Mᵀ * M)).trace := by
  let Q := CFC.sqrt (Mᵀ * M)
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hQs : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hNonneg : 0 ≤ Mᵀ * M := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hGram : Mᵀ * M = Qᵀ * Q := by
    rw [hQs]
    exact (CFC.sqrt_mul_sqrt_self _ hNonneg).symm
  rw [nuclearNorm_eq_of_gram_eq M Q hGram, nuclearNorm_eq_trace_of_posSemidef hQ]

/-- The positive row-polar factor has trace equal to the nuclear norm, so the
average used in the scaled Procrustes formula is `tr P / n` in the usual
left-polar convention. Horn–Johnson 2013, §7.4.6. -/
theorem nuclearNorm_eq_trace_sqrt_rowGram (A : Matrix n n ℝ) :
    nuclearNorm A = (CFC.sqrt (A * Aᵀ)).trace := by
  have h := nuclearNorm_eq_trace_sqrt_gram Aᵀ
  simpa only [nuclearNorm_transpose, Matrix.transpose_transpose] using h

end NLAlib
