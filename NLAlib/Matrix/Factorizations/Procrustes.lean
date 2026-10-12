import NLAlib.Matrix.Factorizations.PolarDecomposition
import NLAlib.Matrix.Norms.NuclearPSD
import NLAlib.Matrix.Spectral.GramSingularValues
/-!
# Orthogonal Procrustes and trace equality

Square polar factors attain the nuclear pairing, so they solve one-sided
Procrustes even at deficient rank. Equality of trace and nuclear norm forces
positive semidefiniteness. Horn–Johnson 2013, §§7.4.4–7.4.6.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Equal Gram matrices on the same matrix shape have equal nuclear norms.
Horn–Johnson §7.3; supports orthogonal-procrustes. -/
theorem nuclearNorm_eq_of_gram_eq (A B : Matrix m n ℝ) (hGram : Aᵀ * A = Bᵀ * B) :
    nuclearNorm A = nuclearNorm B := by
  unfold nuclearNorm kyFanNorm
  apply Finset.sum_congr rfl
  intro i _
  exact toEuclideanLin_singularValues_eq_of_gram_eq A B
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

/-- Every orthogonal square polar factor attains the nuclear dual pairing,
including arbitrary rank and empty spaces. Horn–Johnson 2013, §7.4.4.
atlas: orthogonal-procrustes (partial) -/
theorem frobInner_eq_nuclearNorm_of_polar {M U : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (hM : U * CFC.sqrt (Mᵀ * M) = M) :
    frobInner M U = nuclearNorm M := by
  let Q := CFC.sqrt (Mᵀ * M)
  have hQs : Qᵀ = Q := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (Mᵀ * M)).star_eq
  have hMQ : U * Q = M := hM
  have hPair : frobInner M U = Q.trace := by
    rw [frobInner_eq_trace]
    nth_rw 1 [← hMQ]
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hU, Matrix.mul_one, hQs]
  exact hPair.trans (nuclearNorm_eq_trace_sqrt_gram M).symm

omit [DecidableEq m] [DecidableEq n] in
/-- Moving a one-sided rotation from the Frobenius pairing produces the
square cross-product pairing. Horn–Johnson 2013, §7.4.4. -/
theorem frobInner_mul_eq_frobInner_mul_transpose (A B : Matrix m n ℝ) (U : Matrix m m ℝ) :
    frobInner A (U * B) = frobInner (A * Bᵀ) U := by
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.trace_mul_cycle']
  rw [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The exact Procrustes error at any orthogonal polar factor of `A Bᵀ`.
Horn–Johnson 2013, §7.4.4; includes zero rank and empty dimensions.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_sub_mul_eq_of_cross_polar (A B : Matrix m n ℝ) (U : Matrix m m ℝ)
    (hU : HasOrthonormalCols U)
    (hPolar : U * CFC.sqrt ((A * Bᵀ)ᵀ * (A * Bᵀ)) = A * Bᵀ) :
    frobSq (A - U * B) = frobSq A + frobSq B - 2 * nuclearNorm (A * Bᵀ) := by
  rw [frobSq_sub, frobSq_mul_left_of_orthonormal hU,
    frobInner_mul_eq_frobInner_mul_transpose, frobInner_eq_nuclearNorm_of_polar hU hPolar]
  ring

omit [DecidableEq n] in
/-- The one-sided Procrustes lower bound for every orthogonal competitor.
Horn–Johnson 2013, §7.4.4.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_add_frobSq_sub_two_nuclearNorm_le_sub_mul
    (A B : Matrix m n ℝ) (U : Matrix m m ℝ) (hU : HasOrthonormalCols U) :
    frobSq A + frobSq B - 2 * nuclearNorm (A * Bᵀ) ≤ frobSq (A - U * B) := by
  have h := frobInner_le_nuclearNorm_of_specNorm_le_one (A * Bᵀ) U
    (specNorm_le_one_of_orthonormal hU)
  rw [frobSq_sub, frobSq_mul_left_of_orthonormal hU, frobInner_mul_eq_frobInner_mul_transpose]
  linarith

omit [DecidableEq n] in
/-- One-sided Procrustes has the advertised minimum, attained by a genuine
orthogonal polar factor of the cross-product. Horn–Johnson 2013, §7.4.4.
atlas: orthogonal-procrustes (partial) -/
theorem isLeast_frobSq_sub_orthogonal_mul (A B : Matrix m n ℝ) :
    IsLeast {z : ℝ | ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧ frobSq (A - U * B) = z}
      (frobSq A + frobSq B - 2 * nuclearNorm (A * Bᵀ)) := by
  obtain ⟨U, hU, hPolar⟩ := exists_isometry_mul_sqrt_gram_eq (A * Bᵀ) le_rfl
  refine ⟨⟨U, hU, frobSq_sub_mul_eq_of_cross_polar A B U hU hPolar⟩, ?_⟩
  rintro z ⟨V, hV, rfl⟩
  exact frobSq_add_frobSq_sub_two_nuclearNorm_le_sub_mul A B V hV

/-- Trace equals nuclear norm exactly for positive semidefinite real square
matrices, including singular and empty inputs. Horn–Johnson 2013, Cor. 7.4.1.5;
the proof uses the positive polar factor and a squared Frobenius distance.
atlas: orthogonal-procrustes (partial) -/
theorem trace_eq_nuclearNorm_iff_posSemidef (M : Matrix n n ℝ) :
    M.trace = nuclearNorm M ↔ M.PosSemidef := by
  constructor
  · intro hTrace
    obtain ⟨U, hU, hM⟩ := exists_isometry_mul_sqrt_gram_eq M le_rfl
    let Q := CFC.sqrt (Mᵀ * M)
    let H := CFC.sqrt Q
    have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
    have hHs : Hᵀ = H := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (CFC.sqrt_nonneg Q).star_eq
    have hHH : H * H = Q := CFC.sqrt_mul_sqrt_self _ hQ.nonneg
    have hMQ : U * Q = M := hM
    have hNorm : frobSq H = Q.trace := by
      rw [frobSq, frobInner_eq_trace, hHs, hHH]
    have hPair : frobInner H (U * H) = M.trace := by
      rw [frobInner_eq_trace, hHs, ← Matrix.mul_assoc,
        Matrix.trace_mul_cycle, hHH, Matrix.trace_mul_comm, hMQ]
    have hFrob : frobSq (H - U * H) = 0 := by
      rw [frobSq_sub, frobSq_mul_left_of_orthonormal hU, hNorm, hPair,
        hTrace, nuclearNorm_eq_trace_sqrt_gram]
      change Q.trace - 2 * Q.trace + Q.trace = 0
      ring
    have hHU : H = U * H := sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hFrob)
    have hEqual : M = Q := by
      rw [← hMQ, ← hHH, ← Matrix.mul_assoc, ← hHU]
    rwa [hEqual]
  · intro hM
    exact (nuclearNorm_eq_trace_of_posSemidef hM).symm

end NLAlib
