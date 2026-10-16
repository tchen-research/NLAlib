import NLAlib.Probability.Gaussian.Moments.SeriesHermiteAction
import NLAlib.Matrix.Norms.Frobenius

/-! # Exact finite Hermite vacuum identity for Gaussian matrix moments

Starting from the constant polynomial, the first `p` multiplications never
leave the total-degree cutoff `p`. The finite coefficient isometry therefore
identifies the actual Gaussian even trace moment with the squared Frobenius
norm of a finite matrix applied to its vacuum embedding.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d] {p : ℕ}

/-- Embed ordinary matrix coordinates at vacuum occupation. This is the
literal constant-polynomial coefficient matrix. -/
def hermiteVacuumEmbedding (d : Type*) [Fintype d] [DecidableEq d] (ι : Type*)
    [Fintype ι] [DecidableEq ι] (p : ℕ) : Matrix (d × HermiteIndex ι p) d ℂ :=
  fun a b => if a.2 = HermiteIndex.vacuum then (1 : Matrix d d ℂ) a.1 b else 0

/-- Vacuum coordinates are the constant matrix identity under actual Hermite
polynomial evaluation. -/
theorem matrixHermiteExpansion_vacuum (x : ι → ℝ) :
    matrixHermiteExpansion (hermiteVacuumEmbedding d ι p) x = (1 : Matrix d d ℂ) := by
  ext a b
  simp [matrixHermiteExpansion, hermiteExpansion, hermiteVacuumEmbedding,
    ite_mul, productHermite]

/-- The vacuum coefficient matrix has degree support zero. -/
theorem hermiteVacuumEmbedding_support (a : d) (α : HermiteIndex ι p) (b : d)
    (hα : 0 < α.degree) : hermiteVacuumEmbedding d ι p (a, α) b = 0 := by
  have hn : α ≠ HermiteIndex.vacuum := by
    intro he
    rw [he, HermiteIndex.degree_vacuum] at hα
    exact (lt_irrefl 0 hα)
  simp [hermiteVacuumEmbedding, hn]

/-- Each actual finite Hermite multiplication raises vacuum degree support
by at most one, for every integer power. -/
theorem hermiteSeriesOperator_pow_vacuum_support
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (k : ℕ)
    (a : d) (α : HermiteIndex ι p) (b : d) (hα : k < α.degree) :
    (hermiteSeriesOperator A p ^ k * hermiteVacuumEmbedding d ι p) (a, α) b = 0 := by
  induction k generalizing a α b with
  | zero => simpa only [pow_zero, Matrix.one_mul] using hermiteVacuumEmbedding_support a α b hα
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc]
    apply hermiteSeriesOperator_mul_support A hA _ k
    · intro a' α' b' hα'
      exact ih a' α' b' hα'
    · exact hα

/-- The first `p` powers of the actual finite Hermite matrix exactly represent
the corresponding powers of the Gaussian matrix series polynomial. -/
theorem matrixHermiteExpansion_pow_vacuum
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (k : ℕ) (hk : k ≤ p)
    (x : ι → ℝ) :
    matrixHermiteExpansion (hermiteSeriesOperator A p ^ k * hermiteVacuumEmbedding d ι p) x =
      (∑ i, x i • A i) ^ k := by
  induction k with
  | zero => simp only [pow_zero, Matrix.one_mul, matrixHermiteExpansion_vacuum]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, matrixHermiteExpansion_operator_mul A hA]
    · rw [ih (by omega), pow_succ']
    · intro a α b hα
      apply hermiteSeriesOperator_pow_vacuum_support A hA k a α b
      have ha := α.property
      change α.degree ≤ p at ha
      omega

/-- The squared Frobenius norm of a vacuum embedding is the ordinary matrix
dimension, with unnormalized trace conventions. -/
theorem frobSq_hermiteVacuumEmbedding :
    frobSq (hermiteVacuumEmbedding d ι p) = Fintype.card d := by
  rw [frobSq_eq_sum_norm_sq, Fintype.sum_prod_type]
  simp [hermiteVacuumEmbedding, ite_mul, Matrix.one_apply,
    apply_ite, eq_comm]

/-- Matrix-valued finite Hermite expansion preserves the actual Gaussian
integral of the unnormalized squared Frobenius norm. -/
theorem integral_frobSq_matrixHermiteExpansion {c : Type*} [Fintype c]
    (Z : Matrix (d × HermiteIndex ι p) c ℂ) :
    (∫ x, frobSq (matrixHermiteExpansion Z x) ∂gaussianVector ι) = frobSq Z := by
  simp only [frobSq_eq_sum_norm_sq, matrixHermiteExpansion]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    integrable_norm_sq_hermiteExpansion (fun α => Z (a, α) b)))]
  simp_rw [integral_finsetSum _ (fun b _ => integrable_norm_sq_hermiteExpansion _),
    integral_norm_sq_hermiteExpansion]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

/-- The finite vacuum identity exactly realizes the actual Gaussian even
trace moment, using cutoff `p` rather than an infinite Fock space.
Source: Bandeira et al. (2026), Theorem 2.1, finite Hermite route.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem integral_re_trace_gaussianSeries_even_pow_eq_frobSq_hermiteVacuum
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    (∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) =
      frobSq (hermiteSeriesOperator A p ^ p * hermiteVacuumEmbedding d ι p) := by
  rw [← integral_frobSq_matrixHermiteExpansion]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [matrixHermiteExpansion_pow_vacuum A hA p le_rfl,
    frobSq_eq_re_trace_conjTranspose_mul_self]
  have hX : (∑ i, x i • A i).IsHermitian := by
    apply isSelfAdjoint_sum
    intro i _
    exact (hA i).smul (isSelfAdjoint_iff.mpr (by simp))
  change ((∑ i, x i • A i) ^ (2 * p)).trace.re =
    (((∑ i, x i • A i) ^ p)ᴴ * (∑ i, x i • A i) ^ p).trace.re
  rw [(hX.pow p).eq, ← pow_add, show p + p = 2 * p by omega]

end NLAlib
