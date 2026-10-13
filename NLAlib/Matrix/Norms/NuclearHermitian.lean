import NLAlib.Matrix.Norms.NuclearPSD
import NLAlib.Matrix.Inequalities.Lidskii
import NLAlib.Matrix.Functions.CFCTrace
import NLAlib.Matrix.Inequalities.MajorizationHLP
import NLAlib.Matrix.Spectral.GramSingularValues
/-!
# Nuclear norm and Hermitian spectral variation

Absolute functional calculus is positive semidefinite and has the same Gram
matrix as the original Hermitian matrix. This identifies its singular values
and proves that the nuclear norm is the sum of absolute eigenvalues.
Full Lidskii plus the convex absolute-value test gives the advertised nuclear
variation bound, with constant one and no simple-spectrum assumption.
Source: Bhatia (1997), Theorem III.4.1; Marshall–Olkin–Arnold (2011), 9.G.
Atlas: `lidskii`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- The Gram matrix of an orthogonally diagonalized real matrix is obtained by
squaring the diagonal coefficients. -/
theorem gram_orthogonal_diagonalization {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : HasOrthonormalCols P) (d : n → ℝ) :
    (P * Matrix.diagonal d * Pᵀ)ᵀ * (P * Matrix.diagonal d * Pᵀ) =
      P * Matrix.diagonal (fun i => d i ^ 2) * Pᵀ := by
  calc
    _ = P * Matrix.diagonal d * (Pᵀ * P) * Matrix.diagonal d * Pᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
    _ = P * (Matrix.diagonal d * Matrix.diagonal d) * Pᵀ := by
      rw [hP, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.diagonal_mul_diagonal]
      simp only [pow_two]

/-- The absolute functional calculus has the same actual Gram matrix as a real
Hermitian matrix, including zero and repeated eigenvalues. -/
theorem gram_cfc_abs_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (cfc (abs : ℝ → ℝ) A)ᴴ * cfc (abs : ℝ → ℝ) A = Aᴴ * A := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hP := transpose_eigenvectorUnitary_mul_self hA
  rw [hA.cfc_eq, cfc_eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA (abs : ℝ → ℝ),
    gram_orthogonal_diagonalization hP]
  conv_rhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
  rw [gram_orthogonal_diagonalization hP]
  simp only [sq_abs]

/-- Absolute functional calculus preserves every native singular value of a
real Hermitian matrix. -/
theorem singularValues_cfc_abs {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    singularValues (cfc (abs : ℝ → ℝ) A) k = singularValues A k :=
  singularValues_eq_of_gram_eq _ _ (gram_cfc_abs_eq hA) k

/-- The nuclear norm of a real Hermitian matrix is the sum of the absolute
values of its full decreasing eigenvalue list. Empty dimensions are included. -/
theorem nuclearNorm_eq_sum_abs_eigenvalues₀ {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    nuclearNorm A = ∑ i : Fin (Fintype.card n), |hA.eigenvalues₀ i| := by
  have hAbs : (cfc (abs : ℝ → ℝ) A).PosSemidef :=
    posSemidef_cfc_of_nonneg_eigenvalues hA (fun i => abs_nonneg _)
  calc
    nuclearNorm A = nuclearNorm (cfc (abs : ℝ → ℝ) A) := by
      unfold nuclearNorm kyFanNorm
      simp only [← singularValues_eq_linearMap]
      simp_rw [singularValues_cfc_abs hA]
    _ = (cfc (abs : ℝ → ℝ) A).trace := nuclearNorm_eq_trace_of_posSemidef hAbs
    _ = ∑ i : Fin (Fintype.card n), |hA.eigenvalues₀ i| := by
      rw [trace_cfc_eq_sum_eigenvalues hA (abs : ℝ → ℝ)]
      exact sum_eigenvalues_eq_sum_sorted hA (abs : ℝ → ℝ)

/-- Full Hermitian spectral variation in nuclear norm, with constant one.
Lidskii ordinary majorization and the genuine convex absolute-value test imply
this for arbitrary finite dimensions and all repeated/zero/signed spectra.
Bhatia (1997), Theorem III.4.1.
atlas: lidskii (partial) -/
theorem sum_abs_eigenvalues₀_add_sub_le_nuclearNorm {n : Type*} [Fintype n] [DecidableEq n]
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian) :
    (∑ i : Fin (Fintype.card n), |(hA.add hE).eigenvalues₀ i - hA.eigenvalues₀ i|) ≤ nuclearNorm E := by
  have hconv : ConvexOn ℝ Set.univ ((abs : ℝ → ℝ) : ℝ → ℝ) := by
    convert! (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set ℝ))) using 1
  have h := (majorized_eigenvalues₀_add_sub hA hE).sum_convex_le hconv
  rw [nuclearNorm_eq_sum_abs_eigenvalues₀ hE]
  exact h

end NLAlib
