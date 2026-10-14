import NLAlib.Krylov.Quadrature.Jacobi
import NLAlib.Matrix.Norms.DeflatedTraceBounds

/-! # Bounds on Lanczos recurrence coefficients

Every diagonal coefficient is a unit-vector Rayleigh value. Orthonormal
compression bounds every signed off-diagonal by the ambient spectral norm;
the canonical positive orientation turns this into a positive coefficient bound.
Source: Gautschi (2004), Theorem 1.28; operator derivations OP12–OP14.
-/

noncomputable section

open Matrix Set
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- Every Lanczos diagonal lies in every interval containing the ambient
Hermitian spectrum. Source: Gautschi (2004), Theorem 1.28.
atlas: recurrence-coefficient-bounds (partial) -/
theorem alpha_mem_Icc_of_eigenvalues (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {a c : ℝ} (hs : ∀ i, hA.eigenvalues i ∈ Icc a c) {j : ℕ} (hj : j < q) :
    D.alpha j ∈ Icc a c := by
  let i : Fin q := ⟨j, hj⟩
  have hlo := mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues hA (fun k => (hs k).1) (D.Q.col i)
  have hhi := dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues hA (fun k => (hs k).2) (D.Q.col i)
  rw [D.hasOrthonormalCols.col_dotProduct_col, if_pos rfl, mul_one] at hlo hhi
  have heq : D.alpha j = D.Q.col i ⬝ᵥ (A *ᵥ D.Q.col i) := by
    rw [alpha, dif_pos hj]
    change (D.Qᵀ * A * D.Q) i i = _
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    rfl
  rw [heq]
  exact ⟨hlo, hhi⟩

/-- Every Lanczos diagonal lies between the smallest and largest ambient
Hermitian eigenvalues. The existence of its column supplies nonempty dimension.
Source: Gautschi (2004), Theorem 1.28.
atlas: recurrence-coefficient-bounds (partial) -/
theorem alpha_mem_Icc_lambdaMin_lambdaMax (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {j : ℕ} (hj : j < q) : D.alpha j ∈ Icc (lambdaMin A) (lambdaMax A) := by
  apply D.alpha_mem_Icc_of_eigenvalues hA _ hj
  intro i
  rw [lambdaMin, lambdaMax, hA.spectrum_real_eq_range_eigenvalues]
  have hf : (Set.range hA.eigenvalues).Finite := Set.finite_range _
  exact ⟨csInf_le hf.bddBelow ⟨i, rfl⟩, le_csSup hf.bddAbove ⟨i, rfl⟩⟩

/-- Every signed Lanczos off-diagonal has magnitude at most the ambient spectral
norm. It applies to arbitrary basis signs and to the zero boundary coefficients.
Source: Gautschi (2004), Theorem 1.28.
atlas: recurrence-coefficient-bounds (partial) -/
theorem abs_beta_le_specNorm (D : LanczosDecomp A b q) (j : ℕ) : |D.beta j| ≤ specNorm A := by
  have hT : specNorm D.T ≤ specNorm A := by
    change specNorm (D.Qᵀ * A * D.Q) ≤ specNorm A
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      specNorm_conjTranspose_mul_mul_le_of_hasOrthonormalCols D.hasOrthonormalCols A
  rw [beta]
  split_ifs with hj
  · exact (abs_apply_le_specNorm D.T _ _).trans hT
  · simpa using specNorm_nonneg A

end LanczosDecomp

/-- The canonical positive Lanczos off-diagonal is positive and at most the
ambient spectral norm below breakdown. Source: Gautschi (2004), Theorem 1.28.
atlas: recurrence-coefficient-bounds (partial) -/
theorem beta_arnoldiDecomp_pos_and_le_specNorm (A : Matrix n n ℝ) (b : n → ℝ)
    {q : ℕ} (hq : q ≤ krylovGrade A b) {j : ℕ} (hj0 : 0 < j) (hj : j < q) :
    0 < LanczosDecomp.beta (arnoldiDecomp A b q hq) j ∧
      LanczosDecomp.beta (arnoldiDecomp A b q hq) j ≤ specNorm A := by
  have hpos := LanczosDecomp.beta_arnoldiDecomp_pos A b hq hj0 hj
  exact ⟨hpos, by simpa only [abs_of_pos hpos] using
    LanczosDecomp.abs_beta_le_specNorm (arnoldiDecomp A b q hq) j⟩

end NLAlib
