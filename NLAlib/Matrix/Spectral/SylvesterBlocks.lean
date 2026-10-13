import NLAlib.Matrix.Spectral.SylvesterQualitative
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real Sylvester equations and disjoint-spectrum block intertwiners

Complexification transfers spectral disjointness to coprime real
characteristic polynomials. Disjoint spectra on different block indices
force arbitrary rectangular intertwiners to be block diagonal.
Source: Horn–Johnson (2013), Theorem 2.4.4.1 and Corollary 2.4.4.2.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Disjoint complex spectra give exactly one real solution of every real
Sylvester equation. Source: Horn–Johnson (2013), Theorem 2.4.4.1;
arbitrary finite rectangular shapes, including empty ones, are allowed.
atlas: sylvester-equation -/
theorem existsUnique_real_sylvester_of_disjoint_complex_spectrum
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (hdisj : Disjoint (spectrum ℂ (A.map Complex.ofReal))
      (spectrum ℂ (B.map Complex.ofReal))) (C : Matrix m n ℝ) :
    ∃! X : Matrix m n ℝ, A * X - X * B = C := by
  have hcop := (isCoprime_charpoly_iff_disjoint_spectrum
    (A.map Complex.ofReal) (B.map Complex.ofReal)).mpr hdisj
  have hA : (A.map Complex.ofReal).charpoly = Polynomial.map Complex.ofRealHom A.charpoly :=
    Matrix.charpoly_map A Complex.ofRealHom
  have hB : (B.map Complex.ofReal).charpoly = Polynomial.map Complex.ofRealHom B.charpoly :=
    Matrix.charpoly_map B Complex.ofRealHom
  rw [hA, hB, Polynomial.isCoprime_map] at hcop
  exact existsUnique_sylvester_of_isCoprime_charpoly A B hcop C

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {m n : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] {K : Type*} [Field K]

omit [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] in
/-- Left multiplication by a block diagonal matrix acts separately on
each block row. Source: Horn–Johnson (2013), §0.7; block multiplication. -/
theorem submatrix_blockDiagonal'_mul (A : ∀ i, Matrix (m i) (m i) K)
    (X : Matrix (Σ i, m i) (Σ i, n i) K) (i j : ι) :
    (Matrix.blockDiagonal' A * X).submatrix (Sigma.mk i) (Sigma.mk j) =
      A i * X.submatrix (Sigma.mk i) (Sigma.mk j) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro k hki
    exact Finset.sum_eq_zero fun c _ => by
      rw [Matrix.blockDiagonal'_apply_ne A a c hki.symm, zero_mul]

omit [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, DecidableEq (n i)] in
/-- Right multiplication by a block diagonal matrix acts separately on
each block column. Source: Horn–Johnson (2013), §0.7; block multiplication. -/
theorem submatrix_mul_blockDiagonal' (B : ∀ i, Matrix (n i) (n i) K)
    (X : Matrix (Σ i, m i) (Σ i, n i) K) (i j : ι) :
    (X * Matrix.blockDiagonal' B).submatrix (Sigma.mk i) (Sigma.mk j) =
      X.submatrix (Sigma.mk i) (Sigma.mk j) * B j := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single j]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro k hkj
    exact Finset.sum_eq_zero fun c _ => by
      rw [Matrix.blockDiagonal'_apply_ne B c b hkj, mul_zero]

/-- A rectangular intertwiner between aligned block diagonal matrices
vanishes off the block diagonal if the corresponding distinct block spectra
are disjoint. Its diagonal blocks still intertwine the corresponding blocks.
Source: Horn–Johnson (2013), Corollary 2.4.4.2.
atlas: sylvester-equation -/
theorem eq_blockDiagonal'_of_intertwines_of_disjoint_spectrum [IsAlgClosed K]
    (A : ∀ i, Matrix (m i) (m i) K) (B : ∀ i, Matrix (n i) (n i) K)
    (hdisj : ∀ i j, i ≠ j → Disjoint (spectrum K (A i)) (spectrum K (B j)))
    {X : Matrix (Σ i, m i) (Σ i, n i) K}
    (hX : Matrix.blockDiagonal' A * X = X * Matrix.blockDiagonal' B) :
    X = Matrix.blockDiagonal' (Matrix.blockDiag' X) ∧
      ∀ i, A i * Matrix.blockDiag' X i = Matrix.blockDiag' X i * B i := by
  have hblock (i j : ι) : A i * X.submatrix (Sigma.mk i) (Sigma.mk j) =
      X.submatrix (Sigma.mk i) (Sigma.mk j) * B j := by
    have h := congrArg (fun M : Matrix (Σ i, m i) (Σ i, n i) K =>
      M.submatrix (Sigma.mk i) (Sigma.mk j)) hX
    simpa only [submatrix_blockDiagonal'_mul, submatrix_mul_blockDiagonal'] using h
  constructor
  · ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ a b hij]
      exact congrArg (fun M : Matrix (m i) (n j) K => M a b)
        (eq_zero_of_mul_eq_mul_of_disjoint_spectrum (hdisj i j hij) (hblock i j))
  · exact fun i => hblock i i

/-- The commutant of a block diagonal matrix with pairwise disjoint block
spectra consists exactly of block diagonal matrices whose diagonal blocks
commute with the corresponding primary blocks. Source: Horn–Johnson (2013),
Corollary 2.4.4.2; the diagonal commutation conditions are essential.
atlas: sylvester-equation (partial) -/
theorem commute_blockDiagonal'_iff [IsAlgClosed K]
    (A : ∀ i, Matrix (m i) (m i) K)
    (hdisj : Pairwise fun i j => Disjoint (spectrum K (A i)) (spectrum K (A j)))
    (X : Matrix (Σ i, m i) (Σ i, m i) K) :
    Commute (Matrix.blockDiagonal' A) X ↔
      ∃ Y : ∀ i, Matrix (m i) (m i) K,
        X = Matrix.blockDiagonal' Y ∧ ∀ i, Commute (A i) (Y i) := by
  constructor
  · intro hX
    obtain ⟨hdiag, hcomm⟩ := eq_blockDiagonal'_of_intertwines_of_disjoint_spectrum
      A A (fun _ _ hij => hdisj hij) hX.eq
    exact ⟨Matrix.blockDiag' X, hdiag, hcomm⟩
  · rintro ⟨Y, rfl, hY⟩
    change Matrix.blockDiagonal' A * Matrix.blockDiagonal' Y =
      Matrix.blockDiagonal' Y * Matrix.blockDiagonal' A
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext fun i => (hY i).eq)

end Blocks
end NLAlib
