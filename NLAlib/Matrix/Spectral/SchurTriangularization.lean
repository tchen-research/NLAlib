import NLAlib.ForMathlib.Analysis.SchurTriangularization
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Complex unitary Schur triangularization

An orthonormal triangularizing basis gives an actual unitary matrix factor,
whose triangular diagonal lists the characteristic roots with multiplicity.
Source: Horn–Johnson (2013), Theorem 2.3.1;
atlas `schur-triangularization`.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex Schur triangularization with an explicit enumeration of any
finite matrix index type. Source: Horn–Johnson (2013), Theorem 2.3.1; the
triangular factor's diagonal is certified by its characteristic polynomial,
including repeated eigenvalues and the empty matrix.
atlas: schur-triangularization (partial) -/
theorem exists_unitary_schur_triangularization (A : Matrix n n ℂ)
    (e : Fin (Fintype.card n) ≃ n) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ),
      A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ ∧
      (∀ i j, e.symm j < e.symm i → T i j = 0) ∧
      A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) := by
  classical
  let f : Module.End ℂ (EuclideanSpace ℂ n) := A.toEuclideanLin
  obtain ⟨b₀, hb₀⟩ := exists_orthonormalBasis_upper_triangular (Fintype.card n) f
    (finrank_euclideanSpace (𝕜 := ℂ))
  let b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b₀.reindex e
  let c := EuclideanSpace.basisFun n ℂ
  let U : Matrix.unitaryGroup n ℂ :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T : Matrix n n ℂ := f.toMatrix b.toBasis b.toBasis
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hUUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hback : b.toBasis.toMatrix c.toBasis = (U : Matrix n n ℂ)ᴴ := by
    calc
      b.toBasis.toMatrix c.toBasis =
          b.toBasis.toMatrix c.toBasis * ((U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ) := by
            rw [hUU, Matrix.mul_one]
      _ = (b.toBasis.toMatrix c.toBasis * (U : Matrix n n ℂ)) * (U : Matrix n n ℂ)ᴴ :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (U : Matrix n n ℂ)ᴴ := by
        change (b.toBasis.toMatrix c.toBasis * c.toBasis.toMatrix b.toBasis) *
          (U : Matrix n n ℂ)ᴴ = _
        rw [Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
  have hA : A = (U : Matrix n n ℂ) * T * (U : Matrix n n ℂ)ᴴ := by
    have hbasis := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis b.toBasis c.toBasis b.toBasis f
    have hstd : f.toMatrix c.toBasis c.toBasis = A :=
      LinearMap.toMatrix_toLin c.toBasis c.toBasis A
    calc
      A = f.toMatrix c.toBasis c.toBasis := hstd.symm
      _ = c.toBasis.toMatrix b.toBasis * f.toMatrix b.toBasis b.toBasis *
          b.toBasis.toMatrix c.toBasis := hbasis.symm
      _ = _ := by rw [hback]
  have htri : ∀ i j, e.symm j < e.symm i → T i j = 0 := by
    intro i j hij
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [b, OrthonormalBasis.reindex_apply] using hb₀ (e.symm i) (e.symm j) hij
  have hTfin : (T.submatrix e e).IsUpperTriangular := by
    intro i j hij
    exact htri (e i) (e j) (by simpa using hij)
  have hchar : T.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) := by
    calc
      T.charpoly = (T.submatrix e e).charpoly := (Matrix.charpoly_reindex e.symm T).symm
      _ = ∏ i : Fin (Fintype.card n), (Polynomial.X - Polynomial.C (T (e i) (e i))) :=
        Matrix.charpoly_of_isUpperTriangular _ hTfin
      _ = _ := e.prod_comp (fun i => Polynomial.X - Polynomial.C (T i i))
  refine ⟨U, T, hA, htri, ?_⟩
  rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUUt, Matrix.one_mul, hchar]

/-- Complex Schur triangularization over `Fin n`, in the usual upper
triangular matrix notation, with multiplicities certified by the diagonal
characteristic factorization. Source: Horn–Johnson (2013), Theorem 2.3.1.
atlas: schur-triangularization (partial) -/
theorem exists_unitary_upperTriangular_diagonal_charpoly (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ) :
    ∃ (U : Matrix.unitaryGroup (Fin k) ℂ) (T : Matrix (Fin k) (Fin k) ℂ),
      A = (U : Matrix (Fin k) (Fin k) ℂ) * T * (U : Matrix (Fin k) (Fin k) ℂ)ᴴ ∧
      T.IsUpperTriangular ∧ A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) := by
  have hcard : Fintype.card (Fin k) = k := Fintype.card_fin k
  let e : Fin (Fintype.card (Fin k)) ≃ Fin k := finCongr hcard
  obtain ⟨U, T, hA, htri, hchar⟩ := exists_unitary_schur_triangularization A e
  refine ⟨U, T, hA, ?_, hchar⟩
  intro i j hij
  apply htri i j
  exact hij

end NLAlib
