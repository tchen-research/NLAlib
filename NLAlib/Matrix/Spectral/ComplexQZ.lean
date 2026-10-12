import NLAlib.ForMathlib.Analysis.PencilTriangularization
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Complex QZ for every square matrix pencil

Independent unitary bases simultaneously make both pencil matrices upper
triangular. The construction includes singular, identically singular and empty
pencils, with no invertibility or regularity hypothesis.
-/

noncomputable section
open Module
open scoped Matrix
namespace NLAlib

/-- Every complex square pencil admits a simultaneous two-sided unitary
upper triangular form. The common row and column order may be any enumeration
of the finite labels. Singular and identically singular pencils, common zero
images and the empty pencil are included. Horn–Johnson 2013, Theorem 2.6.1;
derivations §gen:schur, Theorem gen:qz.
atlas: schur-triangularization (partial) -/
theorem exists_unitary_qz_triangularization {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (order : Fin (Fintype.card n) ≃ n) :
    ∃ V W : Matrix.unitaryGroup n ℂ, ∃ T₁ T₂ : Matrix n n ℂ,
      A = (V : Matrix n n ℂ) * T₁ * (W : Matrix n n ℂ)ᴴ ∧
      B = (V : Matrix n n ℂ) * T₂ * (W : Matrix n n ℂ)ᴴ ∧
      (∀ i j, order.symm j < order.symm i → T₁ i j = 0) ∧
      (∀ i j, order.symm j < order.symm i → T₂ i j = 0) := by
  classical
  let a := A.toEuclideanLin
  let b := B.toEuclideanLin
  obtain ⟨e₀, f₀, hA₀, hB₀⟩ := exists_orthonormalBases_pencil_upper_triangular
    (Fintype.card n) a b (finrank_euclideanSpace (𝕜 := ℂ)) (finrank_euclideanSpace (𝕜 := ℂ))
  let e : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := e₀.reindex order
  let f : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := f₀.reindex order
  let c := EuclideanSpace.basisFun n ℂ
  let V : Matrix.unitaryGroup n ℂ :=
    ⟨c.toBasis.toMatrix f.toBasis, c.toMatrix_orthonormalBasis_mem_unitary f⟩
  let W : Matrix.unitaryGroup n ℂ :=
    ⟨c.toBasis.toMatrix e.toBasis, c.toMatrix_orthonormalBasis_mem_unitary e⟩
  let T (M : Matrix n n ℂ) := M.toEuclideanLin.toMatrix e.toBasis f.toBasis
  have hWW : (W : Matrix n n ℂ) * (W : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self W
  have hback : e.toBasis.toMatrix c.toBasis = (W : Matrix n n ℂ)ᴴ := by
    calc
      e.toBasis.toMatrix c.toBasis =
          e.toBasis.toMatrix c.toBasis * ((W : Matrix n n ℂ) * (W : Matrix n n ℂ)ᴴ) := by
            rw [hWW, Matrix.mul_one]
      _ = (e.toBasis.toMatrix c.toBasis * (W : Matrix n n ℂ)) * (W : Matrix n n ℂ)ᴴ :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (W : Matrix n n ℂ)ᴴ := by
        change (e.toBasis.toMatrix c.toBasis * c.toBasis.toMatrix e.toBasis) * _ = _
        rw [Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
  have hFactor (M : Matrix n n ℂ) : M = (V : Matrix n n ℂ) * T M * (W : Matrix n n ℂ)ᴴ := by
    have hh := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis e.toBasis c.toBasis f.toBasis M.toEuclideanLin
    have hstd : M.toEuclideanLin.toMatrix c.toBasis c.toBasis = M :=
      LinearMap.toMatrix_toLin c.toBasis c.toBasis M
    rw [hback, hstd] at hh
    exact hh.symm
  refine ⟨V, W, T A, T B, hFactor A, hFactor B, ?_, ?_⟩
  · intro i j hij
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [e, f, OrthonormalBasis.reindex_apply] using hA₀ (order.symm i) (order.symm j) hij
  · intro i j hij
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [e, f, OrthonormalBasis.reindex_apply] using hB₀ (order.symm i) (order.symm j) hij

/-- Complex QZ in the usual finite-coordinate upper triangular notation,
including empty and singular pencils. Horn–Johnson 2013, Theorem 2.6.1.
atlas: schur-triangularization (partial) -/
theorem exists_unitary_qz_upperTriangular {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ∃ V W : Matrix.unitaryGroup (Fin k) ℂ, ∃ T₁ T₂ : Matrix (Fin k) (Fin k) ℂ,
      A = (V : Matrix (Fin k) (Fin k) ℂ) * T₁ * (W : Matrix (Fin k) (Fin k) ℂ)ᴴ ∧
      B = (V : Matrix (Fin k) (Fin k) ℂ) * T₂ * (W : Matrix (Fin k) (Fin k) ℂ)ᴴ ∧
      T₁.IsUpperTriangular ∧ T₂.IsUpperTriangular := by
  obtain ⟨V, W, T₁, T₂, hA, hB, hT₁, hT₂⟩ :=
    exists_unitary_qz_triangularization A B (finCongr (Fintype.card_fin k))
  exact ⟨V, W, T₁, T₂, hA, hB, fun _ _ h => hT₁ _ _ h, fun _ _ h => hT₂ _ _ h⟩

end NLAlib
