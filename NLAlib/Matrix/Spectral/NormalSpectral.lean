import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Spectral theorem for complex normal matrices

A normal matrix's Hermitian real and imaginary parts commute. Their joint
orthogonal eigenspaces supply a unitary eigenbasis without a Schur theorem.
Source: Horn–Johnson (2013), Theorems 2.5.3 and 2.5.15;
atlas `normal-matrices`.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped Matrix ComplexStarModule Matrix.Norms.L2Operator
open Complex

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every complex normal matrix has an orthonormal eigenbasis. Source:
Horn–Johnson (2013), Theorem 2.5.3; the proof uses joint eigenspaces of the
Hermitian real and imaginary parts and includes an empty index type.
atlas: normal-matrices (partial) -/
theorem exists_orthonormalBasis_eigenvectors_of_normal {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (d : n → ℂ),
      ∀ j, A *ᵥ ⇑(b j) = d j • ⇑(b j) := by
  classical
  let : IsStarNormal A := ⟨hA.symm⟩
  let H : Matrix n n ℂ := realPart A
  let K : Matrix n n ℂ := imaginaryPart A
  have hH : H.IsHermitian := (realPart A).property
  have hK : K.IsHermitian := (imaginaryPart A).property
  have hHC : H.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hKC : K.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hK
  have hcomm : Commute H.toEuclideanLin K.toEuclideanLin :=
    (Commute.realPart_imaginaryPart A).map
      (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℂ n)).toRingHom
  let W (χ : ℂ × ℂ) : Submodule ℂ (EuclideanSpace ℂ n) :=
    Module.End.eigenspace H.toEuclideanLin χ.2 ⊓ Module.End.eigenspace K.toEuclideanLin χ.1
  have hW : DirectSum.IsInternal W := hHC.directSum_isInternal_of_commute hKC hcomm
  have hfinite : Set.Finite {χ | W χ ≠ ⊥} :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hW.submodule_iSupIndep
  let : Fintype {χ : ℂ × ℂ // W χ ≠ ⊥} := hfinite.fintype
  let W' (χ : {χ // W χ ≠ ⊥}) := W χ
  have hW' : DirectSum.IsInternal W' := DirectSum.isInternal_ne_bot_iff.mpr hW
  have horth := (hHC.orthogonalFamily_eigenspace_inf_eigenspace hKC).comp
    (Subtype.val_injective : Function.Injective (fun χ : {χ // W χ ≠ ⊥} => χ.val))
  let b₀ := hW'.subordinateOrthonormalBasis (finrank_euclideanSpace (𝕜 := ℂ)) horth
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b₀.reindex e
  let χ (j : n) := hW'.subordinateOrthonormalBasisIndex
    (finrank_euclideanSpace (𝕜 := ℂ)) (e.symm j) horth
  let d (j : n) : ℂ := (χ j).val.2 + I * (χ j).val.1
  refine ⟨b, d, fun j => ?_⟩
  have hmem : b j ∈ W' (χ j) := by
    simp only [b, OrthonormalBasis.reindex_apply]
    exact hW'.subordinateOrthonormalBasis_subordinate
      (finrank_euclideanSpace (𝕜 := ℂ)) (e.symm j) horth
  have hHj : H.toEuclideanLin (b j) = (χ j).val.2 • b j :=
    Module.End.mem_eigenspace_iff.mp hmem.1
  have hKj : K.toEuclideanLin (b j) = (χ j).val.1 • b j :=
    Module.End.mem_eigenspace_iff.mp hmem.2
  have hdecomp : A = H + I • K := (realPart_add_I_smul_imaginaryPart A).symm
  have heig : A.toEuclideanLin (b j) = d j • b j := by
    rw [hdecomp, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hHj, hKj, smul_smul, ← add_smul]
  exact congrArg (fun v : EuclideanSpace ℂ n => ⇑v) heig

/-- Every complex normal matrix is unitarily diagonalizable. Source:
Horn–Johnson (2013), Theorem 2.5.3; the unitary and eigenvalue list are
constructed from the orthonormal joint eigenbasis, including empty matrices.
atlas: normal-matrices (partial) -/
theorem exists_unitary_diagonalization_of_normal {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ),
      A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ := by
  obtain ⟨b, d, hb⟩ := exists_orthonormalBasis_eigenvectors_of_normal hA
  let U : Matrix.unitaryGroup n ℂ :=
    ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hAU : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal d := by
    ext i j
    have hcol : ∀ k, (U : Matrix n n ℂ) k j = (b j) k := fun _ => rfl
    rw [Matrix.mul_diagonal]
    simpa only [Matrix.mul_apply, hcol, Matrix.mulVec,
      dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun (hb j) i
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  refine ⟨U, d, ?_⟩
  calc
    A = A * ((U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ) := by
      rw [hUU, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hAU]

/-- A unitary diagonalization implies normality. Source: Horn–Johnson
(2013), Theorem 2.5.3; diagonal entries may be arbitrary complex numbers.
atlas: normal-matrices (partial) -/
theorem mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization
    {A : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ)
    (hA : A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ) :
    A * Aᴴ = Aᴴ * A := by
  have hUU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [hA]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),
    hUU, Matrix.one_mul]
  have hD : d * star d = star d * d := funext fun i => mul_comm (d i) (star (d i))
  rw [← Matrix.mul_assoc (Matrix.diagonal d), ← Matrix.mul_assoc (Matrix.diagonal (star d)),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  change (U : Matrix n n ℂ) * (Matrix.diagonal (d * star d) * (U : Matrix n n ℂ)ᴴ) =
    (U : Matrix n n ℂ) * (Matrix.diagonal (star d * d) * (U : Matrix n n ℂ)ᴴ)
  rw [hD]

/-- A complex matrix is normal exactly when it is unitarily diagonalizable.
Source: Horn–Johnson (2013), Theorem 2.5.3.
atlas: normal-matrices (partial) -/
theorem normal_iff_exists_unitary_diagonalization (A : Matrix n n ℂ) :
    A * Aᴴ = Aᴴ * A ↔ ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ),
      A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ :=
  ⟨exists_unitary_diagonalization_of_normal,
    fun ⟨U, d, hA⟩ => mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization U d hA⟩

end NLAlib
