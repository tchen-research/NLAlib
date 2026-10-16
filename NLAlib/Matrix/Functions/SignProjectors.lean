import NLAlib.Matrix.Functions.SignExistence
import NLAlib.Matrix.Spectral.EigenvectorSpectrum
import NLAlib.ForMathlib.LinearAlgebra.SignPrimaryDecomposition

/-!
# The spectral ranges of the matrix-sign projectors

The half-sign projectors select the full generalized eigenspaces in
the right and left half-planes. Defective and nonnormal inputs are
included. Higham, Functions of Matrices, Chapter 5.
-/

noncomputable section
open Matrix Module
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The primary spectral subspace for an arbitrary set of complex
spectral values, formed from maximal generalized eigenspaces. -/
def matrixSpectralSubspace (A : Matrix n n ℂ) (Ω : Set ℂ) : Submodule ℂ (n → ℂ) :=
  ⨆ z : Ω, Module.End.maxGenEigenspace A.toLin' z.val

/-- The range of an algebraic half-involution is its signed eigenspace. -/
theorem range_half_involution_eq_eigenspace {S : Matrix n n ℂ} (hS : S^2=1)
    (a : ℂ) (ha : a^2=1) :
    LinearMap.range ((2 : ℂ)⁻¹ • (1+a • S)).toLin' = Module.End.eigenspace S.toLin' a := by
  have hs (v : n → ℂ) : S *ᵥ (S *ᵥ v)=v := by
    rw [Matrix.mulVec_mulVec, ← pow_two, hS, Matrix.one_mulVec]
  have haa : a*a=1 := by simpa only [pow_two] using ha
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change S *ᵥ (((2 : ℂ)⁻¹ • (1+a • S)) *ᵥ w) =
      a • (((2 : ℂ)⁻¹ • (1+a • S)) *ᵥ w)
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_smul, Matrix.mulVec_add, hs]
    rw [smul_comm a ((2 : ℂ)⁻¹)]
    congr 1
    simp only [smul_add, smul_smul, haa, one_smul]
    abel
  · intro hv
    have he : S *ᵥ v = a • v := Module.End.mem_eigenspace_iff.mp hv
    refine ⟨v, ?_⟩
    change ((2 : ℂ)⁻¹ • (1+a • S)) *ᵥ v = v
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, he,
      smul_smul, haa, one_smul]
    rw [← two_smul ℂ v, smul_smul]
    norm_num

/-- The signed eigenspace of a matrix sign is the matching primary
spectral half-plane. -/
theorem IsMatrixSign.eigenspace_eq_spectralSubspace {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (a : ℂ) (ha : a^2=1) :
    Module.End.eigenspace S.toLin' a = matrixSpectralSubspace A {z | 0 < (a*z).re} := by
  have hc : Commute A.toLin' S.toLin' := by
    change A.toLin' * S.toLin' = S.toLin' * A.toLin'
    simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hS.2.1.eq
  have hss : S.toLin'^2=1 := by
    calc
      _ = (S^2).toLin' := (Matrix.toLin'_pow S 2).symm
      _ = (1 : Matrix n n ℂ).toLin' := congrArg Matrix.toLin' hS.1
      _ = 1 := by rw [Matrix.toLin'_one]; rfl
  apply Module.End.eigenspace_eq_iSup_maxGenEigenspace_of_stable_involution
    A.toLin' S.toLin' hc hss _ a ha
  intro z hz
  obtain ⟨v, hv, hv0⟩ := hz.exists_hasEigenvector
  apply hS.2.2 z (Matrix.mem_spectrum_of_mulVec_eq_smul hv0 _)
  have h := Module.End.mem_eigenspace_iff.mp hv
  change S *ᵥ (A *ᵥ v) = z • v at h
  rwa [Matrix.mulVec_mulVec] at h

/-- The canonical matrix sign has complementary idempotent half-sign
projectors onto exactly the positive and negative primary spectral
subspaces. This includes nonnormal matrices and all Jordan blocks.
atlas: matrix-sign-spectral-projectors -/
theorem matrixSign_spectral_projectors {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) :
    let S := matrixSign A
    let P := (2 : ℂ)⁻¹ • (1+S)
    let Q := (2 : ℂ)⁻¹ • (1-S)
    IsMatrixSign A S ∧ P*P=P ∧ Q*Q=Q ∧ P*Q=0 ∧ Q*P=0 ∧ P+Q=1 ∧
      LinearMap.range P.toLin' = matrixSpectralSubspace A {z | 0 < z.re} ∧
      LinearMap.range Q.toLin' = matrixSpectralSubspace A {z | z.re < 0} := by
  dsimp
  have hs := isMatrixSign_matrixSign hA
  obtain ⟨hp, hq, hpq, hqp, hsum⟩ := hs.projectors
  refine ⟨hs, hp, hq, hpq, hqp, hsum, ?_, ?_⟩
  · simpa using (range_half_involution_eq_eigenspace hs.1 1 (by norm_num)).trans
      (hs.eigenspace_eq_spectralSubspace 1 (by norm_num))
  · have h := (range_half_involution_eq_eigenspace hs.1 (-1) (by norm_num)).trans
      (hs.eigenspace_eq_spectralSubspace (-1) (by norm_num))
    simpa only [neg_one_smul, add_neg_cancel_right, ← sub_eq_add_neg,
      neg_one_mul, Complex.neg_re, neg_pos] using h

end NLAlib
