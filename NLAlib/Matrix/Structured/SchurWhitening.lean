import NLAlib.Matrix.Structured.SaddlePoint
import NLAlib.Matrix.Basic.QuadForm

/-!
# Positive definiteness and order bounds after Schur whitening

The whitened coupling uses the actual inverse square roots. Its Gram matrix is
positive definite under full row rank, becomes the identity for the exact Schur
complement, and inherits the advertised relative Loewner bounds.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Full row rank gives a positive-definite whitened Schur matrix. -/
theorem posDef_saddle_coupling_gram {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜}
    (hA : A.PosDef) (hShat : Shat.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    let C := cfc (fun x => (Real.sqrt x)⁻¹) Shat * B * cfc (fun x => (Real.sqrt x)⁻¹) A
    (C * Cᴴ).PosDef := by
  dsimp only
  rw [saddle_coupling_mul_conjTranspose hA]
  have hR : (cfc (fun x => (Real.sqrt x)⁻¹) Shat).IsHermitian := cfc_predicate _ _
  have hu : IsUnit (cfc (fun x => (Real.sqrt x)⁻¹) Shat) :=
    ⟨⟨_, cfc Real.sqrt Shat, cfc_inv_sqrt_mul_sqrt hShat,
      cfc_sqrt_mul_inv_sqrt hShat⟩, rfl⟩
  simpa only [hR.eq] using (posDef_saddleSchurComplement hA hB).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr hu)

open scoped Matrix.Norms.L2Operator in
/-- Exact Schur whitening gives orthonormal rows of the coupling. -/
theorem saddle_coupling_gram_eq_one {A : Matrix n n 𝕜} (hA : A.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    let C := cfc (fun x => (Real.sqrt x)⁻¹) (saddleSchurComplement A B) * B *
      cfc (fun x => (Real.sqrt x)⁻¹) A
    C * Cᴴ = 1 := by
  dsimp only
  rw [saddle_coupling_mul_conjTranspose hA,
    cfc_inv_sqrt_mul_self_mul_inv_sqrt (posDef_saddleSchurComplement hA hB)]

open scoped Matrix.Norms.L2Operator in
/-- Relative Schur bounds give the same scalar bounds on the whitened Gram matrix. -/
theorem saddle_coupling_gram_order {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜}
    (hA : A.PosDef) (hShat : Shat.PosDef) (B : Matrix m n 𝕜) {a b : ℝ}
    (ha : a • Shat ≤ saddleSchurComplement A B)
    (hb : saddleSchurComplement A B ≤ b • Shat) :
    let C := cfc (fun x => (Real.sqrt x)⁻¹) Shat * B * cfc (fun x => (Real.sqrt x)⁻¹) A
    a • (1 : Matrix m m 𝕜) ≤ C * Cᴴ ∧ C * Cᴴ ≤ b • (1 : Matrix m m 𝕜) := by
  dsimp only
  rw [saddle_coupling_mul_conjTranspose hA]
  let R := cfc (fun x => (Real.sqrt x)⁻¹) Shat
  have hR : R.IsHermitian := cfc_predicate _ _
  have he : R * Shat * R = 1 := cfc_inv_sqrt_mul_self_mul_inv_sqrt hShat
  have hlo := (Matrix.le_iff.mp ha).mul_mul_conjTranspose_same R
  have hhi := (Matrix.le_iff.mp hb).mul_mul_conjTranspose_same R
  constructor <;> apply Matrix.le_iff.mpr
  · simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hR.eq, he] using hlo
  · simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hR.eq, he] using hhi

omit [Fintype n] [DecidableEq n] in
private theorem eigenvalues_mem_Icc_of_order {G : Matrix m m 𝕜} (hG : G.IsHermitian)
    {a b : ℝ} (ha : a • (1 : Matrix m m 𝕜) ≤ G) (hb : G ≤ b • (1 : Matrix m m 𝕜))
    (i : m) : hG.eigenvalues i ∈ Set.Icc a b := by
  let v := (hG.eigenvectorBasis i).ofLp
  have hv : G *ᵥ v = (hG.eigenvalues i) • v := hG.mulVec_eigenvectorBasis i
  have hn : star v ⬝ᵥ v = 1 := by
    have h : (inner 𝕜 (hG.eigenvectorBasis i) (hG.eigenvectorBasis i) : 𝕜) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hG.eigenvectorBasis.orthonormal.1 i]
      simp
    rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  have hlo := (Matrix.le_iff.mp ha).re_quadForm_nonneg v
  have hhi := (Matrix.le_iff.mp hb).re_quadForm_nonneg v
  simp only [quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hv, dotProduct_sub, dotProduct_smul, hn, map_sub, RCLike.smul_re, RCLike.one_re,
    mul_one] at hlo hhi
  exact ⟨by linarith, by linarith⟩

open scoped Matrix.Norms.L2Operator in
/-- Every Gram eigenvalue lies between the native relative Schur bounds. -/
theorem saddle_coupling_eigenvalues_mem_Icc {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜}
    (hA : A.PosDef) (hShat : Shat.PosDef) (B : Matrix m n 𝕜) {a b : ℝ}
    (ha : a • Shat ≤ saddleSchurComplement A B)
    (hb : saddleSchurComplement A B ≤ b • Shat) :
    let C := cfc (fun x => (Real.sqrt x)⁻¹) Shat * B * cfc (fun x => (Real.sqrt x)⁻¹) A
    ∀ i, (Matrix.isHermitian_mul_conjTranspose_self C).eigenvalues i ∈ Set.Icc a b := by
  have h := saddle_coupling_gram_order hA hShat B ha hb
  exact eigenvalues_mem_Icc_of_order _ h.1 h.2

end NLAlib
