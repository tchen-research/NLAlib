import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Coordinates in a Hermitian eigenbasis

The real and complex spectral identities needed for shifted inverse iteration. Coordinates
are inner products against Mathlib's orthonormal eigenbasis; no additional eigenbasis is
chosen. Source: Horn–Johnson (2013), spectral theorem; Trefethen–Bau (1997), Lecture 27.
-/

noncomputable section

open scoped Matrix ComplexConjugate InnerProductSpace
open Matrix

namespace Matrix.IsHermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- The coordinates of a vector in the orthonormal eigenbasis of a Hermitian matrix. -/
def eigenvectorCoordinates (x : n → 𝕜) : n → 𝕜 :=
  fun i => ⟪hA.eigenvectorBasis i, WithLp.toLp 2 x⟫_𝕜

/-- Eigenvector coordinates are the usual conjugate dot products. -/
theorem eigenvectorCoordinates_apply (x : n → 𝕜) (i : n) :
    hA.eigenvectorCoordinates x i = star ⇑(hA.eigenvectorBasis i) ⬝ᵥ x := by
  rw [eigenvectorCoordinates, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Parseval's identity in the Hermitian eigenbasis. -/
theorem sum_sq_norm_eigenvectorCoordinates (x : n → 𝕜) :
    ∑ i, ‖hA.eigenvectorCoordinates x i‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 :=
  hA.eigenvectorBasis.sum_sq_norm_inner_right _

/-- Eigenvector coordinates determine the vector. -/
theorem eigenvectorCoordinates_injective : Function.Injective hA.eigenvectorCoordinates := by
  intro x y h
  apply WithLp.toLp_injective (p := 2)
  apply hA.eigenvectorBasis.repr.injective
  ext i
  simpa [eigenvectorCoordinates, OrthonormalBasis.repr_apply_apply] using congrFun h i

/-- Eigenvector coordinates are linear in the input vector. -/
theorem eigenvectorCoordinates_smul (c : 𝕜) (x : n → 𝕜) :
    hA.eigenvectorCoordinates (c • x) = c • hA.eigenvectorCoordinates x := by
  ext i
  simp [eigenvectorCoordinates, WithLp.toLp_smul, inner_smul_right]

/-- Subtraction in eigenvector coordinates. -/
theorem eigenvectorCoordinates_sub (x y : n → 𝕜) :
    hA.eigenvectorCoordinates (x - y) =
      hA.eigenvectorCoordinates x - hA.eigenvectorCoordinates y := by
  ext i
  simp [eigenvectorCoordinates, WithLp.toLp_sub, inner_sub_right]

/-- The eigenbasis vectors have the standard coordinate vectors as coordinates. -/
theorem eigenvectorCoordinates_eigenvectorBasis (i j : n) :
    hA.eigenvectorCoordinates ⇑(hA.eigenvectorBasis i) j = if j = i then 1 else 0 := by
  exact hA.eigenvectorBasis.inner_eq_ite j i

/-- Matrix multiplication multiplies each eigenvector coordinate by its real eigenvalue. -/
theorem eigenvectorCoordinates_mulVec (x : n → 𝕜) (i : n) :
    hA.eigenvectorCoordinates (A *ᵥ x) i =
      (hA.eigenvalues i : 𝕜) * hA.eigenvectorCoordinates x i := by
  have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (hA.eigenvectorBasis i) (WithLp.toLp 2 x)
  have he : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  change ⟪hA.eigenvectorBasis i, A.toEuclideanLin (WithLp.toLp 2 x)⟫_𝕜 = _
  rw [← hs, he, RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left]
  simp [eigenvectorCoordinates]

/-- A scalar shift subtracts the shift from every eigenvalue in coordinates. -/
theorem eigenvectorCoordinates_sub_smul_mulVec (μ : ℝ) (x : n → 𝕜) (i : n) :
    hA.eigenvectorCoordinates ((A - μ • (1 : Matrix n n 𝕜)) *ᵥ x) i =
      ((hA.eigenvalues i - μ : ℝ) : 𝕜) * hA.eigenvectorCoordinates x i := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [eigenvectorCoordinates, WithLp.toLp_sub, WithLp.toLp_smul,
    inner_sub_right, RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_right]
  rw [← eigenvectorCoordinates, hA.eigenvectorCoordinates_mulVec]
  simp only [eigenvectorCoordinates, RCLike.ofReal_sub]
  ring

/-- A real shift avoiding every eigenvalue of a Hermitian matrix is invertible. -/
theorem isUnit_sub_smul_one_of_eigenvalues_ne {μ : ℝ}
    (hμ : ∀ i, hA.eigenvalues i ≠ μ) : IsUnit (A - μ • (1 : Matrix n n 𝕜)) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply hA.eigenvectorCoordinates_injective
  ext i
  have h := congrArg (fun v => hA.eigenvectorCoordinates v i) hxy
  simp only [hA.eigenvectorCoordinates_sub_smul_mulVec] at h
  exact mul_left_cancel₀ (RCLike.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hμ i))) h

/-- Invertibility of a real Hermitian shift is equivalent to avoiding every eigenvalue. -/
theorem isUnit_sub_smul_one_iff_eigenvalues_ne (μ : ℝ) :
    IsUnit (A - μ • (1 : Matrix n n 𝕜)) ↔ ∀ i, hA.eigenvalues i ≠ μ := by
  refine ⟨?_, hA.isUnit_sub_smul_one_of_eigenvalues_ne⟩
  intro hB i hi
  have hker : (A - μ • (1 : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis i) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hA.mulVec_eigenvectorBasis, hi, sub_self]
  have hz : ⇑(hA.eigenvectorBasis i) = (0 : n → 𝕜) :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hB) (by simpa using hker)
  have hn := hA.eigenvectorBasis.norm_eq_one i
  have hv : hA.eigenvectorBasis i = 0 := by ext j; exact congrFun hz j
  rw [hv, norm_zero] at hn
  exact zero_ne_one hn

/-- The coordinates of a shifted inverse are the original coordinates divided by the
shifted eigenvalues. This includes both real symmetric and complex Hermitian matrices. -/
theorem eigenvectorCoordinates_inv_sub_smul_mulVec {μ : ℝ}
    (hμ : ∀ i, hA.eigenvalues i ≠ μ) (x : n → 𝕜) (i : n) :
    hA.eigenvectorCoordinates ((A - μ • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x) i =
      (((hA.eigenvalues i - μ : ℝ) : 𝕜))⁻¹ * hA.eigenvectorCoordinates x i := by
  let B := A - μ • (1 : Matrix n n 𝕜)
  have hB := hA.isUnit_sub_smul_one_of_eigenvalues_ne hμ
  have hBB : B *ᵥ (B⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hB), Matrix.one_mulVec]
  have h := hA.eigenvectorCoordinates_sub_smul_mulVec μ (B⁻¹ *ᵥ x) i
  rw [hBB] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀
    (RCLike.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hμ i))), one_mul]

/-- The real quadratic form is the eigenvalue-weighted sum of squared coordinates. -/
theorem re_quadForm_eq_sum_eigenvectorCoordinates (x : n → 𝕜) :
    RCLike.re (NLAlib.quadForm A x) =
      ∑ i, hA.eigenvalues i * ‖hA.eigenvectorCoordinates x i‖ ^ 2 := by
  have h := hA.eigenvectorBasis.sum_inner_mul_inner
    (WithLp.toLp 2 x) (WithLp.toLp 2 (A *ᵥ x))
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  change ∑ i, ⟪WithLp.toLp 2 x, hA.eigenvectorBasis i⟫_𝕜 *
    hA.eigenvectorCoordinates (A *ᵥ x) i = NLAlib.quadForm A x at h
  rw [← h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hA.eigenvectorCoordinates_mulVec, ← inner_conj_symm]
  change RCLike.re (star (hA.eigenvectorCoordinates x i) *
    ((hA.eigenvalues i : 𝕜) * hA.eigenvectorCoordinates x i)) = _
  rw [mul_left_comm, RCLike.re_ofReal_mul, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The Rayleigh quotient is the eigenvalue-weighted average of squared coordinates. -/
theorem rayleighQuotient_eq_sum_eigenvectorCoordinates (x : n → 𝕜) :
    NLAlib.rayleighQuotient A x =
      (∑ i, hA.eigenvalues i * ‖hA.eigenvectorCoordinates x i‖ ^ 2) /
        (∑ i, ‖hA.eigenvectorCoordinates x i‖ ^ 2) := by
  rw [NLAlib.rayleighQuotient_def, hA.re_quadForm_eq_sum_eigenvectorCoordinates,
    hA.sum_sq_norm_eigenvectorCoordinates]
  congr 1
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 x)
    (WithLp.toLp 2 x), inner_self_eq_norm_sq_to_K]
  simp

end Matrix.IsHermitian
