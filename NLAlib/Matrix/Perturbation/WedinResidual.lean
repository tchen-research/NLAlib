import NLAlib.Matrix.Perturbation.SingularFrameTails
import NLAlib.Matrix.Perturbation.WedinCoupled
import NLAlib.Matrix.Subspaces.PrincipalAngleDefinitions
import NLAlib.Matrix.Subspaces.FrameContractions
import NLAlib.Matrix.Spectral.Weyl
/-!
# Wedin bounds for actual paired singular-vector frames

Leading frames from two actual SVDs obey the coupled residual equations. The
exact mixed singular gap gives constant-one maximum-operator and paired
Frobenius bounds. Source: Wedin (1972), Section 3; atlas `wedin-sin-theta`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

namespace IsSVD
variable {m n k p : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
  {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}

/-- The first ambient complementary singular residual equation is exact.
Wedin (1972), Section 3; no spectral separation is assumed for the identity. -/
theorem coupled_residual_headColumns_left (h : IsSVD A U V) (hkm : k ≤ m) (hkn : k ≤ n)
    (Uhat : Matrix (Fin m) (Fin p) ℝ) (Vhat : Matrix (Fin n) (Fin p) ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) :
    (A - h.truncatedMatrix k) * residual (headColumns V hkn) Vhat -
      residual (headColumns U hkm) Uhat * T =
        residual (headColumns U hkm) (A * Vhat - Uhat * T) := by
  rw [h.sub_truncatedMatrix_mul_residual_headColumns hkm hkn Vhat, residual_mul]
  simp only [residual, Matrix.mul_sub]
  abel

/-- The second ambient complementary singular residual equation is exact.
Wedin (1972), Section 3; unmatched rectangular null directions are retained. -/
theorem coupled_residual_headColumns_right (h : IsSVD A U V) (hkm : k ≤ m) (hkn : k ≤ n)
    (Uhat : Matrix (Fin m) (Fin p) ℝ) (Vhat : Matrix (Fin n) (Fin p) ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) :
    (A - h.truncatedMatrix k)ᵀ * residual (headColumns U hkm) Uhat -
      residual (headColumns V hkn) Vhat * T =
        residual (headColumns V hkn) (Aᵀ * Uhat - Vhat * T) := by
  rw [h.sub_truncatedMatrix_transpose_mul_residual_headColumns hkm hkn Uhat, residual_mul]
  simp only [residual, Matrix.mul_sub]
  abel

end IsSVD

private theorem specNorm_residual_le {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] {Q : Matrix m k ℝ} (hQ : HasOrthonormalCols Q) (R : Matrix m n ℝ) :
    specNorm (residual Q R) ≤ specNorm R := specNorm_sub_mul_transpose_mul_le hQ R

private theorem frobNorm_residual_le {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq k] {Q : Matrix m k ℝ} (hQ : HasOrthonormalCols Q) (R : Matrix m n ℝ) :
    frobNorm (residual Q R) ≤ frobNorm R := Real.sqrt_le_sqrt (frobSq_residual_le hQ R)

/-- Wedin's exact maximum-residual operator bound for the leading left and
right singular spaces of actual SVDs. Wedin (1972), Section 3. The denominator
is `σ_(k-1)(A+E)-σ_k(A)`; the endpoint `k=min(m,n)` uses the actual zero-padded
next value. Empty selected frames are included whenever the displayed gap is positive.
atlas: wedin-sin-theta (partial) -/
theorem max_specNorm_sinePrincipalAngles_le_max_residual_div
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n)
    (hδ : 0 < singularValues (A + E) (k - 1) - singularValues A k) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    let T := Matrix.diagonal (fun i : Fin k => singularValues (A + E) i)
    max (specNorm (sinePrincipalAngles U₁ Uhat₁)) (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤
      max (specNorm (A * Vhat₁ - Uhat₁ * T)) (specNorm (Aᵀ * Uhat₁ - Vhat₁ * T)) /
        (singularValues (A + E) (k - 1) - singularValues A k) := by
  dsimp only
  let U₁ := headColumns U (hk.trans (min_le_left m n))
  let V₁ := headColumns V (hk.trans (min_le_right m n))
  let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
  let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
  let t : Fin k → ℝ := fun i => singularValues (A + E) i
  have hU : HasOrthonormalCols U₁ := hasOrthonormalCols_headColumns hA.transpose_mul_left _
  have hV : HasOrthonormalCols V₁ := hasOrthonormalCols_headColumns hA.transpose_mul_right _
  have hUh : HasOrthonormalCols Uhat₁ := hasOrthonormalCols_headColumns hhat.transpose_mul_left _
  have hVh : HasOrthonormalCols Vhat₁ := hasOrthonormalCols_headColumns hhat.transpose_mul_right _
  have ht : ∀ i : Fin k, singularValues (A + E) (k - 1) ≤ t i := by
    intro i
    exact singularValues_antitone (A + E) (by have hi := i.isLt; omega)
  have hh := sub_mul_max_specNorm_le_max_coupled_residual
    (singularValues_nonneg (A + E) (k - 1)) ht
    (hA.specNorm_sub_truncatedMatrix k).le (residual U₁ Uhat₁) (residual V₁ Vhat₁)
  rw [hA.coupled_residual_headColumns_left, hA.coupled_residual_headColumns_right] at hh
  have hcontr := max_le_max (specNorm_residual_le hU (A * Vhat₁ - Uhat₁ * Matrix.diagonal t))
    (specNorm_residual_le hV (Aᵀ * Uhat₁ - Vhat₁ * Matrix.diagonal t))
  have hb := hh.trans hcontr
  rw [← specNorm_sinePrincipalAngles_eq_residual hU hUh,
    ← specNorm_sinePrincipalAngles_eq_residual hV hVh] at hb
  apply (le_div_iff₀ hδ).2
  simpa only [mul_comm] using hb

/-- Wedin's exact paired Frobenius residual bound for actual leading singular
frames. Wedin (1972), Section 3; the two residuals are combined by their Euclidean
norm with constant one and rectangular zero directions are included.
atlas: wedin-sin-theta (partial) -/
theorem sqrt_add_sq_frobNorm_sinePrincipalAngles_le_sqrt_add_sq_residual_div
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n)
    (hδ : 0 < singularValues (A + E) (k - 1) - singularValues A k) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    let T := Matrix.diagonal (fun i : Fin k => singularValues (A + E) i)
    Real.sqrt (frobNorm (sinePrincipalAngles U₁ Uhat₁) ^ 2 +
      frobNorm (sinePrincipalAngles V₁ Vhat₁) ^ 2) ≤
      Real.sqrt (frobNorm (A * Vhat₁ - Uhat₁ * T) ^ 2 +
        frobNorm (Aᵀ * Uhat₁ - Vhat₁ * T) ^ 2) /
          (singularValues (A + E) (k - 1) - singularValues A k) := by
  dsimp only
  let U₁ := headColumns U (hk.trans (min_le_left m n))
  let V₁ := headColumns V (hk.trans (min_le_right m n))
  let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
  let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
  let t : Fin k → ℝ := fun i => singularValues (A + E) i
  have hU : HasOrthonormalCols U₁ := hasOrthonormalCols_headColumns hA.transpose_mul_left _
  have hV : HasOrthonormalCols V₁ := hasOrthonormalCols_headColumns hA.transpose_mul_right _
  have hUh : HasOrthonormalCols Uhat₁ := hasOrthonormalCols_headColumns hhat.transpose_mul_left _
  have hVh : HasOrthonormalCols Vhat₁ := hasOrthonormalCols_headColumns hhat.transpose_mul_right _
  have ht : ∀ i : Fin k, singularValues (A + E) (k - 1) ≤ t i := by
    intro i
    exact singularValues_antitone (A + E) (by have hi := i.isLt; omega)
  have hh := sub_sq_mul_add_sq_frobNorm_le_add_sq_coupled_residual
    (singularValues_nonneg (A + E) (k - 1)) ht (hA.specNorm_sub_truncatedMatrix k).le hδ.le
    (residual U₁ Uhat₁) (residual V₁ Vhat₁)
  rw [hA.coupled_residual_headColumns_left, hA.coupled_residual_headColumns_right] at hh
  have hF := pow_le_pow_left₀ (frobNorm_nonneg _)
    (frobNorm_residual_le hU (A * Vhat₁ - Uhat₁ * Matrix.diagonal t)) 2
  have hG := pow_le_pow_left₀ (frobNorm_nonneg _)
    (frobNorm_residual_le hV (Aᵀ * Uhat₁ - Vhat₁ * Matrix.diagonal t)) 2
  have hb := hh.trans (add_le_add hF hG)
  rw [← frobNorm_sinePrincipalAngles_eq_residual hU hUh,
    ← frobNorm_sinePrincipalAngles_eq_residual hV hVh] at hb
  apply (le_div_iff₀ hδ).2
  apply le_of_pow_le_pow_left₀ two_ne_zero (Real.sqrt_nonneg _)
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith [hb]

end NLAlib
