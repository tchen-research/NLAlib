import NLAlib.Matrix.Basic.GramSchurDiagonal
import NLAlib.Matrix.Functions.GeometricMean
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Probability.Gaussian.Moments.ComplexInverseSquare
import NLAlib.Probability.Gaussian.Basic.ComplexConjugation

/-!
# Exact complex Gaussian row-residual inverse moment

Whitening the fixed row Gram matrix produces an orthonormal row-space frame.
Its unitary complement turns the actual Gaussian residual into a squared
complex Gaussian norm of dimension `k-n`. The inverse moment therefore has
the complex denominator `2(k-n-1)` in the circular convention.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- A fixed full-row-rank complex matrix has an orthonormal complementary
frame representing its exact squared residual. -/
theorem exists_orthonormal_complement_gramRowResidual {n k : ℕ}
    (H : Matrix (Fin n) (Fin k) ℂ) (hH : IsUnit (H*Hᴴ)) :
    ∃ V : Matrix (Fin k) (Fin (k-n)) ℂ, HasOrthonormalCols V ∧
      ∀ g, gramRowResidual H g = ((∑ j, Complex.normSq ((Vᴴ*ᵥg) j) : ℝ) : ℂ) := by
  let M := H*Hᴴ
  have hM : M.PosDef := (Matrix.posSemidef_self_mul_conjTranspose H).posDef_iff_isUnit.mpr hH
  let S := cfc Real.sqrt M
  let W := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) M
  have hW : W.IsHermitian := cfc_predicate _ _
  have hSW : S*W=1 := cfc_sqrt_mul_inv_sqrt hM
  have hSS : S*S=M := cfc_sqrt_mul_self hM
  have hWhite : W*M*W=1 := cfc_inv_sqrt_mul_self_mul_inv_sqrt hM
  have hMWW : M*(W*W)=1 := by
    calc
      _ = S*(S*W)*W := by rw [← hSS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSW, Matrix.mul_one, hSW]
  have hW2 : W*W=M⁻¹ := (Matrix.inv_eq_right_inv hMWW).symm
  let Q := Hᴴ*W
  have hQ : HasOrthonormalCols Q := by
    change (Hᴴ*W)ᴴ*(Hᴴ*W)=1
    rw [Matrix.conjTranspose_mul, hW.eq, Matrix.conjTranspose_conjTranspose]
    simpa only [M, Matrix.mul_assoc] using hWhite
  have hproj : Q*Qᴴ=Hᴴ*M⁻¹*H := by
    change (Hᴴ*W)*(Hᴴ*W)ᴴ=Hᴴ*M⁻¹*H
    rw [Matrix.conjTranspose_mul, hW.eq, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Hᴴ*(W*W)*H := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW2]
  have hc : ∃ V : Matrix (Fin k) (Fin (k-n)) ℂ,
      HasOrthonormalCols V ∧ Q*Qᴴ+V*Vᴴ=1 := by
    have hcard : Fintype.card (Fin k)-Fintype.card (Fin n)=k-n := by simp only [Fintype.card_fin]
    rw [← hcard]
    exact exists_unitary_complement Q hQ
  obtain ⟨V,hV,hcomp⟩ := hc
  have hVV : 1-Hᴴ*M⁻¹*H=V*Vᴴ := by rw [← hproj, ← hcomp]; abel
  refine ⟨V,hV,fun g => ?_⟩
  have hcross : star g ⬝ᵥ ((Hᴴ*M⁻¹*H)*ᵥg)=star (H*ᵥg) ⬝ᵥ (M⁻¹*ᵥ(H*ᵥg)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star g) Hᴴ, Matrix.vecMul_conjTranspose, star_star]
  have hr : gramRowResidual H g=quadForm (1-Hᴴ*M⁻¹*H) g := by
    rw [quadForm, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hcross]
    rfl
  rw [hr,hVV]
  have hq := quadForm_conjTranspose_mul_self Vᴴ g
  rw [Matrix.conjTranspose_conjTranspose] at hq
  rw [hq, dotProduct]
  simp only [Pi.star_apply, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]

/-- The exact inverse squared row-residual moment under the actual complex
Gaussian vector law. No residual-distribution hypothesis is assumed. -/
theorem integrable_and_integral_inv_re_gramRowResidual_circularComplexGaussianVector
    {n k : ℕ} (hnk : n+2 ≤ k) (H : Matrix (Fin n) (Fin k) ℂ)
    (hH : IsUnit (H*Hᴴ)) :
    Integrable (fun g => ((gramRowResidual H g).re)⁻¹) (circularComplexGaussianVector (Fin k)) ∧
      ∫ g, ((gramRowResidual H g).re)⁻¹ ∂circularComplexGaussianVector (Fin k) =
        1/(2*((k:ℝ)-n-1)) := by
  obtain ⟨V,hV,hr⟩ := exists_orthonormal_complement_gramRowResidual H hH
  have hv : HasOrthonormalCols Vᴴᴴ := by rwa [Matrix.conjTranspose_conjTranspose]
  have hd : 2 ≤ Fintype.card (Fin (k-n)) := by simp only [Fintype.card_fin]; omega
  obtain ⟨hi,he⟩ := integrable_and_integral_inv_sum_normSq_mulVec_circularComplexGaussianVector Vᴴ hv hd
  have hfun : (fun g => ((gramRowResidual H g).re)⁻¹) =
      fun g => (∑ j, Complex.normSq ((Vᴴ*ᵥg) j))⁻¹ := by
    funext g
    rw [hr, Complex.ofReal_re]
  rw [hfun]
  refine ⟨hi,he.trans ?_⟩
  simp only [Fintype.card_fin, Nat.cast_sub (by omega : n≤k)]
  congr 1
  ring

/-- A full-rank row residual is real, including zero residuals. -/
theorem gramRowResidual_ofReal_re {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℂ)
    (hH : IsUnit (H*Hᴴ)) (g : Fin k → ℂ) :
    ((gramRowResidual H g).re : ℂ)=gramRowResidual H g := by
  obtain ⟨V,hV,hr⟩ := exists_orthonormal_complement_gramRowResidual H hH
  rw [hr,Complex.ofReal_re]

/-- The same native inverse-residual moment applies to a conjugated Gaussian
row, as needed by the Hermitian Schur-complement identity. -/
theorem integrable_and_integral_inv_re_gramRowResidual_star_circularComplexGaussianVector
    {n k : ℕ} (hnk : n+2 ≤ k) (H : Matrix (Fin n) (Fin k) ℂ)
    (hH : IsUnit (H*Hᴴ)) :
    Integrable (fun g => ((gramRowResidual H (star g)).re)⁻¹) (circularComplexGaussianVector (Fin k)) ∧
      ∫ g, ((gramRowResidual H (star g)).re)⁻¹ ∂circularComplexGaussianVector (Fin k) =
        1/(2*((k:ℝ)-n-1)) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_inv_re_gramRowResidual_circularComplexGaussianVector hnk H hH
  have hm : AEStronglyMeasurable (fun g : Fin k → ℂ => ((gramRowResidual H g).re)⁻¹)
      (circularComplexGaussianVector (Fin k)) :=
    (by unfold gramRowResidual; fun_prop : Measurable _).aestronglyMeasurable
  have hs := hasLaw_star_circularComplexGaussianVector (n := Fin k)
  constructor
  · rw [← hs.map_eq] at hi
    exact hi.comp_aemeasurable hs.aemeasurable
  · exact (hs.integral_comp hm).trans hv

end NLAlib
