import NLAlib.Matrix.Subspaces.PrincipalAngleInvariance
import NLAlib.Matrix.Subspaces.PrincipalAngleTangent
/-!
# Complete principal-angle toolkit

Actual arccos angles, ordered cosines, sine residual/complement/projector
characterizations, Frobenius identities, range invariance and symmetry,
largest-angle formula, and the exact tangent inverse formula.
Source: Stewart–Sun §I.5; Golub–Van Loan §2.5.3.
Atlas: `principal-angles-def`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- Complete principal-angle characterizations for equal-width real
orthonormal frames and an orthonormal complement. Stewart–Sun §I.5,
Golub–Van Loan §2.5.3. The angle and sine/tangent matrices use the actual
singular-value list. Empty frames are explicit; a last angle is mentioned
only at positive width, and the inverse formula requires the overlap to be
invertible, derived also from the last-angle condition.
atlas: principal-angles-def -/
theorem principal_angle_characterizations {P Q : Matrix m n ℝ} {R : Matrix m r ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hR : HasOrthonormalCols R)
    (hcomp : P*Pᵀ+R*Rᵀ=1) :
    (Monotone (principalAnglesFintype P Q)) ∧
    (∀ i, principalAnglesFintype P Q i ∈ Set.Icc (0 : ℝ) (Real.pi/2) ∧
      Real.cos (principalAnglesFintype P Q i)=singularValues
        ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i) ∧
    (specNorm (sinePrincipalAngles P Q)=specNorm (Rᵀ*Q)) ∧
    (specNorm (sinePrincipalAngles P Q)=specNorm (projResidual P Q)) ∧
    (specNorm (sinePrincipalAngles P Q)=specNorm (P*Pᵀ-Q*Qᵀ)) ∧
    (frobSq (sinePrincipalAngles P Q)=(Fintype.card n : ℝ)-frobSq (Pᵀ*Q)) ∧
    (frobSq (P*Pᵀ-Q*Qᵀ)=2*frobSq (sinePrincipalAngles P Q)) ∧
    (frobNorm (sinePrincipalAngles P Q)=frobNorm (Rᵀ*Q)) ∧
    (principalAnglesFintype P Q=principalAnglesFintype Q P) ∧
    (∀ P' Q' : Matrix m n ℝ, HasOrthonormalCols P' → HasOrthonormalCols Q' →
      LinearMap.range P.mulVecLin=LinearMap.range P'.mulVecLin →
      LinearMap.range Q.mulVecLin=LinearMap.range Q'.mulVecLin →
        principalAnglesFintype P Q=principalAnglesFintype P' Q') ∧
    (∀ hn : 0 < Fintype.card n, specNorm (sinePrincipalAngles P Q)=
      Real.sqrt (1-singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n))
        (Fintype.card n-1)^2)) ∧
    (IsUnit (Pᵀ*Q) → specNorm (tangentPrincipalAngles P Q)=specNorm ((Rᵀ*Q)*(Pᵀ*Q)⁻¹)) ∧
    (∀ hn : 0 < Fintype.card n,
      principalAnglesFintype P Q ⟨Fintype.card n-1, by omega⟩ < Real.pi/2 →
      specNorm (tangentPrincipalAngles P Q)=specNorm ((Rᵀ*Q)*(Pᵀ*Q)⁻¹)) ∧
    (Fintype.card n=0 → specNorm (sinePrincipalAngles P Q)=0 ∧
      frobNorm (sinePrincipalAngles P Q)=0 ∧ specNorm (tangentPrincipalAngles P Q)=0) := by
  refine ⟨principalAngles_monotone P Q, ?_,
    specNorm_sinePrincipalAngles_eq_complement_overlap hP hQ hR hcomp,
    specNorm_sinePrincipalAngles_eq_residual hP hQ,
    specNorm_sinePrincipalAngles_eq_projector_distance hP hQ,
    frobSq_sinePrincipalAngles_eq_card_sub_overlap hP hQ,
    frobSq_projector_distance_eq_two_mul_sinePrincipalAngles hP hQ,
    frobNorm_sinePrincipalAngles_eq_complement_overlap hP hQ hR hcomp,
    principalAngles_comm P Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨principalAngles_mem_Icc hP hQ i, cos_principalAngles hP hQ i⟩
  · intro P' Q' hP' hQ' hrP hrQ
    exact principalAngles_eq_of_range_eq hP hP' hQ hQ' hrP hrQ
  · intro hn
    exact specNorm_sinePrincipalAngles_eq_sqrt_one_sub_last_sq hP hQ hn
  · intro hC
    exact specNorm_tangentPrincipalAngles_eq_complement_overlap_mul_inv hP hQ hR hcomp hC
  · intro hn hang
    exact specNorm_tangentPrincipalAngles_eq_complement_overlap_mul_inv hP hQ hR hcomp
      (isUnit_overlap_of_principalAngles_last_lt_pi_div_two hn hang)
  · intro hn
    have hs : sinePrincipalAngles P Q=0 := by ext i j; have hi := i.isLt; omega
    have ht : tangentPrincipalAngles P Q=0 := by ext i j; have hi := i.isLt; omega
    simp [hs, ht, specNorm_zero]

end NLAlib
