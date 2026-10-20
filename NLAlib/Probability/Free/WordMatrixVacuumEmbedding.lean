import NLAlib.Probability.Free.WordMatrixVacuum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The actual amplified vacuum subspace

The genuine Euclidean coefficient vector embeds isometrically into the
native word Hilbert direct sum by tensoring each coordinate with the
existing vacuum. Actual native operator columns control every such vector
by the unnormalized genuine amplified vacuum Gram expectation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "K" => WordMatrixHilbertSpace D ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

/-- Tensoring a coefficient vector with the actual word vacuum is a native
linear isometry into the existing finite Hilbert direct sum. -/
def wordMatrixVacuumEmbedding : EuclideanSpace ℂ D →ₗᵢ[ℂ] K where
  toFun v := WithLp.toLp 2 (fun j => v j • wordVacuum ι)
  map_add' v w := by
    apply PiLp.ext
    intro j
    change (v j+w j)•wordVacuum ι=v j•wordVacuum ι+w j•wordVacuum ι
    exact add_smul _ _ _
  map_smul' z v := by
    apply PiLp.ext
    intro j
    change (z*v j)•wordVacuum ι=z•(v j•wordVacuum ι)
    exact mul_smul _ _ _
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    change ‖v j•wordVacuum ι‖^2=‖v j‖^2
    rw [norm_smul,norm_wordVacuum,mul_one]

omit [DecidableEq D] in
/-- Coordinates of the actual amplified vacuum embedding. -/
@[simp]
theorem wordMatrixVacuumEmbedding_apply (v : EuclideanSpace ℂ D) (j : D) :
    wordMatrixVacuumEmbedding (ι := ι) v j=v j•wordVacuum ι := rfl

/-- The actual native matrix vector functional of an embedded coefficient
vector, bundled with its genuine positivity. Normalization holds precisely
for coefficient vectors of unit norm. -/
def wordMatrixVacuumVectorPositiveMap (v : EuclideanSpace ℂ D) : M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun T := inner ℂ (wordMatrixVacuumEmbedding (ι := ι) v)
        (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) T
          (wordMatrixVacuumEmbedding (ι := ι) v))
      map_add' S T := by simp only [map_add,add_apply,inner_add_right]
      map_smul' z T := by
        simp only [map_smul,smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply] }
    (fun T hT => ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (map_nonneg (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)) hT)).inner_nonneg_right _)

/-- The native embedded vector map is a genuine normalized state at unit
coefficient vectors. -/
theorem wordMatrixVacuumVectorPositiveMap_one {v : EuclideanSpace ℂ D} (hv : ‖v‖=1) :
    wordMatrixVacuumVectorPositiveMap (ι := ι) v (1 : M)=1 := by
  change inner ℂ (wordMatrixVacuumEmbedding (ι := ι) v)
    (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) (1 : M)
      (wordMatrixVacuumEmbedding (ι := ι) v))=1
  rw [map_one,one_apply_eq_self,inner_self_eq_norm_sq_to_K,
    LinearIsometry.norm_map,hv]
  norm_num

/-- Every actual embedded vacuum vector is controlled by the actual sum of
native vacuum column energies. This is finite Cauchy--Schwarz, with no
faithfulness or traciality premise and with empty dimensions included. -/
theorem norm_toPiLp_wordMatrixVacuumEmbedding_sq_le (T : M) (v : EuclideanSpace ℂ D) :
    ‖CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) T
      (wordMatrixVacuumEmbedding (ι := ι) v)‖^2 ≤
      ‖v‖^2*(Fintype.card D : ℝ)*
        (wordMatrixVacuumExpectation (D := D) (ι := ι) (star T*T)).re := by
  cases isEmpty_or_nonempty D with
  | inl hD =>
    have hv : v=0 := by ext j; exact (hD.false j).elim
    simp only [hv,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_mul,le_refl]
  | inr hD =>
    let : Nonempty D := hD
    have hcard : (Fintype.card D : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have henergy : (Fintype.card D : ℝ)*
        (wordMatrixVacuumExpectation (D := D) (ι := ι) (star T*T)).re =
          ∑ j, ∑ i, ‖T i j (wordVacuum ι)‖^2 := by
      rw [wordMatrixVacuumExpectation_star_mul,Complex.ofReal_re,← mul_assoc,
        mul_inv_cancel₀ hcard,one_mul]
    rw [mul_assoc,henergy]
    rw [PiLp.norm_sq_eq_of_L2,EuclideanSpace.norm_sq_eq,Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [CStarMatrix.toPiLpStarAlgHom_apply]
    simp only [wordMatrixVacuumEmbedding_apply,map_smul]
    calc
      _ ≤ (∑ j, ‖v j‖*‖T i j (wordVacuum ι)‖)^2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [norm_smul] using norm_sum_le
          (Finset.univ : Finset D) (fun j => v j•T i j (wordVacuum ι))
      _ ≤ _ := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq
          (Finset.univ : Finset D) (fun j => ‖v j‖) (fun j => ‖T i j (wordVacuum ι)‖)

/-- On every positive native matrix, each actual amplified vacuum vector
state is bounded by the genuine sum of the native diagonal vacuum states.
This derives the dimension factor used for the high-height moment bound. -/
theorem re_inner_wordMatrixVacuumEmbedding_le_card_mul_expectation
    {T : M} (hT : 0≤T) (v : EuclideanSpace ℂ D) :
    (inner ℂ (wordMatrixVacuumEmbedding (ι := ι) v)
      (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) T
        (wordMatrixVacuumEmbedding (ι := ι) v))).re ≤
      ‖v‖^2*(Fintype.card D : ℝ)*
        (wordMatrixVacuumExpectation (D := D) (ι := ι) T).re := by
  let S := CFC.sqrt T
  let V := CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)
  have hSS : star S*S=T := by
    rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self T hT]
  have hcompose : (V S).adjoint.comp (V S)=V T := by
    change star (V S)*V S=V T
    rw [← map_star,← map_mul,hSS]
  have h := norm_toPiLp_wordMatrixVacuumEmbedding_sq_le S v
  rw [hSS] at h
  have heq : ‖V S (wordMatrixVacuumEmbedding (ι := ι) v)‖^2 =
      (inner ℂ (wordMatrixVacuumEmbedding (ι := ι) v)
        (V T (wordMatrixVacuumEmbedding (ι := ι) v))).re := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,hcompose]
    rfl
  rwa [heq] at h

end NLAlib

end
