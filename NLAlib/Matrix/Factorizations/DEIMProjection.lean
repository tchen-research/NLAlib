import NLAlib.Matrix.Factorizations.DEIMGreedy
import NLAlib.Matrix.Subspaces.ObliqueProjectionNorms
import NLAlib.Matrix.Subspaces.ComplexObliqueSpectrum
import NLAlib.Matrix.Subspaces.CoordinateFrames
/-!
# DEIM interpolation projectors and their exact amplification factor

Coordinate selection is an orthonormal frame. DEIM's oblique projector
therefore has norm exactly the norm of the inverse sampled basis. A proper
nonzero projector and its complement have equal norms. The full-rank
endpoint is the identity and has zero error.

Source: Brunton–Kutz (2022), §13.4; matrix-toolkit re-derivation, §66.
Atlas: `deim-greedy-interpolation`.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*}
variable [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- The DEIM interpolation operator `U (PᴴU)⁻¹ Pᴴ`. -/
def deimProjector (U : Matrix n r 𝕜) (indices : r → n) : Matrix n n 𝕜 :=
  U * ((coordinateFrame indices)ᴴ * U)⁻¹ * (coordinateFrame indices)ᴴ

/-- DEIM reproduces its basis and the selected coordinates, and is an
idempotent. Combined with the greedy realization in `DEIMGreedy`, the
nonsingularity hypothesis holds for the computed indices.
atlas: deim-greedy-interpolation (partial) -/
theorem deimProjector_properties (U : Matrix n r 𝕜) (indices : r → n)
    (hM : IsUnit (U.submatrix indices id)) :
    deimProjector U indices * U = U ∧
      (coordinateFrame indices)ᴴ * deimProjector U indices = (coordinateFrame indices)ᴴ ∧
      IsIdempotentElem (deimProjector U indices) := by
  have hPU : IsUnit ((coordinateFrame indices)ᴴ * U) :=
    (coordinateFrame_conjTranspose_mul indices U).symm ▸ hM
  have hl := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hPU)
  have hr := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hPU)
  have hfix : deimProjector U indices * U = U := by
    rw [deimProjector, Matrix.mul_assoc, Matrix.mul_assoc, hl, Matrix.mul_one]
  refine ⟨hfix, ?_, ?_⟩
  · rw [deimProjector, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hr, Matrix.one_mul]
  · change deimProjector U indices * deimProjector U indices = deimProjector U indices
    conv_lhs => arg 2; rw [deimProjector]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix]
    rfl

/-- The exact DEIM projector norm is the inverse sampled-basis norm. -/
theorem specNorm_deimProjector (U : Matrix n r 𝕜) (hU : HasOrthonormalCols U)
    (indices : r → n) (hi : Function.Injective indices) :
    specNorm (deimProjector U indices) = specNorm ((U.submatrix indices id)⁻¹) := by
  rw [deimProjector,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols
      (hasOrthonormalCols_coordinateFrame hi),
    specNorm_mul_left_of_hasOrthonormalCols hU, coordinateFrame_conjTranspose_mul]

/-- The DEIM projector has the dimension of its reproduced subspace. -/
theorem rank_deimProjector (U : Matrix n r 𝕜) (hU : HasOrthonormalCols U)
    (indices : r → n) (hM : IsUnit (U.submatrix indices id)) :
    (deimProjector U indices).rank = Fintype.card r := by
  have hrank : U.rank = Fintype.card r := by
    have he := rank_isometry_mul_eq hU (1 : Matrix r r 𝕜)
    simpa using he
  apply le_antisymm
  · rw [deimProjector]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans U.rank_le_card_width)
  · calc
      _ = U.rank := hrank.symm
      _ = (deimProjector U indices * U).rank :=
        congrArg Matrix.rank (deimProjector_properties U indices hM).1.symm
      _ ≤ _ := Matrix.rank_mul_le_left _ _

/-- At the full-state endpoint DEIM is exactly the identity. -/
theorem deimProjector_eq_one_of_card_eq (U : Matrix n r 𝕜) (hU : HasOrthonormalCols U)
    (indices : r → n) (hM : IsUnit (U.submatrix indices id))
    (hr : Fintype.card r = Fintype.card n) : deimProjector U indices = 1 := by
  have hP := (deimProjector_properties U indices hM).2.2
  have hrank := rank_deimProjector U hU indices hM
  have htop : LinearMap.range (deimProjector U indices).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank, hr] using hrank
  have hunit : IsUnit (deimProjector U indices) :=
    Matrix.mulVec_surjective_iff_isUnit.mp (LinearMap.range_eq_top.mp htop)
  have hi := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have he := congrArg (fun M => (deimProjector U indices)⁻¹ * M) hP.eq
  simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul] using he

/-- The interpolation residual factors through the orthogonal projection
residual; this identity underlies the sharp DEIM error estimate. -/
theorem one_sub_deimProjector_mul_one_sub_projector (U : Matrix n r 𝕜) (indices : r → n)
    (hM : IsUnit (U.submatrix indices id)) :
    (1 - deimProjector U indices) * (1 - U * Uᴴ) = 1 - deimProjector U indices := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, (deimProjector_properties U indices hM).1]
  abel

/-- Generic residual bound in terms of the complementary projector norm. -/
theorem norm_sub_deimProjector_mulVec_le (U : Matrix n r 𝕜) (indices : r → n)
    (hM : IsUnit (U.submatrix indices id)) (f : n → 𝕜) :
    ‖WithLp.toLp 2 (f - deimProjector U indices *ᵥ f)‖ ≤
      specNorm (1 - deimProjector U indices) *
        ‖WithLp.toLp 2 ((1 - U * Uᴴ) *ᵥ f)‖ := by
  have he : f - deimProjector U indices *ᵥ f =
      (1 - deimProjector U indices) *ᵥ ((1 - U * Uᴴ) *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, one_sub_deimProjector_mul_one_sub_projector U indices hM,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [he]
  open scoped Matrix.Norms.L2Operator in
    exact (1 - deimProjector U indices).l2_opNorm_mulVec
      (WithLp.toLp 2 ((1 - U * Uᴴ) *ᵥ f))

/-- Sharp proper-subspace DEIM norm and error formulas over the reals.
atlas: deim-greedy-interpolation (partial) -/
theorem real_deimProjector_norm_and_error (U : Matrix n r ℝ) (hU : HasOrthonormalCols U)
    (indices : r → n) (hi : Function.Injective indices) (hM : IsUnit (U.submatrix indices id))
    (hr : 0 < Fintype.card r) (hn : Fintype.card r < Fintype.card n) :
    specNorm (1 - deimProjector U indices) = specNorm ((U.submatrix indices id)⁻¹) ∧
      ∀ f : n → ℝ, ‖WithLp.toLp 2 (f - deimProjector U indices *ᵥ f)‖ ≤
        specNorm ((U.submatrix indices id)⁻¹) * ‖WithLp.toLp 2 ((1 - U * Uᴴ) *ᵥ f)‖ := by
  have hcomp := specNorm_one_sub_eq_of_idempotent_of_rank_pos_lt
    (deimProjector_properties U indices hM).2.2
    (by rwa [rank_deimProjector U hU indices hM])
    (by rwa [rank_deimProjector U hU indices hM])
  rw [specNorm_deimProjector U hU indices hi] at hcomp
  exact ⟨hcomp, fun f => hcomp ▸ norm_sub_deimProjector_mulVec_le U indices hM f⟩

/-- Sharp proper-subspace DEIM norm and error formulas over the complexes.
atlas: deim-greedy-interpolation (partial) -/
theorem complex_deimProjector_norm_and_error (U : Matrix n r ℂ) (hU : HasOrthonormalCols U)
    (indices : r → n) (hi : Function.Injective indices) (hM : IsUnit (U.submatrix indices id))
    (hr : 0 < Fintype.card r) (hn : Fintype.card r < Fintype.card n) :
    specNorm (1 - deimProjector U indices) = specNorm ((U.submatrix indices id)⁻¹) ∧
      ∀ f : n → ℂ, ‖WithLp.toLp 2 (f - deimProjector U indices *ᵥ f)‖ ≤
        specNorm ((U.submatrix indices id)⁻¹) * ‖WithLp.toLp 2 ((1 - U * Uᴴ) *ᵥ f)‖ := by
  open scoped Matrix.Norms.L2Operator in
    have hcomp := (complex_idempotent_complement_norm_properties
      (deimProjector U indices) (deimProjector_properties U indices hM).2.2).1
      (by rwa [rank_deimProjector U hU indices hM])
      (by rwa [rank_deimProjector U hU indices hM])
    change specNorm (1 - deimProjector U indices) = specNorm (deimProjector U indices) at hcomp
    rw [specNorm_deimProjector U hU indices hi] at hcomp
    exact ⟨hcomp, fun f => hcomp ▸ norm_sub_deimProjector_mulVec_le U indices hM f⟩

/-- At zero retained dimension the DEIM projector is exactly zero. The
empty sample inverse does not give the proper-subspace norm formula.
atlas: deim-greedy-interpolation (partial) -/
theorem deimProjector_eq_zero_of_isEmpty [IsEmpty r] (U : Matrix n r 𝕜) (indices : r → n) :
    deimProjector U indices = 0 := by
  ext i j
  simp [deimProjector, Matrix.mul_apply]

/-- The correct zero-dimensional endpoint of the DEIM error estimate.
atlas: deim-greedy-interpolation (partial) -/
theorem deim_empty_error [IsEmpty r] (U : Matrix n r 𝕜) (indices : r → n) (f : n → 𝕜) :
    ‖WithLp.toLp 2 (f - deimProjector U indices *ᵥ f)‖ ≤ ‖WithLp.toLp 2 f‖ := by
  rw [deimProjector_eq_zero_of_isEmpty, Matrix.zero_mulVec, sub_zero]

end NLAlib
