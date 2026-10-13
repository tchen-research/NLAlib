import NLAlib.Matrix.Subspaces.ObliqueFrameInverse
import NLAlib.Matrix.Subspaces.PrincipalAngleDefinitions
/-!
# The oblique projection norm is the principal-angle secant

At positive rank the largest principal angle between the range and the
orthogonal complement of the kernel is strictly below pi/2, and its cosine
is the reciprocal projection norm. Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- For any range and row-space orthonormal frames of a positive-rank
idempotent, the largest principal angle is strictly below pi/2 and its
secant equals the spectral norm. Horn–Johnson 2013, Corollary 3.4.3.3;
the positive frame cardinality is essential.
atlas: cs-decomposition (partial) -/
theorem specNorm_idempotent_eq_secant_of_range_frames {n r : Type*}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    {P : Matrix n n ℝ} (hP : IsIdempotentElem P)
    {Q W : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (hW : HasOrthonormalCols W)
    (hRange : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin)
    (hRow : LinearMap.range W.mulVecLin = LinearMap.range Pᵀ.mulVecLin)
    (hr : 0 < Fintype.card r) :
    let θ := principalAnglesFintype W Q ⟨Fintype.card r - 1, by omega⟩
    θ < Real.pi / 2 ∧ specNorm P = 1 / Real.cos θ := by
  obtain ⟨hC, hForm⟩ := isUnit_overlap_and_eq_mul_inv_mul_of_idempotent hP hQ hW hRange hRow
  have hRank : (Wᵀ * Q).rank = Fintype.card r := Matrix.rank_of_isUnit _ hC
  have hpos : 0 < singularValues ((Wᵀ * Q).reindex (Fintype.equivFin r)
      (Fintype.equivFin r)) (Fintype.card r - 1) := by
    apply (singularValues_pos_iff _ _).mpr
    rw [Matrix.rank_reindex, hRank]
    omega
  refine ⟨?_, ?_⟩
  · simpa only [principalAnglesFintype, singularValues_reindex,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Real.arccos_lt_pi_div_two.mpr hpos
  · rw [hForm, specNorm_mul_transpose_right_of_hasOrthonormalCols (show Wᵀ * W = 1 from hW),
      specNorm_mul_left_of_hasOrthonormalCols (show Qᵀ * Q = 1 from hQ),
      specNorm_inv_eq_inv_singularValues_last _ hC hr,
      cos_principalAngles hW hQ, singularValues_reindex,
      Matrix.conjTranspose_eq_transpose_of_trivial, singularValues_eq_linearMap]

/-- Every positive-rank real idempotent has orthonormal frames for its
actual range and the orthogonal complement of its actual kernel whose
largest principal angle has secant equal to its spectral norm. The angle
is strictly below pi/2, and monotonicity identifies it as the largest one.
This includes the identity at positive dimension. Horn–Johnson 2013,
Corollary 3.4.3.3; derivations §alg:cs.
atlas: cs-decomposition (partial) -/
theorem exists_range_kernel_frames_specNorm_eq_secant {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (hP : IsIdempotentElem P)
    (hr : 0 < P.rank) :
    ∃ Q W : Matrix n (Fin P.rank) ℝ,
      HasOrthonormalCols Q ∧ HasOrthonormalCols W ∧
      LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin ∧
      LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ ∧
      let θ := principalAnglesFintype W Q ⟨P.rank - 1, by simpa using Nat.sub_lt hr Nat.one_pos⟩
      (∀ i, principalAnglesFintype W Q i ≤ θ) ∧
      θ < Real.pi / 2 ∧ specNorm P = 1 / Real.cos θ := by
  let Q : Matrix n (Fin P.rank) ℝ := orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hQ : HasOrthonormalCols Q := hasOrthonormalCols_orthonormalBasisMatrix _
  have hRange : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin :=
    range_orthonormalBasisMatrix _
  have hWexists : ∃ W : Matrix n (Fin P.rank) ℝ, HasOrthonormalCols W ∧
      LinearMap.range W.mulVecLin = LinearMap.range Pᵀ.mulVecLin := by
    have hEx : ∃ W : Matrix n (Fin Pᵀ.rank) ℝ, HasOrthonormalCols W ∧
        LinearMap.range W.mulVecLin = LinearMap.range Pᵀ.mulVecLin :=
        ⟨orthonormalBasisMatrix (LinearMap.range Pᵀ.mulVecLin),
          hasOrthonormalCols_orthonormalBasisMatrix _, range_orthonormalBasisMatrix _⟩
    convert hEx using 1
    rw [Matrix.rank_transpose]
  obtain ⟨W, hW, hRow⟩ := hWexists
  have hAdj : Pᵀ.toEuclideanLin = LinearMap.adjoint P.toEuclideanLin := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint P
  refine ⟨Q, W, hQ, hW, range_toEuclideanLin_eq_of_range_mulVecLin_eq Q P hRange, ?_, ?_⟩
  · rw [range_toEuclideanLin_eq_of_range_mulVecLin_eq W Pᵀ hRow, hAdj,
      LinearMap.orthogonal_ker]
  · refine ⟨?_, ?_⟩
    · intro i
      apply principalAngles_monotone W Q
      change (i : ℕ) ≤ P.rank - 1
      have hi := i.isLt
      simp only [Fintype.card_fin] at hi
      omega
    · have hWidth : 0 < Fintype.card (Fin P.rank) := by simpa only [Fintype.card_fin] using hr
      have hSec := specNorm_idempotent_eq_secant_of_range_frames
        (n := n) (r := Fin P.rank) (P := P) (Q := Q) (W := W)
        hP hQ hW hRange hRow hWidth
      dsimp only at hSec
      simpa only [Fintype.card_fin] using hSec

end NLAlib
