import NLAlib.Matrix.Subspaces.ObliqueProjectionBlocks
import NLAlib.Matrix.Perturbation.Conditioning
/-!
# Oblique projection as the inverse frame overlap

Range and row-space orthonormal frames of an idempotent have an invertible
overlap. The projection is the frame lift of its inverse.
Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Equality of column ranges is unchanged by passing from coordinate vectors
to Euclidean vectors. Horn–Johnson 2013, Section 2.1; range-frame helper. -/
theorem range_toEuclideanLin_eq_of_range_mulVecLin_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℝ) (B : Matrix m p ℝ)
    (h : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    LinearMap.range A.toEuclideanLin = LinearMap.range B.toEuclideanLin := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := h.le (show A *ᵥ v.ofLp ∈ LinearMap.range A.mulVecLin from ⟨v.ofLp, rfl⟩)
    exact ⟨WithLp.toLp 2 w, congrArg (WithLp.toLp 2) hw⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := h.ge (show B *ᵥ v.ofLp ∈ LinearMap.range B.mulVecLin from ⟨v.ofLp, rfl⟩)
    exact ⟨WithLp.toLp 2 w, congrArg (WithLp.toLp 2) hw⟩

/-- Range and row-space orthonormal frames of an idempotent have an
invertible overlap and reconstruct the projection with its inverse. No
positive-rank premise is needed for this algebraic statement.
Horn–Johnson 2013, Corollary 3.4.3.3; supports `cs-decomposition`. -/
theorem isUnit_overlap_and_eq_mul_inv_mul_of_idempotent {n r : Type*}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    {P : Matrix n n ℝ} (hP : IsIdempotentElem P)
    {Q W : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (hW : HasOrthonormalCols W)
    (hRange : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin)
    (hRow : LinearMap.range W.mulVecLin = LinearMap.range Pᵀ.mulVecLin) :
    IsUnit (Wᵀ * Q) ∧ P = Q * (Wᵀ * Q)⁻¹ * Wᵀ := by
  let G := Qᵀ * P * W
  let C := Wᵀ * Q
  have hPQ : P * Q = Q := mul_eq_of_range_le_of_isIdempotentElem hP hRange.le
  have hQproj : Q * (Qᵀ * P) = P := mul_transpose_mul_eq_of_range_le hQ hRange.ge
  have hWproj : P * W * Wᵀ = P := by
    have hh := congrArg Matrix.transpose (mul_transpose_mul_eq_of_range_le hW hRow.ge)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose] using hh
  have hGC : G * C = 1 := by
    calc
      _ = Qᵀ * (P * W * Wᵀ) * Q := by simp only [G, C, Matrix.mul_assoc]
      _ = Qᵀ * Q := by rw [hWproj, Matrix.mul_assoc, hPQ]
      _ = 1 := hQ
  have hCG : C * G = 1 := mul_eq_one_comm.mp hGC
  have hC : IsUnit C := ⟨⟨C, G, hCG, hGC⟩, rfl⟩
  refine ⟨hC, ?_⟩
  rw [Matrix.inv_eq_left_inv hGC]
  change P = Q * (Qᵀ * P * W) * Wᵀ
  rw [← Matrix.mul_assoc Q (Qᵀ * P) W, hQproj, hWproj]

/-- The operator norm of a nonempty square inverse is the reciprocal of its
least actual singular value. Horn–Johnson 2013, Section 5.6; empty domains
are excluded exactly because they have no last singular value. -/
theorem specNorm_inv_eq_inv_singularValues_last {r : Type*}
    [Fintype r] [DecidableEq r] (C : Matrix r r ℝ) (hC : IsUnit C)
    (hr : 0 < Fintype.card r) :
    specNorm C⁻¹ = 1 / singularValues C (Fintype.card r - 1) := by
  have hRank : C.rank = Fintype.card r := Matrix.rank_of_isUnit C hC
  rw [← moorePenroseInverse_eq_inv_of_isUnit _ hC, specNorm_moorePenroseInverse_eq_fintype,
    hRank, if_neg (Nat.ne_of_gt hr), singularValues_reindex,
    singularValues_eq_linearMap]

end NLAlib
