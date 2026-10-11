import NLAlib.Matrix.Projections
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Largest tangent of a transverse graph

The largest tangent is the supremum of the tail norm under a unit head-coordinate
constraint. For a transverse graph `U₁ + U₂ F` it is exactly `specNorm F`.
This is the principal-angle tangent in manuscript `sa:subspace`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- The largest tangent from a subspace to the leading orthonormal block is the
largest tail-coordinate norm among vectors whose head-coordinate norm is at most one.
Source: Saad (2011), §5.1; manuscript `sa:subspace`. For transverse subspaces this is
the usual supremum of the tail/head norm ratio. -/
def subspaceTangent (U₁ : Matrix n k ℝ) (U₂ : Matrix n r ℝ)
    (S : Submodule ℝ (n → ℝ)) : ℝ :=
  sSup ((fun x : n → ℝ => ‖WithLp.toLp 2 (U₂ᵀ *ᵥ x)‖) ''
    {x | x ∈ S ∧ ‖WithLp.toLp 2 (U₁ᵀ *ᵥ x)‖ ≤ 1})

omit [DecidableEq n] in
/-- The principal-angle tangent of a transverse orthogonal graph is the norm of its
graph operator. Source: manuscript `sa:graph` and the following tangent identity;
Saad (2011), §5.1. The empty tail and empty head both have tangent zero. -/
theorem subspaceTangent_range_graph_eq_specNorm
    {U₁ : Matrix n k ℝ} {U₂ : Matrix n r ℝ}
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (F : Matrix r k ℝ) :
    subspaceTangent U₁ U₂ (LinearMap.range (U₁ + U₂ * F).mulVecLin) = specNorm F := by
  have hU' : U₂ᵀ * U₁ = 0 := transpose_mul_eq_zero_comm.1 hU
  have hhead : ∀ z : k → ℝ, U₁ᵀ *ᵥ ((U₁ + U₂ * F) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, Matrix.mul_add, ← Matrix.mul_assoc, hU₁, hU,
      Matrix.zero_mul, add_zero, Matrix.one_mulVec]
  have htail : ∀ z : k → ℝ, U₂ᵀ *ᵥ ((U₁ + U₂ * F) *ᵥ z) = F *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, Matrix.mul_add, ← Matrix.mul_assoc, hU', hU₂,
      Matrix.one_mul, zero_add]
  let f := (Matrix.toEuclideanLin (𝕜 := ℝ)).trans LinearMap.toContinuousLinearMap F
  have he : ((fun x : n → ℝ => ‖WithLp.toLp 2 (U₂ᵀ *ᵥ x)‖) ''
      {x | x ∈ LinearMap.range (U₁ + U₂ * F).mulVecLin ∧
        ‖WithLp.toLp 2 (U₁ᵀ *ᵥ x)‖ ≤ 1}) =
      ((fun z : EuclideanSpace ℝ k => ‖f z‖) '' Metric.closedBall 0 1) := by
    ext a
    constructor
    · rintro ⟨x, ⟨⟨z, rfl⟩, hz⟩, rfl⟩
      refine ⟨WithLp.toLp 2 z, ?_, ?_⟩
      · simpa only [Matrix.mulVecLin_apply, hhead, Metric.mem_closedBall,
          dist_zero_right] using hz
      · change ‖WithLp.toLp 2 (F *ᵥ z)‖ =
          ‖WithLp.toLp 2 (U₂ᵀ *ᵥ ((U₁ + U₂ * F) *ᵥ z))‖
        rw [htail]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(U₁ + U₂ * F) *ᵥ WithLp.ofLp z, ⟨⟨WithLp.ofLp z, rfl⟩, ?_⟩, ?_⟩
      · simpa only [hhead, WithLp.toLp_ofLp, Metric.mem_closedBall,
          dist_zero_right] using hz
      · change ‖WithLp.toLp 2 (U₂ᵀ *ᵥ ((U₁ + U₂ * F) *ᵥ WithLp.ofLp z))‖ =
          ‖WithLp.toLp 2 (F *ᵥ WithLp.ofLp z)‖
        rw [htail]
  rw [subspaceTangent, he, ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  rfl

/-- The tangent of the angle from a vector to an orthonormal frame's range is its
orthogonal-residual norm divided by its projection norm. Source: Saad (2011), §5.1;
manuscript `sa:subspace`, per-vector angle clause. -/
def vectorTangentToFrame {l : Type*} [Fintype l] (Q : Matrix n l ℝ) (u : n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (u - Q *ᵥ (Qᵀ *ᵥ u))‖ / ‖WithLp.toLp 2 (Qᵀ *ᵥ u)‖

omit [DecidableEq n] in
/-- Comparing a unit vector with any orthogonal graph competitor bounds its angle
to the containing frame. Source: manuscript `sa:subspace`, per-vector comparison.
This is an actual vector-to-subspace tangent, not the initial graph-column norm. -/
theorem vectorTangentToFrame_le_of_orthogonal_competitor
    {l : Type*} [Fintype l] [DecidableEq l] {Q : Matrix n l ℝ}
    (hQ : HasOrthonormalCols Q) {u w : n → ℝ} (hu : u ⬝ᵥ u = 1)
    (huw : u ⬝ᵥ w = 0) (hw : u + w ∈ LinearMap.range Q.mulVecLin) :
    vectorTangentToFrame Q u ≤ ‖WithLp.toLp 2 w‖ := by
  let p := Qᵀ *ᵥ u
  let v := Qᵀ *ᵥ (u + w)
  have hpv : p ⬝ᵥ v = 1 := by
    change (Qᵀ *ᵥ u) ⬝ᵥ (Qᵀ *ᵥ (u + w)) = 1
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      mulVec_transpose_mulVec_of_mem_range hQ hw, dotProduct_comm,
      dotProduct_add, hu, huw, add_zero]
  have hvv : v ⬝ᵥ v = 1 + w ⬝ᵥ w := by
    rw [transpose_mulVec_dotProduct_self_of_mem_range hQ hw]
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hu, huw, dotProduct_comm w u, huw]
    ring
  have hcs : 1 ≤ (p ⬝ᵥ p) * (1 + w ⬝ᵥ w) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p v
    have hc : (p ⬝ᵥ v) ^ 2 ≤ (p ⬝ᵥ p) * (v ⬝ᵥ v) := by
      simpa only [dotProduct, pow_two] using h
    simpa only [hpv, hvv, one_pow] using hc
  have hpp0 : 0 ≤ p ⬝ᵥ p := dotProduct_self_nonneg p
  have hpp : 0 < p ⬝ᵥ p := by
    by_contra h
    have hpzero : p ⬝ᵥ p = 0 := le_antisymm (not_lt.mp h) hpp0
    rw [hpzero, zero_mul] at hcs
    linarith
  have hcross : u ⬝ᵥ (Q *ᵥ p) = p ⬝ᵥ p := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hee : (u - Q *ᵥ p) ⬝ᵥ (u - Q *ᵥ p) = 1 - p ⬝ᵥ p := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hu, hcross,
      dotProduct_comm (Q *ᵥ p) u, hcross,
      mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ]
    ring
  have hnorm : ‖WithLp.toLp 2 p‖ ^ 2 = p ⬝ᵥ p := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, p i ^ 2) = p ⬝ᵥ p
    simp only [dotProduct, pow_two]
  have hnormpos : 0 < ‖WithLp.toLp 2 p‖ := by
    nlinarith [norm_nonneg (WithLp.toLp 2 p)]
  unfold vectorTangentToFrame
  change ‖WithLp.toLp 2 (u - Q *ᵥ p)‖ / ‖WithLp.toLp 2 p‖ ≤ ‖WithLp.toLp 2 w‖
  apply (div_le_iff₀ hnormpos).2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, hnorm, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hee' : (∑ i, (u - Q *ᵥ p) i ^ 2) = 1 - p ⬝ᵥ p := by
    simpa only [dotProduct, pow_two] using hee
  rw [hee']
  have hww : (∑ i, w i ^ 2) = w ⬝ᵥ w := by simp only [dotProduct, pow_two]
  rw [hww]
  nlinarith

omit [DecidableEq n] in
/-- Each leading graph column has angle to any containing orthonormal frame at most
its tail-column norm. Source: manuscript `sa:subspace`, the per-vector competitor. -/
theorem vectorTangentToFrame_graph_col_le
    {l : Type*} [Fintype l] [DecidableEq l] {Q : Matrix n l ℝ}
    (hQ : HasOrthonormalCols Q) {U₁ : Matrix n k ℝ} {U₂ : Matrix n r ℝ}
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (F : Matrix r k ℝ)
    (hRange : LinearMap.range (U₁ + U₂ * F).mulVecLin ≤ LinearMap.range Q.mulVecLin)
    (i : k) : vectorTangentToFrame Q (U₁.col i) ≤ ‖WithLp.toLp 2 (F.col i)‖ := by
  let e : k → ℝ := Pi.single i 1
  have he : U₁.col i = U₁ *ᵥ e := by simp [e]
  have hu : U₁.col i ⬝ᵥ U₁.col i = 1 := by
    rw [he, mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hU₁]
    simp [e]
  have horth : U₁.col i ⬝ᵥ (U₂ *ᵥ F.col i) = 0 := by
    have hU' : U₂ᵀ * U₁ = 0 := transpose_mul_eq_zero_comm.1 hU
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, he,
      Matrix.mulVec_mulVec, hU', Matrix.zero_mulVec, zero_dotProduct]
  have hw : U₁.col i + U₂ *ᵥ F.col i ∈ LinearMap.range Q.mulVecLin := by
    apply hRange
    rw [Matrix.range_mulVecLin]
    apply Submodule.subset_span
    refine ⟨i, ?_⟩
    ext j
    simp [Matrix.col, Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h := vectorTangentToFrame_le_of_orthogonal_competitor hQ hu horth hw
  have hnorm : ‖WithLp.toLp 2 (U₂ *ᵥ F.col i)‖ = ‖WithLp.toLp 2 (F.col i)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa only [dotProduct, pow_two] using
      mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hU₂ (F.col i)
  exact h.trans_eq hnorm

end NLAlib
