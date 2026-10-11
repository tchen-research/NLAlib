import NLAlib.Matrix.ComplexProjectionBounds
import NLAlib.Matrix.PolynomialIntertwining
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Complex subspace iteration and its transverse graph

The actual complex column range of `A^t Ω` is a transverse graph after right
normalization. Its largest principal-angle tangent is the graph operator norm,
which contracts at the magnitude-gap rate. Source: manuscript `sa:subspace`;
Saad (2011), §5.1. All ambient and block labels are arbitrary finite types.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- The actual complex subspace iterate is the range of `A^t Ω`.
Source: manuscript `sa:subspace`, subspace iteration definition. -/
def complexSubspaceIterate (A : Matrix n n ℂ) (Ω : Matrix n k ℂ) (t : ℕ) :
    Submodule ℂ (n → ℂ) := LinearMap.range (A ^ t * Ω).mulVecLin

/-- Largest tangent to an orthogonal head block, measured using complex head and
tail coordinates. For a transverse graph this is the usual supremum of tail/head
norm ratios. Source: manuscript `sa:graph`; Saad (2011), §5.1. -/
def complexSubspaceTangent (U₁ : Matrix n k ℂ) (U₂ : Matrix n r ℂ)
    (S : Submodule ℂ (n → ℂ)) : ℝ :=
  sSup ((fun x : n → ℂ => ‖WithLp.toLp 2 (U₂ᴴ *ᵥ x)‖) ''
    {x | x ∈ S ∧ ‖WithLp.toLp 2 (U₁ᴴ *ᵥ x)‖ ≤ 1})

omit [DecidableEq n] in
/-- The complex principal-angle tangent of an orthogonal transverse graph equals
its operator norm, including empty head and tail blocks.
Source: manuscript `sa:graph`; Saad (2011), §5.1. -/
theorem complexSubspaceTangent_range_graph_eq_norm
    {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1)
    (hU : U₁ᴴ * U₂ = 0) (F : Matrix r k ℂ) :
    complexSubspaceTangent U₁ U₂ (LinearMap.range (U₁ + U₂ * F).mulVecLin) = ‖F‖ := by
  have hU' : U₂ᴴ * U₁ = 0 := by
    have h := congrArg Matrix.conjTranspose hU
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  have hhead : ∀ z : k → ℂ, U₁ᴴ *ᵥ ((U₁ + U₂ * F) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, Matrix.mul_add, ← Matrix.mul_assoc, hU₁, hU,
      Matrix.zero_mul, add_zero, Matrix.one_mulVec]
  have htail : ∀ z : k → ℂ, U₂ᴴ *ᵥ ((U₁ + U₂ * F) *ᵥ z) = F *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, Matrix.mul_add, ← Matrix.mul_assoc, hU', hU₂,
      Matrix.one_mul, zero_add]
  let f := (Matrix.toEuclideanLin (𝕜 := ℂ)).trans LinearMap.toContinuousLinearMap F
  have he : ((fun x : n → ℂ => ‖WithLp.toLp 2 (U₂ᴴ *ᵥ x)‖) ''
      {x | x ∈ LinearMap.range (U₁ + U₂ * F).mulVecLin ∧
        ‖WithLp.toLp 2 (U₁ᴴ *ᵥ x)‖ ≤ 1}) =
      ((fun z : EuclideanSpace ℂ k => ‖f z‖) '' Metric.closedBall 0 1) := by
    ext a
    constructor
    · rintro ⟨x, ⟨⟨z, rfl⟩, hz⟩, rfl⟩
      refine ⟨WithLp.toLp 2 z, ?_, ?_⟩
      · simpa only [Matrix.mulVecLin_apply, hhead, Metric.mem_closedBall,
          dist_zero_right] using hz
      · change ‖WithLp.toLp 2 (F *ᵥ z)‖ =
          ‖WithLp.toLp 2 (U₂ᴴ *ᵥ ((U₁ + U₂ * F) *ᵥ z))‖
        rw [htail]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(U₁ + U₂ * F) *ᵥ WithLp.ofLp z, ⟨⟨WithLp.ofLp z, rfl⟩, ?_⟩, ?_⟩
      · simpa only [hhead, WithLp.toLp_ofLp, Metric.mem_closedBall,
          dist_zero_right] using hz
      · change ‖WithLp.toLp 2 (U₂ᴴ *ᵥ ((U₁ + U₂ * F) *ᵥ WithLp.ofLp z))‖ =
          ‖WithLp.toLp 2 (F *ᵥ WithLp.ofLp z)‖
        rw [htail]
  rw [complexSubspaceTangent, he, ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  rfl

/-- Right normalization identifies the actual complex iterate with its exact graph.
Source: manuscript `sa:graph`; Saad (2011), §5.1. Inverses are supplied as data. -/
theorem complexSubspaceIterate_eq_range_graph
    {A : Matrix n n ℂ} {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    {L₁ Linv : Matrix k k ℂ} {L₂ : Matrix r r ℂ}
    (hA₁ : A * U₁ = U₁ * L₁) (hA₂ : A * U₂ = U₂ * L₂)
    {Ω : Matrix n k ℂ} {Ω₁ R : Matrix k k ℂ} {Ω₂ : Matrix r k ℂ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    (hL : L₁ * Linv = 1) (t : ℕ) :
    complexSubspaceIterate A Ω t =
      LinearMap.range (U₁ + U₂ * (L₂ ^ t * Ω₂ * R * Linv ^ t)).mulVecLin := by
  have hpow : L₁ ^ t * Linv ^ t = 1 := by
    have hc : Commute L₁ Linv := by
      change L₁ * Linv = Linv * L₁
      rw [hL, mul_eq_one_comm.1 hL]
    rw [← hc.mul_pow, hL, one_pow]
  have hY : A ^ t * Ω = U₁ * L₁ ^ t * Ω₁ + U₂ * L₂ ^ t * Ω₂ := by
    rw [hΩ, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      pow_mul_eq_mul_pow_of_mul_eq hA₁, pow_mul_eq_mul_pow_of_mul_eq hA₂]
  have hN : A ^ t * Ω * (R * Linv ^ t) =
      U₁ + U₂ * (L₂ ^ t * Ω₂ * R * Linv ^ t) := by
    rw [hY, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ω₁, hR, Matrix.one_mul, hpow, Matrix.mul_one]
  have hRu : IsUnit R :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hR)
  have hLu : IsUnit Linv :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hL)
  have hrange : LinearMap.range (A ^ t * Ω * (R * Linv ^ t)).mulVecLin =
      LinearMap.range (A ^ t * Ω).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
    rw [LinearMap.range_eq_top.2 (Matrix.mulVec_surjective_iff_isUnit.2
      (hRu.mul (hLu.pow t))), Submodule.map_top]
  rw [hN] at hrange
  exact hrange.symm

/-- Complex graph powers contract at the exact norm-product rate, including empty
blocks at time zero. Source: manuscript `sa:subspace-theorem`. -/
theorem norm_pow_mul_mul_pow_complex_le
    (L₂ : Matrix r r ℂ) (F : Matrix r k ℂ) (Linv : Matrix k k ℂ) (t : ℕ) :
    ‖L₂ ^ t * F * Linv ^ t‖ ≤ (‖L₂‖ * ‖Linv‖) ^ t * ‖F‖ := by
  have hp₂ : ‖L₂ ^ t‖ ≤ ‖L₂‖ ^ t := by
    cases t with
    | zero => simpa only [pow_zero] using
        (norm_le_one_of_isHermitian_of_isIdempotentElem
          (P := (1 : Matrix r r ℂ)) Matrix.isHermitian_one
          (by change (1 : Matrix r r ℂ) * 1 = 1; exact Matrix.mul_one _))
    | succ t => exact norm_pow_le' L₂ (Nat.succ_pos t)
  have hp₁ : ‖Linv ^ t‖ ≤ ‖Linv‖ ^ t := by
    cases t with
    | zero => simpa only [pow_zero] using
        (norm_le_one_of_isHermitian_of_isIdempotentElem
          (P := (1 : Matrix k k ℂ)) Matrix.isHermitian_one
          (by change (1 : Matrix k k ℂ) * 1 = 1; exact Matrix.mul_one _))
    | succ t => exact norm_pow_le' Linv (Nat.succ_pos t)
  calc ‖L₂ ^ t * F * Linv ^ t‖ ≤ (‖L₂ ^ t‖ * ‖F‖) * ‖Linv ^ t‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (‖L₂‖ ^ t * ‖F‖) * ‖Linv‖ ^ t :=
      mul_le_mul (mul_le_mul_of_nonneg_right hp₂ (norm_nonneg F)) hp₁
        (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
    _ = _ := by rw [mul_pow]; ring

/-- Complex principal-angle tangents contract by the magnitude-gap norm product.
Source: manuscript `sa:subspace-theorem`; Saad (2011), §5.1. The invariant blocks
may be indefinite; empty tails and all times are included.
atlas: subspace-iteration-convergence (partial) -/
theorem complexSubspaceTangent_complexSubspaceIterate_le
    {A : Matrix n n ℂ} {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    {L₁ Linv : Matrix k k ℂ} {L₂ : Matrix r r ℂ}
    (hA₁ : A * U₁ = U₁ * L₁) (hA₂ : A * U₂ = U₂ * L₂)
    {Ω : Matrix n k ℂ} {Ω₁ R : Matrix k k ℂ} {Ω₂ : Matrix r k ℂ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    (hL : L₁ * Linv = 1) (t : ℕ) :
    complexSubspaceTangent U₁ U₂ (complexSubspaceIterate A Ω t) ≤
      (‖L₂‖ * ‖Linv‖) ^ t * complexSubspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) := by
  have hzero := complexSubspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL 0
  simp only [complexSubspaceIterate, pow_zero, Matrix.one_mul, Matrix.mul_one] at hzero
  rw [complexSubspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL t, hzero,
    complexSubspaceTangent_range_graph_eq_norm hU₁ hU₂ hU,
    complexSubspaceTangent_range_graph_eq_norm hU₁ hU₂ hU]
  simpa only [Matrix.mul_assoc] using norm_pow_mul_mul_pow_complex_le L₂ (Ω₂ * R) Linv t

/-- The explicit complex magnitude-gap bound uses a positive lower envelope for
the leading eigenvalue magnitudes. Real Hermitian eigenvalues may have either
sign. Source: manuscript `sa:subspace-theorem`; Saad (2011), §5.1.
atlas: subspace-iteration-convergence (partial) -/
theorem complexSubspaceTangent_complexSubspaceIterate_le_of_diagonal
    {A : Matrix n n ℂ} {U₁ : Matrix n k ℂ} {U₂ : Matrix n r ℂ}
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (eig₁ : k → ℂ) (eig₂ : r → ℂ)
    (hA₁ : A * U₁ = U₁ * Matrix.diagonal eig₁)
    (hA₂ : A * U₂ = U₂ * Matrix.diagonal eig₂)
    {Ω : Matrix n k ℂ} {Ω₁ R : Matrix k k ℂ} {Ω₂ : Matrix r k ℂ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    {α : ℝ} (hα : 0 < α) (hgap : ∀ i, α ≤ ‖eig₁ i‖) (t : ℕ) :
    complexSubspaceTangent U₁ U₂ (complexSubspaceIterate A Ω t) ≤
      (‖Matrix.diagonal eig₂‖ / α) ^ t *
        complexSubspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) := by
  let Linv : Matrix k k ℂ := Matrix.diagonal fun i => (eig₁ i)⁻¹
  have hEigenNonzero : ∀ i, eig₁ i ≠ 0 := by
    intro i hi
    have := hgap i
    rw [hi, norm_zero] at this
    linarith
  have hL : Matrix.diagonal eig₁ * Linv = 1 := by
    dsimp only [Linv]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hEigenNonzero i)
  have hLi : ‖Linv‖ ≤ 1 / α := by
    dsimp only [Linv]
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hα (hgap i)
  have hrate : ‖Matrix.diagonal eig₂‖ * ‖Linv‖ ≤ ‖Matrix.diagonal eig₂‖ / α := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left hLi (norm_nonneg (Matrix.diagonal eig₂))
  have hzero := complexSubspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL 0
  simp only [complexSubspaceIterate, pow_zero, Matrix.one_mul, Matrix.mul_one] at hzero
  have htan : 0 ≤ complexSubspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) := by
    rw [hzero, complexSubspaceTangent_range_graph_eq_norm hU₁ hU₂ hU]
    exact norm_nonneg _
  exact (complexSubspaceTangent_complexSubspaceIterate_le hU₁ hU₂ hU hA₁ hA₂ hΩ hR hL t).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hrate t) htan)

end NLAlib
