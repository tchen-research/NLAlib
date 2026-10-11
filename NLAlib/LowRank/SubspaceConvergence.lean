import NLAlib.Krylov.Block
import NLAlib.Matrix.PolynomialIntertwining
import NLAlib.Matrix.GraphTangent

/-!
# Magnitude-gap convergence of subspace iteration

Right normalization identifies each iterate with a transverse graph. Its largest
principal-angle tangent is the graph operator norm. The resulting contraction
uses the magnitude gap, so it also applies to indefinite symmetric matrices.
Source: Saad (2011), §5.1; manuscript `sa:subspace`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- Right normalization gives the exact graph of every subspace iterate.
Source: manuscript `sa:graph`; Saad (2011), §5.1. Right inverses are explicit data. -/
theorem subspaceIterate_eq_range_graph
    {A : Matrix n n ℝ} {U₁ : Matrix n k ℝ} {U₂ : Matrix n r ℝ}
    {L₁ Linv : Matrix k k ℝ} {L₂ : Matrix r r ℝ}
    (hA₁ : A * U₁ = U₁ * L₁) (hA₂ : A * U₂ = U₂ * L₂)
    {Ω : Matrix n k ℝ} {Ω₁ R : Matrix k k ℝ} {Ω₂ : Matrix r k ℝ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    (hL : L₁ * Linv = 1) (t : ℕ) :
    subspaceIterate A Ω t =
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
  have hrange := subspaceIterate_mul_of_isUnit A Ω (hRu.mul (hLu.pow t)) t
  rw [subspaceIterate, ← Matrix.mul_assoc, hN] at hrange
  exact hrange.symm

/-- Graph operators contract at the exact norm-product rate.
Source: manuscript `sa:subspace-theorem`, submultiplicativity step. The empty tail
is included without requiring the norm of its identity to equal one. -/
theorem specNorm_pow_mul_mul_pow_le
    (L₂ : Matrix r r ℝ) (F : Matrix r k ℝ) (Linv : Matrix k k ℝ) (t : ℕ) :
    specNorm (L₂ ^ t * F * Linv ^ t) ≤
      (specNorm L₂ * specNorm Linv) ^ t * specNorm F := by
  have hp₂ : specNorm (L₂ ^ t) ≤ specNorm L₂ ^ t := by
    cases t with
    | zero => simpa only [pow_zero] using (specNorm_one_le (n := r))
    | succ t => exact norm_pow_le' L₂ (Nat.succ_pos t)
  have hp₁ : specNorm (Linv ^ t) ≤ specNorm Linv ^ t := by
    cases t with
    | zero => simpa only [pow_zero] using (specNorm_one_le (n := k))
    | succ t => exact norm_pow_le' Linv (Nat.succ_pos t)
  calc specNorm (L₂ ^ t * F * Linv ^ t) ≤
        (specNorm (L₂ ^ t) * specNorm F) * specNorm (Linv ^ t) :=
      (specNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ (specNorm L₂ ^ t * specNorm F) * specNorm Linv ^ t :=
      mul_le_mul (mul_le_mul_of_nonneg_right hp₂ (specNorm_nonneg F)) hp₁
        (specNorm_nonneg _) (mul_nonneg (pow_nonneg (specNorm_nonneg _) _) (specNorm_nonneg _))
    _ = _ := by rw [mul_pow]; ring

/-- Largest principal-angle tangents of subspace iteration contract by the magnitude
gap factor. Source: manuscript `sa:subspace-theorem`; Saad (2011), §5.1.
For diagonal eigenvalue blocks, `specNorm L₂ * specNorm Linv` is
`max |λ_tail| / min |λ_head|`. This form allows indefinite matrices and empty tails.
atlas: subspace-iteration-convergence (partial) -/
theorem subspaceTangent_subspaceIterate_le
    {A : Matrix n n ℝ} {U₁ : Matrix n k ℝ} {U₂ : Matrix n r ℝ}
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0)
    {L₁ Linv : Matrix k k ℝ} {L₂ : Matrix r r ℝ}
    (hA₁ : A * U₁ = U₁ * L₁) (hA₂ : A * U₂ = U₂ * L₂)
    {Ω : Matrix n k ℝ} {Ω₁ R : Matrix k k ℝ} {Ω₂ : Matrix r k ℝ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    (hL : L₁ * Linv = 1) (t : ℕ) :
    subspaceTangent U₁ U₂ (subspaceIterate A Ω t) ≤
      (specNorm L₂ * specNorm Linv) ^ t *
        subspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) := by
  have hzero := subspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL 0
  simp only [subspaceIterate, pow_zero, Matrix.one_mul, Matrix.mul_one] at hzero
  rw [subspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL t, hzero,
    subspaceTangent_range_graph_eq_specNorm hU₁ hU₂ hU,
    subspaceTangent_range_graph_eq_specNorm hU₁ hU₂ hU]
  simpa only [Matrix.mul_assoc] using specNorm_pow_mul_mul_pow_le L₂ (Ω₂ * R) Linv t

/-- The explicit magnitude-gap bound uses any positive lower bound on the absolute
leading eigenvalues. Taking their minimum gives the manuscript's `γ = ‖Λ₂‖ / α`;
for a sorted PSD spectrum this is the usual tail/head eigenvalue ratio.
Source: manuscript `sa:subspace-theorem`; Saad (2011), §5.1.
atlas: subspace-iteration-convergence (partial) -/
theorem subspaceTangent_subspaceIterate_le_of_diagonal
    {A : Matrix n n ℝ} {U₁ : Matrix n k ℝ} {U₂ : Matrix n r ℝ}
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (eig₁ : k → ℝ) (eig₂ : r → ℝ)
    (hA₁ : A * U₁ = U₁ * Matrix.diagonal eig₁)
    (hA₂ : A * U₂ = U₂ * Matrix.diagonal eig₂)
    {Ω : Matrix n k ℝ} {Ω₁ R : Matrix k k ℝ} {Ω₂ : Matrix r k ℝ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    {α : ℝ} (hα : 0 < α) (hgap : ∀ i, α ≤ |eig₁ i|) (t : ℕ) :
    subspaceTangent U₁ U₂ (subspaceIterate A Ω t) ≤
      (specNorm (Matrix.diagonal eig₂) / α) ^ t *
        subspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) := by
  let Linv : Matrix k k ℝ := Matrix.diagonal fun i => (eig₁ i)⁻¹
  have hEigenNonzero : ∀ i, eig₁ i ≠ 0 := by
    intro i hi
    have := hgap i
    rw [hi, abs_zero] at this
    linarith
  have hL : Matrix.diagonal eig₁ * Linv = 1 := by
    dsimp only [Linv]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hEigenNonzero i)
  have hLi : specNorm Linv ≤ 1 / α := by
    dsimp only [Linv]
    rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [Real.norm_eq_abs, abs_inv, ← one_div]
    exact one_div_le_one_div_of_le hα (hgap i)
  have hrate : specNorm (Matrix.diagonal eig₂) * specNorm Linv ≤
      specNorm (Matrix.diagonal eig₂) / α := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_left hLi (specNorm_nonneg (Matrix.diagonal eig₂))
  have hzero := subspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL 0
  simp only [subspaceIterate, pow_zero, Matrix.one_mul, Matrix.mul_one] at hzero
  have htan : 0 ≤ subspaceTangent U₁ U₂ (LinearMap.range Ω.mulVecLin) := by
    rw [hzero, subspaceTangent_range_graph_eq_specNorm hU₁ hU₂ hU]
    exact specNorm_nonneg _
  exact (subspaceTangent_subspaceIterate_le hU₁ hU₂ hU hA₁ hA₂ hΩ hR hL t).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) hrate t) htan)

/-- Each graph column contracts using its own leading eigenvalue magnitude.
Source: manuscript `sa:subspace`, per-vector rate after `sa:subspace-theorem`.
The initial factor is the graph-column norm, as required by the corrected statement. -/
theorem norm_graph_col_le_of_diagonal (L₂ : Matrix r r ℝ) (F : Matrix r k ℝ)
    (eig : k → ℝ) (t : ℕ) (i : k) :
    ‖WithLp.toLp 2 ((L₂ ^ t * F * (Matrix.diagonal fun j => (eig j)⁻¹) ^ t).col i)‖ ≤
      (specNorm L₂ / |eig i|) ^ t * ‖WithLp.toLp 2 (F.col i)‖ := by
  have hcol : (L₂ ^ t * F * (Matrix.diagonal fun j => (eig j)⁻¹) ^ t).col i =
      ((eig i)⁻¹) ^ t • (L₂ ^ t *ᵥ F.col i) := by
    ext j
    change (L₂ ^ t * F * (Matrix.diagonal fun j => (eig j)⁻¹) ^ t) j i = _
    rw [Matrix.diagonal_pow, Matrix.mul_diagonal]
    change (L₂ ^ t * F) j i * ((eig i)⁻¹) ^ t =
      ((eig i)⁻¹) ^ t * (L₂ ^ t * F) j i
    ring
  have hp : specNorm (L₂ ^ t) ≤ specNorm L₂ ^ t := by
    cases t with
    | zero => simpa only [pow_zero] using (specNorm_one_le (n := r))
    | succ t => exact norm_pow_le' L₂ (Nat.succ_pos t)
  have hv : ‖WithLp.toLp 2 (L₂ ^ t *ᵥ F.col i)‖ ≤
      specNorm L₂ ^ t * ‖WithLp.toLp 2 (F.col i)‖ :=
    (Matrix.l2_opNorm_mulVec (L₂ ^ t) (WithLp.toLp 2 (F.col i))).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  rw [hcol, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_pow, abs_inv]
  calc |eig i|⁻¹ ^ t * ‖WithLp.toLp 2 (L₂ ^ t *ᵥ F.col i)‖ ≤
        |eig i|⁻¹ ^ t * (specNorm L₂ ^ t * ‖WithLp.toLp 2 (F.col i)‖) :=
      mul_le_mul_of_nonneg_left hv (pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _)
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

/-- Every leading eigenvector has the corrected individual magnitude-gap angle rate
to a frame containing the iterate. Source: manuscript `sa:subspace`, final per-vector
clause; Saad (2011), §5.1. The initial constant is `‖F₀ e_i‖`, not its initial angle
to the whole starting subspace. A frame for exactly the iterate is a special case.
atlas: subspace-iteration-convergence (partial) -/
theorem vectorTangentToFrame_subspaceIterate_le_of_diagonal
    {l : Type*} [Fintype l] [DecidableEq l]
    {A : Matrix n n ℝ} {U₁ : Matrix n k ℝ} {U₂ : Matrix n r ℝ}
    (hU₁ : HasOrthonormalCols U₁) (hU₂ : HasOrthonormalCols U₂)
    (hU : U₁ᵀ * U₂ = 0) (eig₁ : k → ℝ) (L₂ : Matrix r r ℝ)
    (hA₁ : A * U₁ = U₁ * Matrix.diagonal eig₁) (hA₂ : A * U₂ = U₂ * L₂)
    {Ω : Matrix n k ℝ} {Ω₁ R : Matrix k k ℝ} {Ω₂ : Matrix r k ℝ}
    (hΩ : Ω = U₁ * Ω₁ + U₂ * Ω₂) (hR : Ω₁ * R = 1)
    (hEigen : ∀ i, eig₁ i ≠ 0) (t : ℕ) {Q : Matrix n l ℝ}
    (hQ : HasOrthonormalCols Q)
    (hRange : subspaceIterate A Ω t ≤ LinearMap.range Q.mulVecLin) (i : k) :
    vectorTangentToFrame Q (U₁.col i) ≤
      (specNorm L₂ / |eig₁ i|) ^ t * ‖WithLp.toLp 2 ((Ω₂ * R).col i)‖ := by
  let Linv : Matrix k k ℝ := Matrix.diagonal fun i => (eig₁ i)⁻¹
  have hL : Matrix.diagonal eig₁ * Linv = 1 := by
    dsimp only [Linv]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact mul_inv_cancel₀ (hEigen j)
  rw [subspaceIterate_eq_range_graph hA₁ hA₂ hΩ hR hL t] at hRange
  have h := vectorTangentToFrame_graph_col_le hQ hU₁ hU₂ hU _ hRange i
  exact h.trans (by simpa only [Matrix.mul_assoc] using
    norm_graph_col_le_of_diagonal L₂ (Ω₂ * R) eig₁ t i)

end NLAlib
