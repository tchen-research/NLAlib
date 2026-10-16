import NLAlib.Matrix.Basic.QuadraticMinimization
import NLAlib.Matrix.Spectral.ThinSVD
import NLAlib.Matrix.Functions.DiagonalFilter
/-!
# Tikhonov regularization

The positive regularization parameter makes the normal matrix positive
definite at every rank. Its inverse filter is the usual singular-value
filter, converges to the full Moore–Penrose inverse as the parameter tends
to zero from above, and has the sharp noise envelope `1/(2√β)`.

Source: Hansen, Rank-Deficient and Discrete Ill-Posed Problems, §4.3;
matrix-toolkit re-derivation, §25. Atlas: `tikhonov-spectral-filter`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- The positive-parameter Tikhonov normal matrix. -/
def tikhonovNormal (A : Matrix m n 𝕜) (β : ℝ) : Matrix n n 𝕜 := Aᴴ * A + β • 1

/-- The Tikhonov regularized inverse operator. -/
def tikhonovInverse (A : Matrix m n 𝕜) (β : ℝ) : Matrix n m 𝕜 :=
  (tikhonovNormal A β)⁻¹ * Aᴴ

/-- The actual penalized Euclidean least-squares objective. -/
def tikhonovObjective (A : Matrix m n 𝕜) (b : m → 𝕜) (β : ℝ) (x : n → 𝕜) : ℝ :=
  ‖WithLp.toLp 2 (A *ᵥ x - b)‖ ^ 2 + β * ‖WithLp.toLp 2 x‖ ^ 2

/-- Positive regularization makes the normal matrix positive definite,
without any rank assumption. -/
theorem posDef_tikhonovNormal (A : Matrix m n 𝕜) {β : ℝ} (hβ : 0 < β) :
    (tikhonovNormal A β).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self A)
    (Matrix.PosDef.one.smul hβ)

/-- The singular-coordinate formula for the actual regularized inverse.
Only positive singular directions are needed; all null directions are zero.
atlas: tikhonov-spectral-filter (partial) -/
theorem IsThinSVD.tikhonovInverse_eq {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) {β : ℝ} (hβ : 0 < β) :
    tikhonovInverse A β =
      V * diagonal (fun i => ((σ i / (σ i ^ 2 + β) : ℝ) : 𝕜)) * Uᴴ := by
  let S : Matrix r r 𝕜 := diagonal (fun i => (σ i : 𝕜))
  let G : Matrix r r 𝕜 := diagonal (fun i => ((σ i ^ 2 + β : ℝ) : 𝕜))
  let F : Matrix r r 𝕜 := diagonal (fun i => ((σ i / (σ i ^ 2 + β) : ℝ) : 𝕜))
  have hp := h.isSingularTripletFamily
  have hHV : tikhonovNormal A β * V = V * G := by
    calc
      _ = Aᴴ * (A * V) + β • V := by
        simp [tikhonovNormal, Matrix.add_mul, Matrix.mul_assoc]
      _ = V * S * S + β • V := by
        rw [hp.mul_right, ← Matrix.mul_assoc, hp.adjoint_mul_left]
      _ = V * (S * S + β • (1 : Matrix r r 𝕜)) := by
        simp [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by
        congr 1
        ext i j
        by_cases hij : i = j
        · subst j; simp [G, S, Matrix.diagonal_mul_diagonal, pow_two,
            RCLike.real_smul_eq_coe_mul]
        · simp [G, S, Matrix.diagonal_mul_diagonal, hij]
  have hGF : G * F = S := by
    dsimp only [G, F, S]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    have hd : σ i ^ 2 + β ≠ 0 := by positivity
    field_simp [hd]
  have hS : Sᴴ = S := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [S, Matrix.conjTranspose_apply]
    · simp [S, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have hAstar : Aᴴ = V * S * Uᴴ := by
    rw [h.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    change V * (Sᴴ * Uᴴ) = _
    rw [hS]
    rw [Matrix.mul_assoc]
  have hnormal : tikhonovNormal A β * (V * F * Uᴴ) = Aᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hHV, Matrix.mul_assoc V G F, hGF,
      ← hAstar]
  unfold tikhonovInverse
  rw [← hnormal, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_tikhonovNormal A hβ).isUnit), Matrix.one_mul]

/-- The penalized least-squares objective is the normal-matrix quadratic
plus the data-dependent constant. -/
theorem tikhonovObjective_eq_quadraticObjective (A : Matrix m n 𝕜) (b : m → 𝕜)
    (β : ℝ) (x : n → 𝕜) :
    tikhonovObjective A b β x =
      2 * quadraticObjective (tikhonovNormal A β) (Aᴴ *ᵥ b) x +
        ‖WithLp.toLp 2 b‖ ^ 2 := by
  have hc : star (Aᴴ *ᵥ b) ⬝ᵥ x = star b ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose]
  have hr : RCLike.re (star (A *ᵥ x) ⬝ᵥ b) = RCLike.re (star b ⬝ᵥ (A *ᵥ x)) := by
    calc
      _ = RCLike.re (star (star b ⬝ᵥ (A *ᵥ x))) := by
        congr 1
        rw [← Matrix.star_dotProduct_star, star_star]
      _ = _ := by simp [RCLike.star_def]
  have hq : RCLike.re (quadForm (tikhonovNormal A β) x) =
      RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) + β * RCLike.re (star x ⬝ᵥ x) := by
    simp only [tikhonovNormal, quadForm, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, map_add,
      RCLike.real_smul_eq_coe_mul, RCLike.re_ofReal_mul]
    rw [← quadForm, quadForm_conjTranspose_mul_self]
  simp only [tikhonovObjective, norm_toLp_sq_eq_re_star_dotProduct, star_sub,
    sub_dotProduct, dotProduct_sub, map_sub, quadraticObjective, hq, hc, hr]
  ring

/-- The unique minimizer of the actual penalized least-squares objective is
`(AᴴA+βI)⁻¹Aᴴb`, with no rank assumption.
atlas: tikhonov-spectral-filter (partial) -/
theorem tikhonovInverse_mulVec_unique_minimizer (A : Matrix m n 𝕜) (b : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) :
    (∀ x, tikhonovObjective A b β (tikhonovInverse A β *ᵥ b) ≤
      tikhonovObjective A b β x) ∧
    ∀ x, tikhonovObjective A b β x ≤
      tikhonovObjective A b β (tikhonovInverse A β *ᵥ b) →
        x = tikhonovInverse A β *ᵥ b := by
  have hmin := quadraticObjective_inv_mulVec_minimizer (posDef_tikhonovNormal A hβ) (Aᴴ *ᵥ b)
  simp only [tikhonovInverse, ← Matrix.mulVec_mulVec,
    tikhonovObjective_eq_quadraticObjective]
  constructor
  · intro x
    linarith [hmin.1 x]
  · intro x hx
    apply hmin.2 x
    linarith

private theorem abs_tikhonov_scalar_filter_le {s β : ℝ} (hs : 0 ≤ s) (hβ : 0 < β) :
    |s / (s ^ 2 + β)| ≤ 1 / (2 * Real.sqrt β) := by
  have hd : 0 < s ^ 2 + β := by positivity
  have hr : 0 < 2 * Real.sqrt β := by positivity
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ hd hr]
  have hsq := Real.sq_sqrt hβ.le
  nlinarith [sq_nonneg (s - Real.sqrt β)]

/-- The sharp scalar filter envelope bounds the regularized inverse norm.
atlas: tikhonov-spectral-filter (partial) -/
theorem specNorm_tikhonovInverse_le (A : Matrix m n 𝕜) {β : ℝ} (hβ : 0 < β) :
    specNorm (tikhonovInverse A β) ≤ 1 / (2 * Real.sqrt β) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  rw [h.tikhonovInverse_eq hβ,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols h.left_orth,
    specNorm_mul_left_of_hasOrthonormalCols h.right_orth]
  open scoped Matrix.Norms.L2Operator in
    rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [RCLike.norm_ofReal]
    exact abs_tikhonov_scalar_filter_le (singularValues_nonneg A i) hβ

/-- Noise amplification is at most `‖e‖/(2√β)`, uniformly over the data.
atlas: tikhonov-spectral-filter (partial) -/
theorem norm_tikhonovInverse_noise_le (A : Matrix m n 𝕜) (b e : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) :
    ‖WithLp.toLp 2 (tikhonovInverse A β *ᵥ (b + e) - tikhonovInverse A β *ᵥ b)‖ ≤
      ‖WithLp.toLp 2 e‖ / (2 * Real.sqrt β) := by
  rw [Matrix.mulVec_add, add_sub_cancel_left]
  calc
    _ ≤ specNorm (tikhonovInverse A β) * ‖WithLp.toLp 2 e‖ := by
      open scoped Matrix.Norms.L2Operator in
        exact (tikhonovInverse A β).l2_opNorm_mulVec (WithLp.toLp 2 e)
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_right (specNorm_tikhonovInverse_le A hβ)
        (norm_nonneg (WithLp.toLp 2 e))
      simpa [div_eq_mul_inv, mul_comm] using hb

end NLAlib
