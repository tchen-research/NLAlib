import NLAlib.Matrix.Spectral.ThinSVD
import NLAlib.Matrix.Spectral.SpectralBounds
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Landweber iteration and its singular-coordinate dynamics

The actual affine recurrence has an exact matrix-power error formula. In
positive singular coordinates the error multiplier is `1-ησ²`, while the
nullspace component is preserved. This gives the finite spectral filter
and the limit for arbitrary initialization.

Source: Hansen, §6.3; matrix-toolkit re-derivation, §27.
Atlas: `landweber-spectral-filter`.
-/
noncomputable section
open Matrix Filter Topology
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- The linear error multiplier in Landweber iteration. -/
def landweberStepMatrix (A : Matrix m n 𝕜) (η : ℝ) : Matrix n n 𝕜 :=
  1 - η • (Aᴴ * A)

/-- The actual Landweber recurrence, with arbitrary starting vector. -/
def landweberIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (η : ℝ) (x₀ : n → 𝕜) :
    ℕ → n → 𝕜
  | 0 => x₀
  | t + 1 => landweberIterate A b η x₀ t +
      η • (Aᴴ *ᵥ (b - A *ᵥ landweberIterate A b η x₀ t))

/-- The recurrence written as one linear step and a constant forcing term. -/
theorem landweberIterate_succ (A : Matrix m n 𝕜) (b : m → 𝕜) (η : ℝ)
    (x₀ : n → 𝕜) (t : ℕ) :
    landweberIterate A b η x₀ (t + 1) =
      landweberStepMatrix A η *ᵥ landweberIterate A b η x₀ t + η • (Aᴴ *ᵥ b) := by
  simp only [landweberIterate, landweberStepMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, smul_sub]
  abel

/-- The Moore–Penrose solution is a fixed point of the Landweber step. -/
theorem landweberStepMatrix_mulVec_pinv_add (A : Matrix m n 𝕜) (b : m → 𝕜) (η : ℝ) :
    landweberStepMatrix A η *ᵥ (moorePenroseInverse A *ᵥ b) + η • (Aᴴ *ᵥ b) =
      moorePenroseInverse A *ᵥ b := by
  have hn : Aᴴ * A * moorePenroseInverse A = Aᴴ := by
    have he := congrArg Matrix.conjTranspose (mul_moorePenroseInverse_mul A)
    rw [Matrix.conjTranspose_mul, (mul_moorePenroseInverse_isHermitian A).eq] at he
    simpa only [Matrix.mul_assoc] using he
  simp only [landweberStepMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [Matrix.mulVec_mulVec, hn]
  abel

/-- Exact error propagation about the minimum-norm least-squares solution.
No step-size or rank assumption is needed for this finite identity. -/
theorem landweberIterate_sub_pinv (A : Matrix m n 𝕜) (b : m → 𝕜) (η : ℝ)
    (x₀ : n → 𝕜) (t : ℕ) :
    landweberIterate A b η x₀ t - moorePenroseInverse A *ᵥ b =
      landweberStepMatrix A η ^ t *ᵥ (x₀ - moorePenroseInverse A *ᵥ b) := by
  induction t with
  | zero => simp [landweberIterate]
  | succ t ih =>
    rw [landweberIterate_succ, pow_succ', ← Matrix.mulVec_mulVec, ← ih, Matrix.mulVec_sub]
    have hf := landweberStepMatrix_mulVec_pinv_add A b η
    linear_combination hf

/-- Positive singular directions diagonalize the Landweber error multiplier,
and its complementary nullspace projection is fixed. -/
theorem IsThinSVD.landweberStepMatrix_mul {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (η : ℝ) :
    landweberStepMatrix A η * V = V * diagonal (fun i => ((1 - η * σ i ^ 2 : ℝ) : 𝕜)) ∧
      landweberStepMatrix A η * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have hp := h.isSingularTripletFamily
  have hgram : (Aᴴ * A) * V = V * diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) := by
    rw [Matrix.mul_assoc, hp.mul_right, ← Matrix.mul_assoc, hp.adjoint_mul_left,
      Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [pow_two, RCLike.ofReal_mul]
  constructor
  · rw [landweberStepMatrix, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hgram]
    have hd : diagonal (fun i => ((1 - η * σ i ^ 2 : ℝ) : 𝕜)) =
        (1 : Matrix r r 𝕜) - η • diagonal (fun i => ((σ i ^ 2 : ℝ) : 𝕜)) := by
      ext i j
      by_cases hij : i = j
      · subst j; simp [RCLike.real_smul_eq_coe_mul]
      · simp [hij]
    rw [hd, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  · have hAP : A * (1 - V * Vᴴ) = 0 := by
      rw [h.eq]
      simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ Vᴴ V, h.right_orth.conjTranspose_mul_self, Matrix.mul_one]
      abel
    rw [landweberStepMatrix, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc Aᴴ A, hAP, Matrix.mul_zero, smul_zero, sub_zero]

/-- Exact powers of the Landweber step: a fixed nullspace component and
the scalar powers `(1-ησ²)^t` in the positive singular subspace.
atlas: landweber-spectral-filter (partial) -/
theorem IsThinSVD.landweberStepMatrix_pow {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (η : ℝ) (t : ℕ) :
    landweberStepMatrix A η ^ t = 1 - V * Vᴴ +
      V * diagonal (fun i => (((1 - η * σ i ^ 2) ^ t : ℝ) : 𝕜)) * Vᴴ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ih, Matrix.mul_add, (h.landweberStepMatrix_mul η).2,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, (h.landweberStepMatrix_mul η).1,
      Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal]
    congr 3
    funext i
    simp [pow_succ', RCLike.ofReal_mul]

/-- With zero initialization, the actual iteration is precisely the finite
Landweber spectral filter, including rank-deficient matrices.
atlas: landweber-spectral-filter (partial) -/
theorem IsThinSVD.landweberIterate_zero_eq {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (b : m → 𝕜) (η : ℝ) (t : ℕ) :
    landweberIterate A b η 0 t =
      (V * diagonal (fun i => (((1 - (1 - η * σ i ^ 2) ^ t) / σ i : ℝ) : 𝕜)) * Uᴴ) *ᵥ b := by
  have he := landweberIterate_sub_pinv A b η 0 t
  have hP : (1 - V * Vᴴ) * moorePenroseInverse A = 0 := by
    rw [h.moorePenroseInverse_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have hz : (1 - V * Vᴴ) * V = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
        h.right_orth.conjTranspose_mul_self, Matrix.mul_one, sub_self]
    rw [hz, Matrix.zero_mul, Matrix.zero_mul]
  rw [h.landweberStepMatrix_pow, zero_sub, Matrix.mulVec_neg, Matrix.add_mulVec,
    Matrix.mulVec_mulVec, hP, Matrix.zero_mulVec, zero_add] at he
  have hdiff : moorePenroseInverse A -
      V * diagonal (fun i => (((1 - η * σ i ^ 2) ^ t : ℝ) : 𝕜)) * Vᴴ * moorePenroseInverse A =
      V * diagonal (fun i => (((1 - (1 - η * σ i ^ 2) ^ t) / σ i : ℝ) : 𝕜)) * Uᴴ := by
    rw [h.moorePenroseInverse_eq]
    have hc : (V * diagonal (fun i => (((1 - η * σ i ^ 2) ^ t : ℝ) : 𝕜)) * Vᴴ) *
        (V * diagonal (fun i => ((σ i)⁻¹ : 𝕜)) * Uᴴ) =
        V * (diagonal (fun i => (((1 - η * σ i ^ 2) ^ t : ℝ) : 𝕜)) *
          diagonal (fun i => ((σ i)⁻¹ : 𝕜))) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, h.right_orth.conjTranspose_mul_self, Matrix.one_mul]
    rw [hc, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_sub]
    congr 2
    funext i
    norm_cast
    simp [div_eq_mul_inv, sub_mul]
  rw [← hdiff, Matrix.sub_mulVec]
  rw [← Matrix.mulVec_mulVec]
  linear_combination he

/-- A zero forward operator leaves every starting vector unchanged. -/
@[simp] theorem landweberIterate_zero_matrix (b : m → 𝕜) (η : ℝ) (x₀ : n → 𝕜) (t : ℕ) :
    landweberIterate (0 : Matrix m n 𝕜) b η x₀ t = x₀ := by
  induction t with
  | zero => rfl
  | succ t ih => simp [landweberIterate, ih]

end NLAlib
