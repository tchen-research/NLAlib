import NLAlib.Matrix.Functions.RidgeKernel
import NLAlib.Matrix.Functions.GeometricMean
import NLAlib.Matrix.Functions.GeometricMeanIdentities
import NLAlib.Matrix.Norms.LoewnerBounds

/-!
# Whitening identities for ridge sampling

Whitening the actual rows of `A` by the inverse square root of its regularized Gram matrix
produces squared row norms equal to the ridge leverage scores. The whitened covariance is
the transpose ridge kernel, hence a positive contraction, and its trace is the effective
dimension. These are deterministic identities; the sampling law is added by the consumer.

Source: Cohen–Musco–Musco 2017, Theorem 5; the finite covariance derivation is in
`sketching_lowrank_routes_2026_10_24/sketching.tex`, ridge-sampling section.
Atlas: `ridge-sampling-regularized-approximation` (matrix analysis helpers).
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The actual rows whitened by `(Aᵀ A + ρ I)⁻¹/²`, used only for the analysis of ridge
sampling. The CFC formula is total; the ridge identities require `ρ > 0`. -/
def ridgeWhitenedRows (A : Matrix m n ℝ) (ρ : ℝ) : Matrix m n ℝ :=
  A * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ)

/-- The row Gram matrix of the whitened rows is the actual ridge kernel. -/
theorem ridgeWhitenedRows_mul_transpose (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeWhitenedRows A ρ * (ridgeWhitenedRows A ρ)ᵀ = ridgeKernel A ρ := by
  let T := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ)
  have hT : T.IsHermitian := cfc_predicate _ _
  have hTs : Tᵀ = T := hT.eq
  have hi : (ridgeGram A ρ)⁻¹ = T * T :=
    inv_eq_cfc_inv_sqrt_mul_self (posDef_ridgeGram A hρ)
  change (A * T) * (A * T)ᵀ = A * (ridgeGram A ρ)⁻¹ * Aᵀ
  rw [Matrix.transpose_mul, hTs]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T T Aᵀ, ← hi]

/-- The squared Euclidean norm of each actual whitened row equals its ridge leverage
score. This identifies the rank-one sample size with the sampling domination hypothesis. -/
theorem norm_ridgeWhitenedRows_row_sq (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) (i : m) :
    ‖(WithLp.toLp 2 (ridgeWhitenedRows A ρ i) : EuclideanSpace ℝ n)‖ ^ 2 =
      ridgeLeverageScore A ρ i := by
  rw [norm_toLp_sq_eq_dotProduct_self, ridgeLeverageScore_eq_ridgeKernel_apply]
  have h := congrArg (fun M : Matrix m m ℝ => M i i) (ridgeWhitenedRows_mul_transpose A hρ)
  simpa only [dotProduct, Matrix.mul_apply, Matrix.transpose_apply] using h

/-- The covariance trace of the whitened rows is the actual effective dimension. -/
theorem trace_transpose_ridgeWhitenedRows_mul (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ((ridgeWhitenedRows A ρ)ᵀ * ridgeWhitenedRows A ρ).trace = ridgeEffectiveDimension A ρ := by
  rw [Matrix.trace_mul_comm, ridgeWhitenedRows_mul_transpose A hρ,
    ← ridgeEffectiveDimension_eq_trace]

/-- The column covariance of the whitened rows is the transpose ridge kernel. -/
theorem transpose_ridgeWhitenedRows_mul [DecidableEq m]
    (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (ridgeWhitenedRows A ρ)ᵀ * ridgeWhitenedRows A ρ = ridgeKernel Aᵀ ρ := by
  let T := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ)
  have hT : T.IsHermitian := cfc_predicate _ _
  have hTs : Tᵀ = T := hT.eq
  have hi : (ridgeGram A ρ)⁻¹ = T * T :=
    inv_eq_cfc_inv_sqrt_mul_self (posDef_ridgeGram A hρ)
  have hn : T * ridgeGram A ρ * T = 1 :=
    cfc_inv_sqrt_mul_self_mul_inv_sqrt (posDef_ridgeGram A hρ)
  have hg : Aᵀ * A = ridgeGram A ρ - ρ • 1 := by
    unfold ridgeGram
    abel
  rw [ridgeKernel_eq_one_sub_smul_inv Aᵀ hρ, Matrix.transpose_transpose]
  change (A * T)ᵀ * (A * T) = 1 - ρ • (ridgeGram A ρ)⁻¹
  rw [Matrix.transpose_mul, hTs]
  calc
    T * Aᵀ * (A * T) = T * (Aᵀ * A) * T := by simp only [Matrix.mul_assoc]
    _ = T * (ridgeGram A ρ - ρ • 1) * T := by rw [hg]
    _ = 1 - ρ • (ridgeGram A ρ)⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hn, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, ← hi]

/-- The covariance of the whitened rows is a contraction for every input rank. -/
theorem transpose_ridgeWhitenedRows_mul_le_one [DecidableEq m]
    (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (ridgeWhitenedRows A ρ)ᵀ * ridgeWhitenedRows A ρ ≤ 1 := by
  rw [transpose_ridgeWhitenedRows_mul A hρ]
  exact ridgeKernel_le_one Aᵀ hρ

/-- A bound on the actual whitened Gram difference gives the two regularized Loewner
bounds by congruence with the positive square root. This is a deterministic implication
for arbitrary matrices, with no rank assumption on the approximating matrix. -/
theorem ridgeGram_bounds_of_specNorm_whitened_sub_le {k : Type*} [Fintype k]
    (A : Matrix m n ℝ) (B : Matrix k n ℝ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hbound : specNorm (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ) *
      (Bᵀ * B - Aᵀ * A) * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (ridgeGram A ρ)) ≤ ε) :
    (1 - ε) • ridgeGram A ρ ≤ ridgeGram B ρ ∧
      ridgeGram B ρ ≤ (1 + ε) • ridgeGram A ρ := by
  let H := ridgeGram A ρ
  let T := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) H
  let S := cfc Real.sqrt H
  let D := Bᵀ * B - Aᵀ * A
  let E := T * D * T
  have hT : T.IsHermitian := cfc_predicate _ _
  have hS : S.IsHermitian := cfc_predicate _ _
  have hD : D.IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self B).sub (Matrix.isHermitian_conjTranspose_mul_self A)
  have hE : E.IsHermitian := by
    change Eᴴ = E
    simp only [E, Matrix.conjTranspose_mul, hT.eq, hD.eq, Matrix.mul_assoc]
  have hST : S * T = 1 := cfc_sqrt_mul_inv_sqrt (posDef_ridgeGram A hρ)
  have hTS : T * S = 1 := cfc_inv_sqrt_mul_sqrt (posDef_ridgeGram A hρ)
  have hSS : S * S = H := cfc_sqrt_mul_self (posDef_ridgeGram A hρ)
  have hSE : S * E * S = D := by
    calc
      _ = (S * T) * D * (T * S) := by dsimp only [E]; noncomm_ring
      _ = D := by rw [hST, hTS, Matrix.one_mul, Matrix.mul_one]
  have hcong (X Y : Matrix n n ℝ) (h : X ≤ Y) : S * X * S ≤ S * Y * S := by
    apply Matrix.le_iff.mpr
    simpa only [hS.eq, Matrix.mul_sub, Matrix.sub_mul] using
      (Matrix.le_iff.mp h).mul_mul_conjTranspose_same S
  have hsand := (hE.specNorm_le_iff_sandwich hε).mp hbound
  have hlow : -(ε • H) ≤ D := by
    have h := hcong _ _ hsand.1
    simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hSS, hSE] using h
  have hupp : D ≤ ε • H := by
    have h := hcong _ _ hsand.2
    simpa only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hSE] using h
  have hB : ridgeGram B ρ = H + D := by
    dsimp only [H, D, ridgeGram]
    abel
  rw [hB, sub_smul, add_smul, one_smul]
  exact ⟨by simpa only [H, sub_eq_add_neg, add_comm] using add_le_add_left hlow H,
    by simpa only [H, add_comm] using add_le_add_left hupp H⟩

end NLAlib
