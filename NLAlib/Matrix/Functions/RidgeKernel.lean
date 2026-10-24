import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Functions.LoewnerHeinz

/-!
# Ridge leverage scores and the ridge kernel

For positive regularization, `ridgeGram A ρ = Aᵀ A + ρ I` is positive definite and
`ridgeKernel A ρ = A (ridgeGram A ρ)⁻¹ Aᵀ` is a positive contraction. Ridge leverage scores
are the quadratic forms of the inverse regularized Gram matrix at the actual rows of `A`;
their sum is the effective dimension. Increasing regularization decreases the kernel and
every score. The spectral-sum formula is developed separately in `RidgeSpectral`.

Source: Cohen–Musco–Musco 2017, ridge scores and Lemma 4, in the transposed general-ρ form;
the finite derivation is `sketching_lowrank_routes_2026_10_24/sketching.tex`, ridge section.
Atlas: `ridge-leverage-effective-dimension`.
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The regularized column Gram matrix `Aᵀ A + ρ I`. It is positive definite for `ρ > 0`.
The definition is total; the inverse-based ridge results require positive regularization.
atlas: ridge-leverage-effective-dimension (partial) -/
def ridgeGram (A : Matrix m n ℝ) (ρ : ℝ) : Matrix n n ℝ := Aᵀ * A + ρ • 1

/-- The ridge kernel `A (Aᵀ A + ρ I)⁻¹ Aᵀ`. For positive regularization this is a positive
contraction on the row-index space. At other parameters the displayed total inverse formula
is retained without asserting a ridge-score interpretation.
atlas: ridge-leverage-effective-dimension (partial) -/
def ridgeKernel (A : Matrix m n ℝ) (ρ : ℝ) : Matrix m m ℝ :=
  A * (ridgeGram A ρ)⁻¹ * Aᵀ

/-- The ridge leverage score of row `i`: its quadratic form under `(Aᵀ A + ρ I)⁻¹`.
Theorems about ridge scores use `ρ > 0`; the zero-regularization Moore–Penrose convention is
the separate native ordinary leverage-score interface.
atlas: ridge-leverage-effective-dimension (partial) -/
def ridgeLeverageScore (A : Matrix m n ℝ) (ρ : ℝ) (i : m) : ℝ :=
  quadForm (ridgeGram A ρ)⁻¹ (A i)

/-- The ridge effective dimension is the finite sum of the actual row ridge scores.
Its singular-value formula is a theorem, rather than another definition.
atlas: ridge-leverage-effective-dimension (partial) -/
def ridgeEffectiveDimension (A : Matrix m n ℝ) (ρ : ℝ) : ℝ :=
  ∑ i, ridgeLeverageScore A ρ i

/-- Positive regularization makes the column Gram matrix positive definite, at every rank
and including empty dimensions. -/
theorem posDef_ridgeGram (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (ridgeGram A ρ).PosDef := by
  have hi : (ρ • (1 : Matrix n n ℝ)).PosDef := Matrix.PosDef.one.smul hρ
  have h := hi.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  rw [add_comm] at h
  simpa only [ridgeGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    h

/-- The quadratic-form ridge score is exactly the corresponding diagonal entry of the
ridge kernel. No regularization hypothesis is needed for this algebraic identity.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeLeverageScore_eq_ridgeKernel_apply (A : Matrix m n ℝ) (ρ : ℝ) (i : m) :
    ridgeLeverageScore A ρ i = ridgeKernel A ρ i i := by
  simp only [ridgeLeverageScore, ridgeKernel, quadForm, star_trivial, dotProduct,
    Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The effective dimension is the trace of the ridge kernel.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeEffectiveDimension_eq_trace (A : Matrix m n ℝ) (ρ : ℝ) :
    ridgeEffectiveDimension A ρ = (ridgeKernel A ρ).trace := by
  simp only [ridgeEffectiveDimension, ridgeLeverageScore_eq_ridgeKernel_apply,
    Matrix.trace, Matrix.diag]

/-- The ridge kernel is positive semidefinite for positive regularization. -/
theorem posSemidef_ridgeKernel (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (ridgeKernel A ρ).PosSemidef := by
  simpa only [ridgeKernel, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (posDef_ridgeGram A hρ).inv.posSemidef.mul_mul_conjTranspose_same A

/-- Every ridge leverage score is nonnegative.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeLeverageScore_nonneg (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) (i : m) :
    0 ≤ ridgeLeverageScore A ρ i :=
  (posDef_ridgeGram A hρ).inv.posSemidef.quadForm_nonneg _

/-- At positive regularization a row has zero ridge score exactly when that row is zero.
In particular, a zero-probability row in ridge-score-dominated sampling contributes nothing. -/
theorem ridgeLeverageScore_eq_zero_iff (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) (i : m) :
    ridgeLeverageScore A ρ i = 0 ↔ A i = 0 := by
  constructor
  · intro hzero
    by_contra hrow
    have hp := (posDef_ridgeGram A hρ).inv.quadForm_pos hrow
    change 0 < ridgeLeverageScore A ρ i at hp
    rw [hzero] at hp
    exact (lt_irrefl 0) hp
  · intro hrow
    simp only [ridgeLeverageScore, hrow, quadForm_zero_right]

/-- The ridge effective dimension is nonnegative. -/
theorem ridgeEffectiveDimension_nonneg (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ ridgeEffectiveDimension A ρ :=
  Finset.sum_nonneg fun i _ => ridgeLeverageScore_nonneg A hρ i

omit [Fintype n] in
/-- Increasing regularization increases the regularized column Gram matrix. -/
theorem ridgeGram_mono (A : Matrix m n ℝ) {ρ μ : ℝ} (hρμ : ρ ≤ μ) :
    ridgeGram A ρ ≤ ridgeGram A μ := by
  rw [Matrix.le_iff]
  have heq : ridgeGram A μ - ridgeGram A ρ = (μ - ρ) • (1 : Matrix n n ℝ) := by
    simp only [ridgeGram, sub_smul]
    abel
  rw [heq]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hρμ)

/-- Increasing positive regularization decreases the ridge kernel in Loewner order. -/
theorem ridgeKernel_antitone (A : Matrix m n ℝ) {ρ μ : ℝ}
    (hρ : 0 < ρ) (hρμ : ρ ≤ μ) : ridgeKernel A μ ≤ ridgeKernel A ρ := by
  have hi := inv_le_inv_of_posDef (posDef_ridgeGram A hρ) (ridgeGram_mono A hρμ)
  have hp := (Matrix.le_iff.mp hi).mul_mul_conjTranspose_same A
  apply Matrix.le_iff.mpr
  simpa only [ridgeKernel, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_sub, Matrix.sub_mul] using hp

/-- Each ridge leverage score decreases as the positive regularization parameter grows.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeLeverageScore_antitone (A : Matrix m n ℝ) {ρ μ : ℝ}
    (hρ : 0 < ρ) (hρμ : ρ ≤ μ) (i : m) :
    ridgeLeverageScore A μ i ≤ ridgeLeverageScore A ρ i := by
  rw [ridgeLeverageScore_eq_ridgeKernel_apply, ridgeLeverageScore_eq_ridgeKernel_apply]
  have hd : 0 ≤ (ridgeKernel A ρ - ridgeKernel A μ) i i :=
    (Matrix.le_iff.mp (ridgeKernel_antitone A hρ hρμ)).diag_nonneg
  simpa only [Matrix.sub_apply, sub_nonneg] using hd

/-- The effective dimension decreases as the positive regularization parameter grows.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeEffectiveDimension_antitone (A : Matrix m n ℝ) {ρ μ : ℝ}
    (hρ : 0 < ρ) (hρμ : ρ ≤ μ) :
    ridgeEffectiveDimension A μ ≤ ridgeEffectiveDimension A ρ :=
  Finset.sum_le_sum fun i _ => ridgeLeverageScore_antitone A hρ hρμ i

/-- The ridge kernel is the identity minus the scaled inverse regularized row Gram matrix.
This push-through identity includes rank-deficient and empty matrices. -/
theorem ridgeKernel_eq_one_sub_smul_inv [DecidableEq m]
    (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeKernel A ρ = 1 - ρ • (ridgeGram Aᵀ ρ)⁻¹ := by
  have hc := (Matrix.isUnit_iff_isUnit_det _).mp (posDef_ridgeGram A hρ).isUnit
  have hr := (Matrix.isUnit_iff_isUnit_det _).mp (posDef_ridgeGram Aᵀ hρ).isUnit
  have hcomm : ridgeGram Aᵀ ρ * A = A * ridgeGram A ρ := by
    simp only [ridgeGram, Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hprod : ridgeGram Aᵀ ρ * ridgeKernel A ρ = A * Aᵀ := by
    calc
      ridgeGram Aᵀ ρ * ridgeKernel A ρ =
          (ridgeGram Aᵀ ρ * A) * (ridgeGram A ρ)⁻¹ * Aᵀ := by
        simp only [ridgeKernel, Matrix.mul_assoc]
      _ = (A * ridgeGram A ρ) * (ridgeGram A ρ)⁻¹ * Aᵀ := by rw [hcomm]
      _ = A * Aᵀ := by
        rw [Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ hc, Matrix.mul_one]
  have hK : ridgeKernel A ρ = (ridgeGram Aᵀ ρ)⁻¹ * (A * Aᵀ) := by
    have hh := congrArg (fun X => (ridgeGram Aᵀ ρ)⁻¹ * X) hprod
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hr, Matrix.one_mul] using hh
  have hrow : A * Aᵀ = ridgeGram Aᵀ ρ - ρ • 1 := by
    simp only [ridgeGram, Matrix.transpose_transpose]
    abel
  rw [hK, hrow, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hr,
    Matrix.mul_smul, Matrix.mul_one]

/-- The ridge kernel is below the identity for positive regularization. -/
theorem ridgeKernel_le_one [DecidableEq m] (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeKernel A ρ ≤ 1 := by
  rw [Matrix.le_iff, ridgeKernel_eq_one_sub_smul_inv A hρ]
  have heq : (1 : Matrix m m ℝ) - (1 - ρ • (ridgeGram Aᵀ ρ)⁻¹) =
      ρ • (ridgeGram Aᵀ ρ)⁻¹ := by abel
  rw [heq]
  exact (posDef_ridgeGram Aᵀ hρ).inv.posSemidef.smul hρ.le

/-- Every ridge leverage score is at most one.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeLeverageScore_le_one (A : Matrix m n ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (i : m) : ridgeLeverageScore A ρ i ≤ 1 := by
  classical
  rw [ridgeLeverageScore_eq_ridgeKernel_apply]
  have hd : 0 ≤ (1 - ridgeKernel A ρ) i i :=
    (Matrix.le_iff.mp (ridgeKernel_le_one A hρ)).diag_nonneg
  simpa only [Matrix.sub_apply, Matrix.one_apply, if_true, sub_nonneg] using hd

end NLAlib
