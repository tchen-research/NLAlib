import NLAlib.Sketching.Sampling.CovarianceBernstein
import NLAlib.Matrix.Subspaces.Projections

/-!
# Relative Gram approximation from leverage sampling

Sampling the original rows preserves its full Gram matrix when an orthonormal frame
for its column range is preserved. This reduces finite-rank covariance approximation
to the actual finite covariance Bernstein theorem, with dimension equal to the frame
dimension, including deficient ambient data matrices.

Source: Tropp 2015, Theorem 6.1.1; Spielman–Srivastava, Theorem 1 and Lemmas 3–4.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A sampled orthonormal frame controls the full Gram matrix of data in its range.
The sampled data matrix is the literal selection and rescaling of the original rows. -/
theorem sampled_gram_bounds_of_specNorm_frame_sub_le {r s : ℕ}
    (A : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) (hU : HasOrthonormalCols U)
    (hUA : U * (Uᵀ * A) = A) (p : m → ℝ≥0) (ω : Fin s → m)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : specNorm ((sampledRowMatrix U p ω)ᵀ * sampledRowMatrix U p ω - 1) ≤ ε) :
    (1 - ε) • (Aᵀ * A) ≤ (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω ∧
      (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω ≤ (1 + ε) • (Aᵀ * A) := by
  let D := Uᵀ * A
  let T := (sampledRowMatrix U p ω)ᵀ * sampledRowMatrix U p ω
  have hH : (T - 1).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self (sampledRowMatrix U p ω)).sub
      Matrix.isHermitian_one
  have hsand := (hH.specNorm_le_iff_sandwich hε).mp hbound
  have hLo : (1 - ε) • (1 : Matrix (Fin r) (Fin r) ℝ) ≤ T := by
    rw [sub_smul, one_smul]
    have h := add_le_add_right hsand.1 (1 : Matrix (Fin r) (Fin r) ℝ)
    convert h using 1 <;> abel
  have hHi : T ≤ (1 + ε) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [add_smul, one_smul]
    have h := add_le_add_right hsand.2 (1 : Matrix (Fin r) (Fin r) ℝ)
    convert h using 1
    abel
  have hcong (X Y : Matrix (Fin r) (Fin r) ℝ) (h : X ≤ Y) :
      Dᵀ * X * D ≤ Dᵀ * Y * D := by
    apply Matrix.le_iff.mpr
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] using
      (Matrix.le_iff.mp h).conjTranspose_mul_mul_same D
  have hAD : Dᵀ * D = Aᵀ * A := by
    have hu : Uᵀ * U = 1 := hU.conjTranspose_mul_self
    calc
      _ = (U * D)ᵀ * (U * D) := by
        rw [Matrix.transpose_mul U D]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U D, hu, Matrix.one_mul]
      _ = _ := by rw [show U * D = A from hUA]
  have hsamp : sampledRowMatrix A p ω = sampledRowMatrix U p ω * D := by
    rw [← hUA, sampledRowMatrix_mul]
  have hsampleGram : Dᵀ * T * D =
      (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω := by
    rw [hsamp, Matrix.transpose_mul (sampledRowMatrix U p ω) D]
    simp only [T, Matrix.mul_assoc]
  constructor
  · have h := hcong _ _ hLo
    simpa only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAD, hsampleGram] using h
  · have h := hcong _ _ hHi
    simpa only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAD, hsampleGram] using h

omit [DecidableEq n] in
/-- Actual independent row sampling with leverage-dominating probabilities preserves
the complete data Gram matrix, with the frame dimension in the tail prefactor.
Source: Tropp 2015, Theorem 6.1.1; Spielman–Srivastava, Theorem 1 and Lemmas 3–4. -/
theorem measureReal_sampled_gram_sandwich_failure_le
    [MeasurableSpace m] [MeasurableSingletonClass m]
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) (hU : HasOrthonormalCols U)
    (hUA : U * (Uᵀ * A) = A) (p : m → ℝ≥0) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, (∑ a, ‖U i a‖ ^ 2) ≤ (r : ℝ) * (p i : ℝ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (Measure.pi (fun _ : Fin s => finiteSamplingLaw p hp)).real
      {ω | ¬ ((1 - ε) • (Aᵀ * A) ≤ (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω ∧
        (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω ≤ (1 + ε) • (Aᵀ * A))} ≤
      2 * r * Real.exp (-(s : ℝ) * ε ^ 2 / (3 * r)) := by
  classical
  let : NeZero r := ⟨hr.ne'⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hgram : Uᵀ * U = 1 := hU.conjTranspose_mul_self
  have htail := measureReal_specNorm_sampled_transpose_mul_sub_le U p hp hrR
    (by rw [hgram]) hdom hs hε
  simp only [hgram, Fintype.card_fin] at htail
  have hsubset : {ω : Fin s → m | ¬ ((1 - ε) • (Aᵀ * A) ≤
      (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω ∧
      (sampledRowMatrix A p ω)ᵀ * sampledRowMatrix A p ω ≤ (1 + ε) • (Aᵀ * A))} ⊆
      {ω | ε < specNorm ((sampledRowMatrix U p ω)ᵀ * sampledRowMatrix U p ω - 1)} := by
    intro ω hω
    by_contra hnot
    exact hω (sampled_gram_bounds_of_specNorm_frame_sub_le A U hU hUA p ω hε.le (not_lt.mp hnot))
  refine (measureReal_mono hsubset).trans (htail.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hden : 0 < 2 * (r : ℝ) * (1 + ε / 3) := by positivity
  have hdenle : 2 * (r : ℝ) * (1 + ε / 3) ≤ 3 * r := by nlinarith
  apply (div_le_div_iff₀ hden (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hdenle
    (show 0 ≤ (s : ℝ) * ε ^ 2 by positivity)
  nlinarith only [hh]

end NLAlib
