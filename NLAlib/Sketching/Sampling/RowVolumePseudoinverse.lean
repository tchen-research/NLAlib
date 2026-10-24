import NLAlib.Sketching.Sampling.RowVolumeLaw
import NLAlib.Matrix.Basic.RowSubsetPseudoinverse

/-!
# Unbiased padded pseudoinverses under row-volume sampling

The actual finite row-volume law normalizes the determinant-weighted matrix identity.
The theorem retains singular subsets with their zero masses and needs no general-position
condition. Ambient row sets are arbitrary; choosing all rows gives the original matrix
pseudoinverse and its consequences for every fixed right-hand-side matrix.

Source: Dereziński–Warmuth 2018, Theorem 5 and Appendix B.
Atlas: `row-volume-pseudoinverse-unbiased`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
private local instance {r c : Type*} [Fintype r] [Fintype c] [DecidableEq c] :
    NormedSpace ℝ (Matrix r c 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro t A
    have he : t • A = (t : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (t : 𝕜) A

/-- Integrals under the row-volume law are the inverse normalizer times the
literal determinant-weighted sum over the specified sized subsets. -/
theorem integral_rowVolumeLaw_eq_inv_smul_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (f : Finset n → E) :
    (∫ S, f S ∂rowVolumeLaw X T s hT hds hst) =
      ((((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T)⁻¹) •
        ∑ S ∈ T.powersetCard s, rowSubsetVolume X S • f S := by
  classical
  rw [integral_rowVolumeLaw]
  have hsum : (∑ S : Finset n, rowVolumeWeight X T S s • f S) =
      ∑ S ∈ T.powersetCard s, rowSubsetVolume X S • f S := by
    simp only [rowVolumeWeight, ite_smul, zero_smul, ← Finset.sum_filter]
    congr 1
    ext S
    simp
  rw [← hsum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [smul_smul]
  congr 1
  ring

open scoped Matrix.Norms.L2Operator in
/-- The actual padded row-subset pseudoinverse is integrable under every
admissible row-volume law, including its singular zero-mass subsets.
atlas: row-volume-pseudoinverse-unbiased (partial) -/
theorem integrable_rowSubsetPseudoinverse (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    Integrable (rowSubsetPseudoinverse X) (rowVolumeLaw X T s hT hds hst) := .of_finite

open scoped Matrix.Norms.L2Operator in
/-- Actual fixed-size row-volume sampling is unbiased for the padded
Moore–Penrose inverse, without any general-position assumption. For `T = univ`
the mean is exactly `X⁺`. Source: Dereziński–Warmuth 2018, Theorem 5 and Appendix B.
atlas: row-volume-pseudoinverse-unbiased (partial) -/
theorem integral_rowSubsetPseudoinverse (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, rowSubsetPseudoinverse X S ∂rowVolumeLaw X T s hT hds hst) =
      rowSubsetPseudoinverse X T := by
  have hZ := sum_rowVolumeWeight_pos X T s hT hds hst
  rw [sum_rowVolumeWeight X T s hds] at hZ
  rw [integral_rowVolumeLaw_eq_inv_smul_sum, sum_rowSubsetVolume_smul_pseudoinverse_powersetCard X T s hds,
    smul_smul, inv_mul_cancel₀ hZ.ne', one_smul]

open scoped Matrix.Norms.L2Operator in
/-- Every fixed right-hand-side matrix inherits unbiased least-squares
coefficients from the actual row-volume law.
atlas: row-volume-pseudoinverse-unbiased (partial) -/
theorem integral_rowSubsetPseudoinverse_mul {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (Y : Matrix n r 𝕜) :
    (∫ S, rowSubsetPseudoinverse X S * Y ∂rowVolumeLaw X T s hT hds hst) =
      rowSubsetPseudoinverse X T * Y := by
  calc
    _ = (∫ S, rowSubsetPseudoinverse X S ∂rowVolumeLaw X T s hT hds hst) * Y := by
      rw [integral_rowVolumeLaw, integral_rowVolumeLaw]
      simp only [Matrix.sum_mul, Matrix.smul_mul]
    _ = _ := congrArg (fun M => M * Y) (integral_rowSubsetPseudoinverse X T s hT hds hst)

open scoped Matrix.Norms.L2Operator in
/-- The corresponding fitted-matrix estimator is unbiased, and at all rows its
mean is the native column-space projector `X X⁺`.
atlas: row-volume-pseudoinverse-unbiased (partial) -/
theorem integral_mul_rowSubsetPseudoinverse (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, X * rowSubsetPseudoinverse X S ∂rowVolumeLaw X T s hT hds hst) =
      X * rowSubsetPseudoinverse X T := by
  calc
    _ = X * (∫ S, rowSubsetPseudoinverse X S ∂rowVolumeLaw X T s hT hds hst) := by
      rw [integral_rowVolumeLaw, integral_rowVolumeLaw]
      simp only [Matrix.mul_sum, Matrix.mul_smul]
    _ = _ := congrArg (fun M => X * M) (integral_rowSubsetPseudoinverse X T s hT hds hst)

open scoped Matrix.Norms.L2Operator in
/-- The exact pseudoinverse mean transports to any probability space carrying
the actual finite row-volume subset law.
atlas: row-volume-pseudoinverse-unbiased (partial) -/
theorem integral_rowSubsetPseudoinverse_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (R : Ω → Finset n) (hR : HasLaw R (rowVolumeLaw X T s hT hds hst) μ) :
    (∫ ω, rowSubsetPseudoinverse X (R ω) ∂μ) = rowSubsetPseudoinverse X T := by
  calc
    _ = ∫ S, rowSubsetPseudoinverse X S ∂rowVolumeLaw X T s hT hds hst :=
      hR.integral_comp (show AEStronglyMeasurable (rowSubsetPseudoinverse X)
        (rowVolumeLaw X T s hT hds hst) from .of_discrete)
    _ = _ := integral_rowSubsetPseudoinverse X T s hT hds hst

end NLAlib
