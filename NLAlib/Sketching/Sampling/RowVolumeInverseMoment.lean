import NLAlib.Sketching.Sampling.RowVolumePseudoinverse
import NLAlib.ForMathlib.Combinatorics.BinomialRatios
import NLAlib.Matrix.Basic.GramCentering
import NLAlib.Matrix.Norms.Frobenius
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral

/-!
# Inverse and covariance moments for actual row-volume sampling

The exact cofactor sum includes singular subsets whose adjugates may be nonzero.
Their normalized sum is a PSD defect. Retaining that defect gives the precise
inverse and covariance formulas; discarding it gives the stated Loewner and
Frobenius bounds. Full support is required only at the selected subset size
for the equality conclusions.

Source: Dereziński–Warmuth 2018, Theorem 6 and equations (2)–(3).
Atlas: `row-volume-inverse-moment`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

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

/-- The normalized sum of the adjugates of singular size-`s` row restrictions.
The formula is total; moment interpretations use positive row-volume mass. -/
def rowVolumeAdjugateDefect (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) : Matrix d d 𝕜 :=
  ((((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T)⁻¹) •
    ∑ S ∈ T.powersetCard s, if rowSubsetVolume X S = 0 then (rowSubsetGram X S).adjugate else 0

/-- The singular-adjugate defect is PSD, including corank-one restrictions.
No claim that a singular adjugate vanishes is used.
atlas: row-volume-inverse-moment (partial) -/
theorem posSemidef_rowVolumeAdjugateDefect (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) :
    (rowVolumeAdjugateDefect X T s).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply smul_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (rowSubsetVolume_nonneg X T)))
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact (rowSubsetGram_posSemidef X S).adjugate.nonneg
  · exact le_rfl

/-- Full support at the selected size makes the exact singular-adjugate defect
zero. No condition on smaller subsets is imposed. -/
theorem rowVolumeAdjugateDefect_eq_zero_of_full_support (X : Matrix n d 𝕜)
    (T : Finset n) (s : ℕ)
    (hfull : ∀ S ∈ T.powersetCard s, IsUnit (rowSubsetGram X S)) :
    rowVolumeAdjugateDefect X T s = 0 := by
  unfold rowVolumeAdjugateDefect
  have hz : (∑ S ∈ T.powersetCard s,
      if rowSubsetVolume X S = 0 then (rowSubsetGram X S).adjugate else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    exact if_neg ((rowSubsetVolume_pos_iff_isUnit X S).mpr (hfull S hS)).ne'
  rw [hz, smul_zero]

open scoped Matrix.Norms.L2Operator in
/-- The exact inverse Gram expectation equals the explicit inverse multiple
minus the PSD singular-adjugate defect. This holds for actual row-volume sampling
without a general-position assumption. Source: Dereziński–Warmuth 2018, Theorem 6.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_inv_rowSubsetGram_eq_smul_inv_sub_defect
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, (rowSubsetGram X S)⁻¹ ∂rowVolumeLaw X T s hT hds hst) =
      (((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) •
        (rowSubsetGram X T)⁻¹ - rowVolumeAdjugateDefect X T s := by
  classical
  let c := (T.card - Fintype.card d).choose (s - Fintype.card d)
  let c' := (T.card - (Fintype.card d - 1)).choose (s - (Fintype.card d - 1))
  have hc : (0 : ℝ) < c := Nat.cast_pos.mpr (Nat.choose_pos (Nat.sub_le_sub_right hst _))
  have hAdj := sum_adjugate_rowSubsetGram_powersetCard X T s hd ((Nat.sub_le _ _).trans hds)
  change (∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate) =
    (c' : 𝕜) • (rowSubsetGram X T).adjugate at hAdj
  rw [Nat.cast_smul_eq_nsmul 𝕜, ← Nat.cast_smul_eq_nsmul ℝ] at hAdj
  have hsum : (∑ S ∈ T.powersetCard s, rowSubsetVolume X S • (rowSubsetGram X S)⁻¹) =
      (c' : ℝ) • (rowSubsetGram X T).adjugate -
        ∑ S ∈ T.powersetCard s, if rowSubsetVolume X S = 0 then (rowSubsetGram X S).adjugate else 0 := by
    simp_rw [rowSubsetVolume_smul_inv_eq_adjugate_sub_ite]
    rw [Finset.sum_sub_distrib, hAdj]
  have hAdjT : (rowSubsetGram X T).adjugate = rowSubsetVolume X T • (rowSubsetGram X T)⁻¹ := by
    have h := rowSubsetVolume_smul_inv_eq_adjugate_sub_ite X T
    rw [if_neg hT.ne', sub_zero] at h
    exact h.symm
  have hratio : ((((c : ℝ) * rowSubsetVolume X T)⁻¹) * (c' : ℝ)) * rowSubsetVolume X T =
      ((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ) := by
    calc
      _ = (c' : ℝ) / (c : ℝ) := by field_simp [hc.ne', hT.ne']
      _ = _ := Nat.cast_choose_pred_div_choose hd hds hst
  rw [integral_rowVolumeLaw_eq_inv_smul_sum, hsum, smul_sub, hAdjT, smul_smul, smul_smul, hratio]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The inverse Gram expectation is bounded above by `(N-d+1)/(s-d+1)` times
the ambient inverse Gram. Singular subsets have their actual zero probability.
Source: Dereziński–Warmuth 2018, Theorem 6.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_inv_rowSubsetGram_le
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, (rowSubsetGram X S)⁻¹ ∂rowVolumeLaw X T s hT hds hst) ≤
      (((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) •
        (rowSubsetGram X T)⁻¹ := by
  rw [integral_inv_rowSubsetGram_eq_smul_inv_sub_defect X T s hd hT hds hst]
  exact sub_le_self _ (posSemidef_rowVolumeAdjugateDefect X T s).nonneg

open scoped Matrix.Norms.L2Operator in
/-- The same expectation is the second row Gram moment of the total padded
Moore–Penrose inverse, including at singular zero-mass subsets. -/
theorem integral_rowSubsetPseudoinverse_mul_conjTranspose_eq_integral_inv
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, rowSubsetPseudoinverse X S * (rowSubsetPseudoinverse X S)ᴴ
      ∂rowVolumeLaw X T s hT hds hst) =
      ∫ S, (rowSubsetGram X S)⁻¹ ∂rowVolumeLaw X T s hT hds hst := by
  rw [integral_rowVolumeLaw_eq_inv_smul_sum, integral_rowVolumeLaw_eq_inv_smul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun S _ => rowSubsetVolume_smul_pseudoinverse_mul_conjTranspose X S)

open scoped Matrix.Norms.L2Operator in
/-- Centering the actual row-volume pseudoinverse law subtracts precisely the
Gram of its proved mean; it does not assume any general-position condition. -/
theorem integral_centered_rowSubsetPseudoinverse_mul_conjTranspose
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T) *
        (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T)ᴴ
      ∂rowVolumeLaw X T s hT hds hst) =
      (∫ S, rowSubsetPseudoinverse X S * (rowSubsetPseudoinverse X S)ᴴ
        ∂rowVolumeLaw X T s hT hds hst) -
        rowSubsetPseudoinverse X T * (rowSubsetPseudoinverse X T)ᴴ := by
  classical
  let Z := ((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T
  let p := fun S => rowVolumeWeight X T S s / Z
  have hZ : 0 < Z := by
    dsimp only [Z]
    rw [← sum_rowVolumeWeight X T s hds]
    exact sum_rowVolumeWeight_pos X T s hT hds hst
  have hp : ∑ S, p S = 1 := by
    simp only [p, ← Finset.sum_div]
    rw [sum_rowVolumeWeight X T s hds]
    exact div_self hZ.ne'
  have hmean : ∑ S, p S • rowSubsetPseudoinverse X S = rowSubsetPseudoinverse X T := by
    simpa only [integral_rowVolumeLaw, p, Z] using
      integral_rowSubsetPseudoinverse X T s hT hds hst
  simpa only [integral_rowVolumeLaw, p, Z] using
    sum_smul_sub_mul_conjTranspose p hp (rowSubsetPseudoinverse X) (rowSubsetPseudoinverse X T) hmean

open scoped Matrix.Norms.L2Operator in
/-- The exact covariance of the padded inverse has coefficient `(N-s)/(s-d+1)`
and the same explicit PSD singular-adjugate defect as the inverse moment.
Source: Dereziński–Warmuth 2018, Theorem 6.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_centered_rowSubsetPseudoinverse_eq_smul_inv_sub_defect
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T) *
        (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T)ᴴ
      ∂rowVolumeLaw X T s hT hds hst) =
      (((T.card - s : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) •
        (rowSubsetGram X T)⁻¹ - rowVolumeAdjugateDefect X T s := by
  rw [integral_centered_rowSubsetPseudoinverse_mul_conjTranspose,
    integral_rowSubsetPseudoinverse_mul_conjTranspose_eq_integral_inv,
    integral_inv_rowSubsetGram_eq_smul_inv_sub_defect X T s hd hT hds hst,
    rowSubsetPseudoinverse_mul_conjTranspose_of_isUnit X T
      ((rowSubsetVolume_pos_iff_isUnit X T).mp hT)]
  have hn : T.card - Fintype.card d + 1 = (s - Fintype.card d + 1) + (T.card - s) := by omega
  have hr : ((T.card - Fintype.card d + 1 : ℕ) : ℝ) /
      ((s - Fintype.card d + 1 : ℕ) : ℝ) - 1 =
      ((T.card - s : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ) := by
    rw [hn, Nat.cast_add]
    field_simp
    ring
  rw [← hr, sub_smul, one_smul]
  abel

open scoped Matrix.Norms.L2Operator in
/-- The covariance Loewner bound for the actual padded pseudoinverse under
size-`s` row-volume sampling, without a general-position hypothesis.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_centered_rowSubsetPseudoinverse_le
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T) *
        (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T)ᴴ
      ∂rowVolumeLaw X T s hT hds hst) ≤
      (((T.card - s : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) •
        (rowSubsetGram X T)⁻¹ := by
  rw [integral_centered_rowSubsetPseudoinverse_eq_smul_inv_sub_defect X T s hd hT hds hst]
  exact sub_le_self _ (posSemidef_rowVolumeAdjugateDefect X T s).nonneg

open scoped Matrix.Norms.L2Operator in
/-- If every subset at the selected size has full column rank, the inverse
moment bound is an equality. Smaller subsets need not have full rank.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_inv_rowSubsetGram_eq_of_full_support
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (hfull : ∀ S ∈ T.powersetCard s, IsUnit (rowSubsetGram X S)) :
    (∫ S, (rowSubsetGram X S)⁻¹ ∂rowVolumeLaw X T s hT hds hst) =
      (((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) •
        (rowSubsetGram X T)⁻¹ := by
  rw [integral_inv_rowSubsetGram_eq_smul_inv_sub_defect X T s hd hT hds hst,
    rowVolumeAdjugateDefect_eq_zero_of_full_support X T s hfull, sub_zero]

open scoped Matrix.Norms.L2Operator in
/-- The covariance bound is an equality under full support at the selected
size, with no stronger general-position assumption.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_centered_rowSubsetPseudoinverse_eq_of_full_support
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (hfull : ∀ S ∈ T.powersetCard s, IsUnit (rowSubsetGram X S)) :
    (∫ S, (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T) *
        (rowSubsetPseudoinverse X S - rowSubsetPseudoinverse X T)ᴴ
      ∂rowVolumeLaw X T s hT hds hst) =
      (((T.card - s : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) •
        (rowSubsetGram X T)⁻¹ := by
  rw [integral_centered_rowSubsetPseudoinverse_eq_smul_inv_sub_defect X T s hd hT hds hst,
    rowVolumeAdjugateDefect_eq_zero_of_full_support X T s hfull, sub_zero]

open scoped Matrix.Norms.L2Operator in
/-- The exact Frobenius second moment retains the trace of the explicit PSD
singular-adjugate defect. Source: Dereziński–Warmuth 2018, Theorem 6.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_frobSq_rowSubsetPseudoinverse_eq_sub_defect
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, frobSq (rowSubsetPseudoinverse X S) ∂rowVolumeLaw X T s hT hds hst) =
      (((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) *
        frobSq (rowSubsetPseudoinverse X T) - RCLike.re (rowVolumeAdjugateDefect X T s).trace := by
  have hnorm (S : Finset n) : frobSq (rowSubsetPseudoinverse X S) =
      RCLike.re (rowSubsetPseudoinverse X S * (rowSubsetPseudoinverse X S)ᴴ).trace := by
    rw [frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.trace_mul_comm]
  calc
    _ = RCLike.re (∫ S, rowSubsetPseudoinverse X S * (rowSubsetPseudoinverse X S)ᴴ
        ∂rowVolumeLaw X T s hT hds hst).trace := by
      rw [Matrix.re_trace_integral (Integrable.of_finite)]
      exact integral_congr_ae (ae_of_all _ hnorm)
    _ = _ := by
      rw [integral_rowSubsetPseudoinverse_mul_conjTranspose_eq_integral_inv,
        integral_inv_rowSubsetGram_eq_smul_inv_sub_defect X T s hd hT hds hst,
        Matrix.trace_sub, Matrix.trace_smul, map_sub, RCLike.smul_re,
        ← rowSubsetPseudoinverse_mul_conjTranspose_of_isUnit X T
          ((rowSubsetVolume_pos_iff_isUnit X T).mp hT), ← hnorm]

open scoped Matrix.Norms.L2Operator in
/-- The Frobenius second moment bound for the literal padded pseudoinverse
under actual fixed-size row-volume sampling, without general position.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_frobSq_rowSubsetPseudoinverse_le
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (∫ S, frobSq (rowSubsetPseudoinverse X S) ∂rowVolumeLaw X T s hT hds hst) ≤
      (((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) *
        frobSq (rowSubsetPseudoinverse X T) := by
  rw [integral_frobSq_rowSubsetPseudoinverse_eq_sub_defect X T s hd hT hds hst]
  exact sub_le_self _ (RCLike.nonneg_iff.mp
    (posSemidef_rowVolumeAdjugateDefect X T s).trace_nonneg).1

open scoped Matrix.Norms.L2Operator in
/-- The Frobenius bound is an equality if all size-`s` row restrictions have
full column rank. No condition on smaller restrictions is used.
atlas: row-volume-inverse-moment (partial) -/
theorem integral_frobSq_rowSubsetPseudoinverse_eq_of_full_support
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (hfull : ∀ S ∈ T.powersetCard s, IsUnit (rowSubsetGram X S)) :
    (∫ S, frobSq (rowSubsetPseudoinverse X S) ∂rowVolumeLaw X T s hT hds hst) =
      (((T.card - Fintype.card d + 1 : ℕ) : ℝ) / ((s - Fintype.card d + 1 : ℕ) : ℝ)) *
        frobSq (rowSubsetPseudoinverse X T) := by
  rw [integral_frobSq_rowSubsetPseudoinverse_eq_sub_defect X T s hd hT hds hst,
    rowVolumeAdjugateDefect_eq_zero_of_full_support X T s hfull, Matrix.trace_zero, map_zero, sub_zero]

end NLAlib
