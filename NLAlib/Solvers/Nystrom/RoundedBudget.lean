import NLAlib.Solvers.Nystrom.ExpectedCondition

/-!
# The rounded effective-dimension sketch width

The FTU rule takes `k=ceil(3 d_eff/2)` and `ell=2k+1`. The head is positive
unless the input is zero, and its cost is linear in effective dimension.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Head size in the FTU effective-dimension rule. -/
def nystromSketchHead {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : ℕ :=
  ⌈3 * nystromEffectiveDimension A μ / 2⌉₊

/-- Gaussian sketch width in the FTU rule, before optional ambient-dimension capping. -/
def nystromSketchWidth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : ℕ :=
  nystromSketchHead A μ + (nystromSketchHead A μ + 1)

/-- The exact rounded head meets the effective-dimension threshold. -/
theorem le_nystromSketchHead {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    3 * nystromEffectiveDimension A μ / 2 ≤ nystromSketchHead A μ := Nat.le_ceil _

/-- Effective dimension is nonnegative under positive regularization. -/
theorem nystromEffectiveDimension_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {μ : ℝ} (hμ : 0 < μ) : 0 ≤ nystromEffectiveDimension A μ := by
  unfold nystromEffectiveDimension effectiveDimensionOfSpectrum
  exact Finset.sum_nonneg fun i _ => div_nonneg (singularValues_nonneg A i)
    (add_nonneg (singularValues_nonneg A i) hμ.le)

open scoped Matrix.Norms.L2Operator in
/-- Every nonzero matrix has positive effective dimension at positive regularization. -/
theorem nystromEffectiveDimension_pos_of_ne_zero {n : ℕ} [Nonempty (Fin n)]
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    0 < nystromEffectiveDimension A μ := by
  have hn : specNorm A ≠ 0 := by simpa only [specNorm_eq_norm, ne_eq, norm_eq_zero] using hA
  have hpos := lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm hn)
  have hσ : 0 < singularValues A 0 := by rwa [singularValues_zero_eq_specNorm]
  have ht : 0 < singularValues A 0 / (singularValues A 0 + μ) :=
    div_pos hσ (add_pos hσ hμ)
  apply lt_of_lt_of_le ht
  unfold nystromEffectiveDimension effectiveDimensionOfSpectrum
  let i0 : Fin n := ⟨0, by simpa only [Fintype.card_fin] using (Fintype.card_pos : 0 < Fintype.card (Fin n))⟩
  exact Finset.single_le_sum (s := Finset.univ) (a := i0) (fun (i : Fin n) _ => div_nonneg (singularValues_nonneg A i)
    (add_nonneg (singularValues_nonneg A i) hμ.le)) (Finset.mem_univ i0)

/-- The rounded head is nonzero for a nonzero input. -/
theorem nystromSketchHead_pos_of_ne_zero {n : ℕ} [Nonempty (Fin n)]
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    0 < nystromSketchHead A μ := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by norm_num) (nystromEffectiveDimension_pos_of_ne_zero hA hμ))
    (by norm_num)

/-- The full rounded sketch count is at most `3 d_eff + 3`.
atlas: nystrom-pcg (partial) -/
theorem nystromSketchWidth_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    (nystromSketchWidth A μ : ℝ) ≤ 3 * nystromEffectiveDimension A μ + 3 := by
  have h := (Nat.ceil_lt_add_one
    (show 0 ≤ 3 * nystromEffectiveDimension A μ / 2 by
      have := nystromEffectiveDimension_nonneg A hμ; positivity)).le
  unfold nystromSketchWidth nystromSketchHead
  push_cast
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The retained floor is at most the regularization at every sketch, even
when the sketch is wider than the ambient dimension. -/
theorem nystromFloor_le_regularization_of_effectiveDimension {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {μ : ℝ} (hμ : 0 < μ)
    (hk : nystromEffectiveDimension A μ ≤ k)
    (Ω : Matrix (Fin n) (Fin (k+(k+1))) ℝ) : nystromFloor A Ω ≤ μ := by
  change singularValues (nystrom A Ω) (k+(k+1)-1) ≤ μ
  by_cases hj : k+(k+1)-1 < n
  · let j : Fin n := ⟨k+(k+1)-1, hj⟩
    apply (singularValues_nystrom_le hA Ω j).trans
    have h := apply_le_mul_of_effectiveDimensionOfSpectrum_le
      (fun i : Fin n => singularValues A i) (fun i => singularValues_nonneg A i)
      (fun i l hil => singularValues_antitone A hil) hμ (by norm_num : (0 : ℝ) < 1) j (by
        change (1 + 1 / (1 : ℝ)) * nystromEffectiveDimension A μ ≤ (j.val : ℝ) + 1
        have he : j.val = 2*k := by dsimp [j]; omega
        rw [he]
        push_cast
        linarith)
    simpa using h
  · rw [singularValues_eq_zero_of_height_le _ (by simpa using Nat.le_of_not_gt hj)]
    exact hμ.le

/-- The rounded head also meets the weaker effective-dimension threshold. -/
theorem nystromEffectiveDimension_le_nystromSketchHead {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ} (hμ : 0 < μ) :
    nystromEffectiveDimension A μ ≤ nystromSketchHead A μ := by
  have := le_nystromSketchHead A μ
  have := nystromEffectiveDimension_nonneg A hμ
  linarith

end NLAlib
