/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Functions.SingularValueTransform
import NLAlib.Matrix.Subspaces.ProjectorCapture
import NLAlib.Matrix.Subspaces.SingularDirectionProjector

/-! # Rank-penalized approximation by singular-direction selection

The range projector turns the objective into a linear function of projector diagonals
in a full singular basis, plus a nonnegative squared residual. Every threshold tie may
be selected independently. Without ties the diagonal and the whole projector are forced.
Source: Fessler–Nadakuditi (2024), §§7.4–7.5, equations (7.28), (7.30), (7.34).
Atlas: `rank-penalty-thresholding`.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The rank-penalized squared-error objective, with total rank and exact normalization. -/
def rankPenaltyObjective (μ : ℝ) (Y X : Matrix m n 𝕜) : ℝ :=
  1 / 2 * frobSq (Y - X) + μ * X.rank

/-- The strict hard-threshold selector. At a threshold tie it discards the direction. -/
def singularValueHardThreshold (μ : ℝ) (Y : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  singularValueTransform (fun s => if Real.sqrt (2 * μ) < s then s else 0) Y

private theorem coefficient_mul_indicator_le {c w : ℝ} {keep : Bool}
    (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (hneg : c < 0 → keep = true) (hpos : 0 < c → keep = false) :
    c * (if keep then 1 else 0) ≤ c * w := by
  cases hk : keep with
  | false =>
    have hc : 0 ≤ c := by
      by_contra hn
      have ht := hneg (lt_of_not_ge hn)
      simp [hk] at ht
    simpa [hk] using mul_nonneg hc hw.1
  | true =>
    have hc : c ≤ 0 := by
      by_contra hn
      have ht := hpos (lt_of_not_ge hn)
      simp [hk] at ht
    simpa [hk] using mul_le_mul_of_nonpos_left hw.2 hc

private theorem sum_coefficient_mul_indicator_le {ι : Type*} [Fintype ι]
    (c w : ι → ℝ) (keep : ι → Bool) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (hneg : ∀ i, c i < 0 → keep i = true) (hpos : ∀ i, 0 < c i → keep i = false) :
    (∑ i, c i * (if keep i then 1 else 0)) ≤ ∑ i, c i * w i := by
  exact Finset.sum_le_sum fun i _ => coefficient_mul_indicator_le (hw i) (hneg i) (hpos i)

private theorem eq_indicator_of_sum_coefficient_mul_le {ι : Type*} [Fintype ι]
    (c w : ι → ℝ) (keep : ι → Bool) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (hneg : ∀ i, c i < 0 → keep i = true) (hpos : ∀ i, 0 < c i → keep i = false)
    (hc : ∀ i, c i ≠ 0)
    (hle : (∑ i, c i * w i) ≤ ∑ i, c i * (if keep i then 1 else 0)) :
    ∀ i, w i = if keep i then 1 else 0 := by
  have hn (i) : 0 ≤ c i * w i - c i * (if keep i then 1 else 0) :=
    sub_nonneg.mpr (coefficient_mul_indicator_le (hw i) (hneg i) (hpos i))
  have hsum : (∑ i, (c i * w i - c i * (if keep i then 1 else 0))) = 0 := by
    apply le_antisymm
    · simpa only [Finset.sum_sub_distrib, sub_nonpos] using hle
    · exact Finset.sum_nonneg fun i _ => hn i
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hsum i (Finset.mem_univ i)
  have hp : c i * (w i - (if keep i then 1 else 0)) = 0 := by nlinarith [hi]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (hc i))

private theorem IsSVD.projector_coordinates_are_projector {p q : ℕ} {Y : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD Y U V)
    {P : Matrix m m 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P) :
    (Uᴴ * P * U).IsHermitian ∧ IsIdempotentElem (Uᴴ * P * U) := by
  constructor
  · change (Uᴴ * P * U)ᴴ = Uᴴ * P * U
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs.eq,
      Matrix.mul_assoc]
  · change (Uᴴ * P * U) * (Uᴴ * P * U) = Uᴴ * P * U
    calc
      _ = Uᴴ * (P * (U * Uᴴ) * P) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h.mul_conjTranspose_left, Matrix.mul_one, show P * P = P from hp]

private theorem IsSVD.rankPenaltyObjective_rangeProjector_eq {p q : ℕ}
    {Y : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD Y U V) (μ : ℝ) (X : Matrix m n 𝕜) :
    rankPenaltyObjective μ Y X = 1 / 2 * frobSq Y +
      (∑ i : Fin p, (μ - 1 / 2 * singularValues Y i ^ 2) *
        RCLike.re ((Uᴴ * rangeProjector X * U) i i)) +
      1 / 2 * frobSq (rangeProjector X * Y - X) := by
  have hs := rangeProjector_isHermitian X
  have hp := rangeProjector_isIdempotentElem X
  have hError := frobSq_sub_eq_projector_error_add hs hp Y X (rangeProjector_mul X)
  have hCapture := h.frobSq_projector_mul_eq_sum hs hp
  have hTrace : (∑ i : Fin p, RCLike.re ((Uᴴ * rangeProjector X * U) i i)) = (X.rank : ℝ) := by
    rw [h.re_trace_conjTranspose_mul_mul, trace_eq_rank_of_isIdempotentElem _ hp,
      rank_rangeProjector, RCLike.natCast_re]
  have hSum : (∑ i : Fin p, (μ - 1 / 2 * singularValues Y i ^ 2) *
      RCLike.re ((Uᴴ * rangeProjector X * U) i i)) =
      μ * (∑ i : Fin p, RCLike.re ((Uᴴ * rangeProjector X * U) i i)) -
        1 / 2 * ∑ i : Fin p, singularValues Y i ^ 2 *
          RCLike.re ((Uᴴ * rangeProjector X * U) i i) := by
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [rankPenaltyObjective, hError, hSum, hTrace, ← hCapture]
  ring

private theorem IsSVD.rankPenaltyObjective_projector_mul_le {p q : ℕ}
    {Y : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD Y U V) {μ : ℝ} (hμ : 0 ≤ μ) {P : Matrix m m 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) :
    rankPenaltyObjective μ Y (P * Y) ≤ 1 / 2 * frobSq Y +
      ∑ i : Fin p, (μ - 1 / 2 * singularValues Y i ^ 2) *
        RCLike.re ((Uᴴ * P * U) i i) := by
  have hCapture := h.frobSq_projector_mul_eq_sum hs hp
  have hTrace : (∑ i : Fin p, RCLike.re ((Uᴴ * P * U) i i)) = (P.rank : ℝ) := by
    rw [h.re_trace_conjTranspose_mul_mul, trace_eq_rank_of_isIdempotentElem _ hp,
      RCLike.natCast_re]
  have hPyth := frobSq_projector_mul_add_complement hs hp Y
  have hRes : (1 - P) * Y = Y - P * Y := by rw [Matrix.sub_mul, Matrix.one_mul]
  rw [hRes] at hPyth
  have hSum : (∑ i : Fin p, (μ - 1 / 2 * singularValues Y i ^ 2) *
      RCLike.re ((Uᴴ * P * U) i i)) =
      μ * (∑ i : Fin p, RCLike.re ((Uᴴ * P * U) i i)) -
        1 / 2 * ∑ i : Fin p, singularValues Y i ^ 2 * RCLike.re ((Uᴴ * P * U) i i) := by
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [rankPenaltyObjective, hSum, hTrace, ← hCapture]
  have hr : ((P * Y).rank : ℝ) ≤ (P.rank : ℝ) := by
    exact_mod_cast Matrix.rank_mul_le_left P Y
  have hb := mul_le_mul_of_nonneg_left hr hμ
  linarith

private theorem IsSVD.rankPenaltyObjective_selected_le_sum {p q : ℕ}
    {Y : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD Y U V) {μ : ℝ} (hμ : 0 ≤ μ) (keep : Fin p → Bool) :
    rankPenaltyObjective μ Y (singularDirectionProjector U keep * Y) ≤
      1 / 2 * frobSq Y + ∑ i : Fin p, (μ - 1 / 2 * singularValues Y i ^ 2) *
        (if keep i then 1 else 0) := by
  have hUpper := h.rankPenaltyObjective_projector_mul_le hμ
    (singularDirectionProjector_isHermitian U keep)
    (HasOrthonormalCols.isIdempotentElem_singularDirectionProjector h.conjTranspose_mul_left keep)
  rw [HasOrthonormalCols.conjTranspose_mul_singularDirectionProjector_mul h.conjTranspose_mul_left] at hUpper
  simp only [Matrix.diagonal_apply_eq] at hUpper
  have hRe : ∀ i : Fin p, RCLike.re (if keep i then (1 : 𝕜) else 0) =
      if keep i then (1 : ℝ) else 0 := by intro i; split_ifs <;> simp
  simp only [hRe] at hUpper
  exact hUpper

/-- Every scalar-optimal mask of SVD directions is an actual global rank-penalized
minimizer. The mask is free at each threshold tie, so ties can be retained independently.
Fessler–Nadakuditi (2024), §7.5.3.
atlas: rank-penalty-thresholding (partial)-/
theorem IsSVD.rankPenaltyObjective_selected_le {p q : ℕ}
    {Y : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD Y U V) {μ : ℝ} (hμ : 0 ≤ μ) (keep : Fin p → Bool)
    (hneg : ∀ i : Fin p, μ - 1 / 2 * singularValues Y i ^ 2 < 0 → keep i = true)
    (hpos : ∀ i : Fin p, 0 < μ - 1 / 2 * singularValues Y i ^ 2 → keep i = false)
    (X : Matrix m n 𝕜) :
    rankPenaltyObjective μ Y (singularDirectionProjector U keep * Y) ≤
      rankPenaltyObjective μ Y X := by
  let c : Fin p → ℝ := fun i => μ - 1 / 2 * singularValues Y i ^ 2
  let R := Uᴴ * rangeProjector X * U
  have hR := h.projector_coordinates_are_projector (rangeProjector_isHermitian X)
    (rangeProjector_isIdempotentElem X)
  have hw : ∀ i, RCLike.re (R i i) ∈ Set.Icc (0 : ℝ) 1 :=
    re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem R hR.1 hR.2
  have hbox := sum_coefficient_mul_indicator_le c (fun i => RCLike.re (R i i)) keep hw hneg hpos
  have hUpper := h.rankPenaltyObjective_selected_le_sum hμ keep
  rw [h.rankPenaltyObjective_rangeProjector_eq μ X]
  have hrem := frobSq_nonneg (rangeProjector X * Y - X)
  change (∑ i, c i * (if keep i then 1 else 0)) ≤ ∑ i, c i * RCLike.re (R i i) at hbox
  change rankPenaltyObjective μ Y (singularDirectionProjector U keep * Y) ≤
    1 / 2 * frobSq Y + ∑ i, c i * (if keep i then 1 else 0) at hUpper
  change rankPenaltyObjective μ Y (singularDirectionProjector U keep * Y) ≤
    1 / 2 * frobSq Y + (∑ i, c i * RCLike.re (R i i)) +
      1 / 2 * frobSq (rangeProjector X * Y - X)
  linarith

/-- With no zero coefficient, an optimal SVD direction mask determines the unique
matrix minimizer. The proof forces the actual range projector and its fitted output. -/
theorem IsSVD.eq_selected_of_rankPenaltyObjective_le {p q : ℕ}
    {Y : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD Y U V) {μ : ℝ} (hμ : 0 ≤ μ) (keep : Fin p → Bool)
    (hneg : ∀ i : Fin p, μ - 1 / 2 * singularValues Y i ^ 2 < 0 → keep i = true)
    (hpos : ∀ i : Fin p, 0 < μ - 1 / 2 * singularValues Y i ^ 2 → keep i = false)
    (hc : ∀ i : Fin p, μ - 1 / 2 * singularValues Y i ^ 2 ≠ 0)
    (X : Matrix m n 𝕜)
    (hX : rankPenaltyObjective μ Y X ≤
      rankPenaltyObjective μ Y (singularDirectionProjector U keep * Y)) :
    X = singularDirectionProjector U keep * Y := by
  let c : Fin p → ℝ := fun i => μ - 1 / 2 * singularValues Y i ^ 2
  let R := Uᴴ * rangeProjector X * U
  have hR := h.projector_coordinates_are_projector (rangeProjector_isHermitian X)
    (rangeProjector_isIdempotentElem X)
  have hw : ∀ i, RCLike.re (R i i) ∈ Set.Icc (0 : ℝ) 1 :=
    re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem R hR.1 hR.2
  have hLower := sum_coefficient_mul_indicator_le c (fun i => RCLike.re (R i i)) keep hw hneg hpos
  have hUpper := h.rankPenaltyObjective_selected_le_sum hμ keep
  have hObj := h.rankPenaltyObjective_rangeProjector_eq μ X
  change rankPenaltyObjective μ Y X = 1 / 2 * frobSq Y +
    (∑ i, c i * RCLike.re (R i i)) + 1 / 2 * frobSq (rangeProjector X * Y - X) at hObj
  change rankPenaltyObjective μ Y (singularDirectionProjector U keep * Y) ≤
    1 / 2 * frobSq Y + ∑ i, c i * (if keep i then 1 else 0) at hUpper
  have hrem := frobSq_nonneg (rangeProjector X * Y - X)
  have hCost : (∑ i, c i * RCLike.re (R i i)) ≤
      ∑ i, c i * (if keep i then 1 else 0) := by linarith
  have hSq : frobSq (rangeProjector X * Y - X) ≤ 0 := by linarith
  have hFit : rangeProjector X * Y = X :=
    sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp (le_antisymm hSq hrem))
  have hdiag := eq_indicator_of_sum_coefficient_mul_le c
    (fun i => RCLike.re (R i i)) keep hw hneg hpos hc hCost
  have hRdiag := hR.1.eq_diagonal_of_isIdempotentElem_of_re_diag hR.2 keep hdiag
  change R = Matrix.diagonal (fun i => if keep i then (1 : 𝕜) else 0) at hRdiag
  have hP : rangeProjector X = singularDirectionProjector U keep := by
    calc
      _ = (U * Uᴴ) * rangeProjector X * (U * Uᴴ) := by
        rw [h.mul_conjTranspose_left, Matrix.one_mul, Matrix.mul_one]
      _ = U * R * Uᴴ := by simp only [R, Matrix.mul_assoc]
      _ = _ := by rw [hRdiag]; rfl
  rw [← hFit, hP]

/-- Every full SVD realizes the strict hard-threshold selector. -/
theorem IsSVD.singularValueHardThreshold_eq {p q : ℕ} {Y : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD Y U V) (μ : ℝ) :
    singularValueHardThreshold μ Y = U *
      (rectDiag (fun i => if Real.sqrt (2 * μ) < singularValues Y i then singularValues Y i else 0) :
        Matrix (Fin p) (Fin q) 𝕜) * Vᴴ := by
  exact h.singularValueTransform_eq
    (φ := fun s => if Real.sqrt (2 * μ) < s then s else 0)
    (by split_ifs <;> rfl)

private theorem IsSVD.singularDirectionProjector_mul_eq_hardThreshold {p q : ℕ}
    {Y : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD Y U V) (μ : ℝ) :
    singularDirectionProjector U (fun i => decide (Real.sqrt (2 * μ) < singularValues Y i)) * Y =
      singularValueHardThreshold μ Y := by
  rw [h.singularValueHardThreshold_eq μ]
  conv_lhs => rhs; rw [h.eq]
  simp only [singularDirectionProjector, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, h.conjTranspose_mul_left, Matrix.one_mul]
  have hd : (Matrix.diagonal (fun i : Fin p =>
      if decide (Real.sqrt (2 * μ) < singularValues Y i) then (1 : 𝕜) else 0)) *
      (rectDiag (singularValues Y) : Matrix (Fin p) (Fin q) 𝕜) =
      rectDiag (fun i => if Real.sqrt (2 * μ) < singularValues Y i then singularValues Y i else 0) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [rectDiag_apply_ofReal, decide_eq_true_eq]
    by_cases hij : (i : ℕ) = j
    · rw [if_pos hij, if_pos hij]
      by_cases ht : Real.sqrt (2 * μ) < singularValues Y i
      · simp only [if_pos ht, one_mul]
      · simp only [if_neg ht, zero_mul, RCLike.ofReal_zero]
    · simp only [if_neg hij, mul_zero]
  simpa only [Matrix.mul_assoc] using congrArg (fun M => U * M * Vᴴ) hd

private theorem hardThresholdMask_sign {s μ : ℝ} (hs : 0 ≤ s) (hμ : 0 ≤ μ) :
    (μ - 1 / 2 * s ^ 2 < 0 → decide (Real.sqrt (2 * μ) < s) = true) ∧
    (0 < μ - 1 / 2 * s ^ 2 → decide (Real.sqrt (2 * μ) < s) = false) := by
  have hθ := Real.sqrt_nonneg (2 * μ)
  have hθsq := Real.sq_sqrt (show 0 ≤ 2 * μ by positivity)
  constructor
  · intro h
    have ht : Real.sqrt (2 * μ) < s := by nlinarith
    simpa only [decide_eq_true_eq] using ht
  · intro h
    have ht : ¬Real.sqrt (2 * μ) < s := by nlinarith
    simpa only [decide_eq_false_iff_not] using ht

private theorem hardThreshold_coefficient_ne_zero {s μ : ℝ}
    (hs : 0 ≤ s) (hμ : 0 ≤ μ) (hne : s ≠ Real.sqrt (2 * μ)) :
    μ - 1 / 2 * s ^ 2 ≠ 0 := by
  intro heq
  have hθ := Real.sqrt_nonneg (2 * μ)
  have hθsq := Real.sq_sqrt (show 0 ≤ 2 * μ by positivity)
  apply hne
  nlinarith

/-- Strict hard thresholding gives a global minimizer for every nonnegative rank penalty,
including zero, zero input, repeated singular values, and threshold ties (discarded by the selector).
Fessler–Nadakuditi (2024), §7.5.3, equation (7.34).
atlas: rank-penalty-thresholding (partial)-/
theorem rankPenaltyObjective_hardThreshold_le (Y X : Matrix m n 𝕜)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    rankPenaltyObjective μ Y (singularValueHardThreshold μ Y) ≤ rankPenaltyObjective μ Y X := by
  obtain ⟨U, V, h⟩ := exists_isSVD Y
  have hp := h.rankPenaltyObjective_selected_le hμ
    (fun i => decide (Real.sqrt (2 * μ) < singularValues Y i))
    (fun i => (hardThresholdMask_sign (singularValues_nonneg Y i) hμ).1)
    (fun i => (hardThresholdMask_sign (singularValues_nonneg Y i) hμ).2) X
  rwa [h.singularDirectionProjector_mul_eq_hardThreshold μ] at hp

/-- Away from threshold ties, the strict hard-threshold output is the unique minimizing
matrix. This forces the actual competitor's range projector; it does not assume aligned SVDs.
Fessler–Nadakuditi (2024), §7.5.3.
atlas: rank-penalty-thresholding (partial) -/
theorem eq_hardThreshold_of_rankPenaltyObjective_le (Y X : Matrix m n 𝕜)
    {μ : ℝ} (hμ : 0 < μ) (hNoTie : ∀ i, singularValues Y i ≠ Real.sqrt (2 * μ))
    (hX : rankPenaltyObjective μ Y X ≤
      rankPenaltyObjective μ Y (singularValueHardThreshold μ Y)) :
    X = singularValueHardThreshold μ Y := by
  obtain ⟨U, V, h⟩ := exists_isSVD Y
  have hp := h.eq_selected_of_rankPenaltyObjective_le hμ.le
    (fun i => decide (Real.sqrt (2 * μ) < singularValues Y i))
    (fun i => (hardThresholdMask_sign (singularValues_nonneg Y i) hμ.le).1)
    (fun i => (hardThresholdMask_sign (singularValues_nonneg Y i) hμ.le).2)
    (fun i => hardThreshold_coefficient_ne_zero (singularValues_nonneg Y i) hμ.le (hNoTie i)) X
    (by simpa only [h.singularDirectionProjector_mul_eq_hardThreshold μ] using hX)
  rwa [h.singularDirectionProjector_mul_eq_hardThreshold μ] at hp

/-- The exact no-tie minimizer characterization for the rank-penalized objective.
Fessler–Nadakuditi (2024), §7.5.3.
atlas: rank-penalty-thresholding (partial)-/
theorem rankPenaltyObjective_hardThreshold_minimizer_iff (Y X : Matrix m n 𝕜)
    {μ : ℝ} (hμ : 0 < μ) (hNoTie : ∀ i, singularValues Y i ≠ Real.sqrt (2 * μ)) :
    (∀ Z, rankPenaltyObjective μ Y X ≤ rankPenaltyObjective μ Y Z) ↔
      X = singularValueHardThreshold μ Y := by
  constructor
  · intro h
    exact eq_hardThreshold_of_rankPenaltyObjective_le Y X hμ hNoTie (h _)
  · rintro rfl
    exact fun Z => rankPenaltyObjective_hardThreshold_le Y Z hμ.le

omit [DecidableEq m] [DecidableEq n] in
/-- At zero rank penalty the unique minimizer is the original matrix, including
rank-deficient and empty inputs. Fessler–Nadakuditi (2024), equation (7.28), endpoint.
atlas: rank-penalty-thresholding (partial)-/
theorem rankPenaltyObjective_zero_minimizer_iff (Y X : Matrix m n 𝕜) :
    (∀ Z, rankPenaltyObjective 0 Y X ≤ rankPenaltyObjective 0 Y Z) ↔ X = Y := by
  constructor
  · intro h
    have hY := h Y
    simp only [rankPenaltyObjective, sub_self, frobSq_zero, mul_zero, zero_mul, add_zero] at hY
    have hzero : frobSq (Y - X) = 0 := by nlinarith [frobSq_nonneg (Y - X)]
    exact (sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp hzero)).symm
  · rintro rfl Z
    simp only [rankPenaltyObjective, sub_self, frobSq_zero, mul_zero, zero_mul, add_zero]
    exact mul_nonneg (by norm_num) (frobSq_nonneg _)

/-- A zero rank penalty makes the strict hard-threshold selector return the input.
Fessler–Nadakuditi (2024), equation (7.28), endpoint.
atlas: rank-penalty-thresholding (partial) -/
@[simp] theorem singularValueHardThreshold_zero (Y : Matrix m n 𝕜) :
    singularValueHardThreshold 0 Y = Y := by
  exact (rankPenaltyObjective_zero_minimizer_iff Y _).mp
    (fun Z => rankPenaltyObjective_hardThreshold_le Y Z le_rfl)

end NLAlib
