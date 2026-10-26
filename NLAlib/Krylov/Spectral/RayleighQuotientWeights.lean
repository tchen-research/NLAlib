import NLAlib.Krylov.Spectral.RayleighQuotientBounds

/-!
# Finite spectral-weight estimates for Rayleigh quotient iteration

The weights are squared absolute eigenvector coordinates. The estimates retain the exact
denominator in the Rayleigh quotient bound, and the distance to the shifted spectrum in the
inverse-step bound. Source: Trefethen–Bau (1997), Lecture 27.
-/

namespace NLAlib.RayleighQuotientIteration

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The error of a weighted spectral average is controlled by the weight away from a
distinguished eigenvalue. Helper for the Hermitian RQI estimate. -/
theorem abs_weighted_average_sub_le {lam w : n → ℝ} {i : n} {M : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hi : 0 < w i)
    (hM : ∀ j, j ≠ i → |lam j - lam i| ≤ M) :
    |(∑ j, lam j * w j) / (∑ j, w j) - lam i| ≤
      M * ((∑ j ∈ Finset.univ.erase i, w j) / w i) /
        (1 + (∑ j ∈ Finset.univ.erase i, w j) / w i) := by
  let s := ∑ j ∈ Finset.univ.erase i, w j
  have hs : 0 ≤ s := Finset.sum_nonneg fun j _ => hw j
  have hsum : ∑ j, w j = w i + s := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact add_comm _ _
  have hpos : 0 < ∑ j, w j := by rw [hsum]; positivity
  have herr : (∑ j, lam j * w j) / (∑ j, w j) - lam i =
      (∑ j ∈ Finset.univ.erase i, (lam j - lam i) * w j) / (∑ j, w j) := by
    have heq : (∑ j ∈ Finset.univ.erase i, (lam j - lam i) * w j) =
        (∑ j, lam j * w j) - lam i * (∑ j, w j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [← sub_mul]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp
    rw [heq]
    field_simp
  have habs : |∑ j ∈ Finset.univ.erase i, (lam j - lam i) * w j| ≤ M * s := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |(lam j - lam i) * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, M * w j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_right (hM j (Finset.mem_erase.mp hj).1) (hw j)
      _ = M * s := (Finset.mul_sum _ _ _).symm
  rw [herr, abs_div, abs_of_pos hpos]
  calc
    _ ≤ M * s / (∑ j, w j) := div_le_div_of_nonneg_right habs hpos.le
    _ = M * (s / w i) / (1 + s / w i) := by
      rw [hsum]
      have hd : 1 + s / w i ≠ 0 := ne_of_gt (by positivity)
      field_simp

/-- In an extremal spectrum the Rayleigh error also controls the off-axis spectral
weight from below. The lower-spectrum version suffices; negating the eigenvalues gives
the upper-spectrum version. -/
theorem gap_mul_weight_ratio_le_weighted_average_sub {lam w : n → ℝ} {i : n} {g : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hi : 0 < w i)
    (hg : ∀ j, j ≠ i → g ≤ lam j - lam i) :
    g * ((∑ j ∈ Finset.univ.erase i, w j) / w i) /
        (1 + (∑ j ∈ Finset.univ.erase i, w j) / w i) ≤
      (∑ j, lam j * w j) / (∑ j, w j) - lam i := by
  let s := ∑ j ∈ Finset.univ.erase i, w j
  have hs : 0 ≤ s := Finset.sum_nonneg fun j _ => hw j
  have hsum : ∑ j, w j = w i + s := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact add_comm _ _
  have hpos : 0 < ∑ j, w j := by rw [hsum]; positivity
  have hbound : g * s ≤ ∑ j ∈ Finset.univ.erase i, (lam j - lam i) * w j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (hg j (Finset.mem_erase.mp hj).1) (hw j)
  have heq : (∑ j ∈ Finset.univ.erase i, (lam j - lam i) * w j) =
      (∑ j, lam j * w j) - lam i * (∑ j, w j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp
  calc
    _ = g * s / (∑ j, w j) := by
      change g * (s / w i) / (1 + s / w i) = g * s / (∑ j, w j)
      rw [hsum]
      have hd : 1 + s / w i ≠ 0 := ne_of_gt (by positivity)
      field_simp
    _ ≤ ((∑ j, lam j * w j) - lam i * (∑ j, w j)) / (∑ j, w j) := by
      apply div_le_div_of_nonneg_right _ hpos.le
      rwa [← heq]
    _ = _ := by field_simp

/-- Reweighting by reciprocal squared shifted eigenvalues contracts the ratio of
off-axis to target weight by the squared spectral separation ratio. -/
theorem inverse_weight_ratio_le {w a : n → ℝ} {i : n} {d : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hi : 0 < w i) (hai : a i ≠ 0) (hd : 0 < d)
    (ha : ∀ j, j ≠ i → d ≤ |a j|) :
    (∑ j ∈ Finset.univ.erase i, w j / a j ^ 2) / (w i / a i ^ 2) ≤
      (|a i| / d) ^ 2 * ((∑ j ∈ Finset.univ.erase i, w j) / w i) := by
  have hsum : (∑ j ∈ Finset.univ.erase i, w j / a j ^ 2) ≤
      (∑ j ∈ Finset.univ.erase i, w j) / d ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    apply div_le_div_of_nonneg_left (hw j) (sq_pos_of_pos hd)
    have h := ha j (Finset.mem_erase.mp hj).1
    nlinarith [sq_abs (a j)]
  calc
    _ ≤ ((∑ j ∈ Finset.univ.erase i, w j) / d ^ 2) / (w i / a i ^ 2) :=
      div_le_div_of_nonneg_right hsum (div_nonneg hi.le (sq_nonneg _))
    _ = _ := by rw [div_pow, sq_abs]; field_simp

end NLAlib.RayleighQuotientIteration
