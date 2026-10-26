import NLAlib.Matrix.Spectral.WeightedResolvent
import NLAlib.Matrix.Basic.RankOneInverse
import NLAlib.Matrix.Basic.QuadForm

/-!
# Choosing a column for a weighted lower barrier

The averaging step selects one actual column from a decomposition of a PSD
matrix. Its interaction with the indefinite resolvent is strictly below `-1`,
and Sherman--Morrison preserves the weighted potential. Source:
Spielman--Srivastava (2009), Theorem 2.
-/

noncomputable section

open scoped Matrix BigOperators MatrixOrder
open Matrix

namespace NLAlib.RestrictedInvertibility

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem sum_quadForm_eq_trace_mul (v : I → n → ℝ) (H R : Matrix n n ℝ)
    (hH : ∑ i, vecMulVec (v i) (v i) = H) :
    ∑ i, quadForm R (v i) = (R * H).trace := by
  calc
    _ = ∑ i, (R * vecMulVec (v i) (v i)).trace := by
      apply Finset.sum_congr rfl
      intro i _
      simp [quadForm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
    _ = (R * ∑ i, vecMulVec (v i) (v i)).trace := by
      rw [Finset.mul_sum, Matrix.trace_sum]
    _ = _ := by rw [hH]

omit [DecidableEq n] in
private theorem rank_one_le_decomposition (v : I → n → ℝ) (H : Matrix n n ℝ)
    (hH : ∑ i, vecMulVec (v i) (v i) = H) (i : I) :
    (H - vecMulVec (v i) (v i)).PosSemidef := by
  classical
  have hsum := Finset.sum_erase_add (Finset.univ : Finset I)
    (fun j => vecMulVec (v j) (v j)) (Finset.mem_univ i)
  have heq : H - vecMulVec (v i) (v i) =
      ∑ j ∈ Finset.univ.erase i, vecMulVec (v j) (v j) := by
    rw [← hH, ← hsum]
    simp
  rw [heq]
  exact Matrix.posSemidef_sum _ fun j _ => by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v j)

omit [DecidableEq n] in
private theorem interaction_sq_le_weighted_quadForm
    (v : I → n → ℝ) (H R : Matrix n n ℝ)
    (hH : ∑ i, vecMulVec (v i) (v i) = H) (hR : R.IsHermitian) (i : I) :
    (quadForm R (v i)) ^ 2 ≤ quadForm (R * H * R) (v i) := by
  have hp := (rank_one_le_decomposition v H hH i).quadForm_nonneg (R *ᵥ v i)
  have hcong : quadForm (R * H * R) (v i) = quadForm H (R *ᵥ v i) := by
    have hh := quadForm_conjTranspose_mul_mul H R (v i)
    simpa only [hR.eq] using hh
  rw [hcong]
  have hid : quadForm (H - vecMulVec (v i) (v i)) (R *ᵥ v i) =
      quadForm H (R *ᵥ v i) - quadForm R (v i) ^ 2 := by
    simp only [quadForm, star_trivial, Matrix.sub_mulVec, dotProduct_sub,
      Matrix.vecMulVec_mulVec, dotProduct_smul]
    simp only [op_smul_eq_mul]
    rw [dotProduct_comm (R *ᵥ v i) (v i)]
    ring
  rw [hid] at hp
  linarith

/-- Finite averaging yields a genuine column whose interaction with the new
resolvent is strictly below `-1`. The strictness follows from the actual
decomposition `H = ∑ vᵢvᵢᵀ`, rather than a non-strict scalar certificate.
Source: Spielman--Srivastava (2009), Theorem 2. -/
theorem exists_column_interaction_lt_neg_one
    [Nonempty I] (v : I → n → ℝ) {H R : Matrix n n ℝ}
    (hH : ∑ i, vecMulVec (v i) (v i) = H)
    (hHpos : H.PosSemidef) (hR : R.IsHermitian)
    {Δ Λ δ φ : ℝ} (hΔ : 0 < Δ) (_hΛ : 0 < Λ) (_hδ : 0 < δ)
    (hHle : H ≤ Λ • (1 : Matrix n n ℝ))
    (htrace : (H * R).trace = φ - Δ)
    (hpot : φ ≤ -(Fintype.card I : ℝ) - Λ / δ)
    (hsq : Λ * (H * R ^ 2).trace ≤ Δ * (Λ / δ + Δ)) :
    ∃ i, quadForm R (v i) < -1 ∧
      quadForm (R * H * R) (v i) ≤ Δ * (-1 - quadForm R (v i)) := by
  have hRHR : (R * H * R).PosSemidef := by
    simpa only [hR.eq] using hHpos.conjTranspose_mul_mul_same R
  have hsumN : (∑ i, quadForm (R * H * R) (v i)) ≤
      Λ * (H * R ^ 2).trace := by
    rw [sum_quadForm_eq_trace_mul v H (R * H * R) hH]
    have hh := trace_mul_le_trace_mul_of_posSemidef hRHR hHle
    have ht : ((R * H * R) * (Λ • (1 : Matrix n n ℝ))).trace =
        Λ * (H * R ^ 2).trace := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
      congr 1
      rw [pow_two, Matrix.trace_mul_cycle]
      exact Matrix.trace_mul_comm _ _
    exact ht ▸ hh
  have hsumQ : (∑ i, quadForm R (v i)) = φ - Δ := by
    rw [sum_quadForm_eq_trace_mul v H R hH, Matrix.trace_mul_comm, htrace]
  have hsumR : (∑ i, Δ * (-1 - quadForm R (v i))) =
      Δ * (-(Fintype.card I : ℝ) - (φ - Δ)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsumQ]
    simp
  have hsum : (∑ i, quadForm (R * H * R) (v i)) ≤
      ∑ i, Δ * (-1 - quadForm R (v i)) := by
    rw [hsumR]
    calc
      _ ≤ Λ * (H * R ^ 2).trace := hsumN
      _ ≤ Δ * (Λ / δ + Δ) := hsq
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hΔ.le
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨i, ?_, hi⟩
  have hq := interaction_sq_le_weighted_quadForm v H R hH hR i
  have hnon : 0 ≤ quadForm (R * H * R) (v i) := hRHR.quadForm_nonneg _
  have hle : quadForm R (v i) ≤ -1 := by nlinarith
  by_contra hnot
  have heq : quadForm R (v i) = -1 := le_antisymm hle (not_lt.mp hnot)
  rw [heq] at hi hq
  nlinarith

/-- The selected column preserves the weighted potential at the decreased
barrier. Invertibility and the strict interaction are explicit, so the total
matrix inverse is used only on its valid branch. Source:
Spielman--Srivastava (2009), Theorem 2, Sherman--Morrison step. -/
theorem lowerPotential_add_vecMulVec_le
    {A H : Matrix n n ℝ} {b Δ φ : ℝ} (v : n → ℝ)
    (hunit : IsUnit (A - b • (1 : Matrix n n ℝ)))
    (_hΔ : 0 < Δ)
    (htrace : lowerPotential H A b = φ - Δ)
    (hinteraction : quadForm (A - b • (1 : Matrix n n ℝ))⁻¹ v < -1)
    (hcert : quadForm ((A - b • (1 : Matrix n n ℝ))⁻¹ * H *
        (A - b • (1 : Matrix n n ℝ))⁻¹) v ≤
      Δ * (-1 - quadForm (A - b • (1 : Matrix n n ℝ))⁻¹ v)) :
    lowerPotential H (A + vecMulVec v v) b ≤ φ := by
  let R : Matrix n n ℝ := (A - b • (1 : Matrix n n ℝ))⁻¹
  let q : ℝ := quadForm R v
  have hd : 1 + q < 0 := by dsimp [q, R]; linarith
  have hinv := Matrix.trace_mul_inv_add_smul_vecMulVec_self
    (A - b • (1 : Matrix n n ℝ)) H v 1
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
    (show 1 + 1 * (v ⬝ᵥ ((A - b • (1 : Matrix n n ℝ))⁻¹ *ᵥ v)) ≠ 0 by
      simpa [q, R, quadForm, star_trivial] using ne_of_lt hd)
  have hh : lowerPotential H (A + vecMulVec v v) b =
      (φ - Δ) - quadForm (R * H * R) v / (1 + q) := by
    have hmat : A + vecMulVec v v - b • (1 : Matrix n n ℝ) =
        A - b • (1 : Matrix n n ℝ) + (1 : ℝ) • vecMulVec v v := by module
    unfold lowerPotential
    rw [hmat]
    calc
      _ = _ := hinv
      _ = _ := by
        change lowerPotential H A b -
          (1 / (1 + 1 * q)) * quadForm (R * H * R) v = _
        rw [htrace]
        ring
  rw [hh]
  have hquot : -Δ ≤ quadForm (R * H * R) v / (1 + q) := by
    apply (le_div_iff_of_neg hd).mpr
    dsimp [R, q] at *
    nlinarith
  linarith

end NLAlib.RestrictedInvertibility
