import NLAlib.Matrix.Norms.SchattenComparison

/-!
# Normalized Schatten singular coefficients

A nonzero matrix's singular values divided by its Schatten norm have unit
source power sum. Their dual powers attain the original norm in the scalar
singular-value pairing. All formulas include zero singular directions.
-/

noncomputable section
namespace NLAlib

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- A nonzero matrix has strictly positive finite Schatten norm at every
positive exponent. -/
theorem schattenNormReal_pos (A : Matrix m n 𝕜) {p : ℝ} (hp : 0 < p) (hA : A ≠ 0) :
    0 < schattenNormReal A p :=
  lt_of_le_of_ne (schattenNormReal_nonneg A p)
    (Ne.symm (fun h => hA ((schattenNormReal_eq_zero_iff A hp).mp h)))

omit [DecidableEq m] in
/-- Raising a positive-exponent Schatten norm to its exponent recovers the
full singular-value power sum. -/
theorem schattenNormReal_rpow_eq_sum (A : Matrix m n 𝕜) {p : ℝ} (hp : 0 < p) :
    schattenNormReal A p ^ p =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ p := by
  rw [schattenNormReal, one_div]
  exact Real.rpow_inv_rpow
    (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (singularValues_nonneg A i) p) hp.ne'

/-- Every normalized singular coefficient belongs to the unit interval. -/
theorem singularValues_div_schattenNormReal_mem_Icc (A : Matrix m n 𝕜)
    {p : ℝ} (hp : 0 < p) (hA : A ≠ 0) (i : ℕ) :
    singularValues A i / schattenNormReal A p ∈ Set.Icc (0 : ℝ) 1 := by
  have hC := schattenNormReal_pos A hp hA
  exact ⟨div_nonneg (singularValues_nonneg A i) hC.le,
    (div_le_one hC).mpr ((singularValues_le_specNorm A i).trans (specNorm_le_schattenNormReal A hp))⟩

omit [DecidableEq m] in
/-- Normalizing by the Schatten norm makes the source powers sum to one. -/
theorem sum_singularValues_div_schattenNormReal_rpow_eq_one (A : Matrix m n 𝕜)
    {p : ℝ} (hp : 0 < p) (hA : A ≠ 0) :
    (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i / schattenNormReal A p) ^ p) = 1 := by
  have hC := schattenNormReal_pos A hp hA
  simp_rw [Real.div_rpow (singularValues_nonneg A _) hC.le]
  rw [← Finset.sum_div, ← schattenNormReal_rpow_eq_sum A hp,
    div_self (Real.rpow_pos_of_pos hC p).ne']

omit [DecidableEq m] in
/-- The normalized singular dual powers recover the original Schatten norm
in the scalar singular-value pairing. -/
theorem sum_singularValues_mul_normalized_rpow_eq_schattenNormReal
    (A : Matrix m n 𝕜) {p : ℝ} (hp : 1 < p) (hA : A ≠ 0) :
    (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * (singularValues A i / schattenNormReal A p) ^ (p - 1)) =
      schattenNormReal A p := by
  have hp0 := lt_trans zero_lt_one hp
  have hC := schattenNormReal_pos A hp0 hA
  have hterm (i : ℕ) :
      singularValues A i * (singularValues A i / schattenNormReal A p) ^ (p - 1) =
        schattenNormReal A p * (singularValues A i / schattenNormReal A p) ^ p := by
    let w := singularValues A i / schattenNormReal A p
    have hw : 0 ≤ w := div_nonneg (singularValues_nonneg A i) hC.le
    have hσ : singularValues A i = schattenNormReal A p * w := by dsimp [w]; field_simp
    have hprod : w * w ^ (p - 1) = w ^ p := by
      calc
        _ = w ^ (1 : ℝ) * w ^ (p - 1) := by rw [Real.rpow_one]
        _ = w ^ (1 + (p - 1)) :=
          (Real.rpow_add_of_nonneg hw zero_le_one (sub_nonneg.mpr hp.le)).symm
        _ = _ := by congr 1; ring
    change singularValues A i * w ^ (p - 1) = schattenNormReal A p * w ^ p
    rw [hσ, mul_assoc, hprod]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_singularValues_div_schattenNormReal_rpow_eq_one A hp0 hA, mul_one]

end NLAlib
