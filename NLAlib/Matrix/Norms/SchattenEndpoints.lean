import NLAlib.Matrix.Norms.SchattenProducts
import NLAlib.Matrix.Norms.SchattenTrace
/-!
# Extended Schatten Hölder endpoints

Infinity is treated explicitly and all finite exponents are transported from
the exact real-exponent power formulas. All product and trace constants are one.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix ENNReal

namespace NLAlib

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq q]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- The `(p,∞,p)` Schatten product endpoint for every positive finite exponent,
with exact constant one and all rank/empty-dimension cases. -/
theorem schattenNormReal_mul_le_mul_specNorm {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (B : Matrix n q 𝕜)
    {p : ℝ} (hp : 0 < p) : schattenNormReal (A * B) p ≤ schattenNormReal A p * specNorm B := by
  let N := max (min (Fintype.card m) (Fintype.card n)) (min (Fintype.card m) (Fintype.card q))
  have hNA : min (Fintype.card m) (Fintype.card n) ≤ N := le_max_left _ _
  have hNAB : min (Fintype.card m) (Fintype.card q) ≤ N := le_max_right _ _
  have hSA : 0 ≤ ∑ i ∈ Finset.range N, singularValues A i ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg _ i) p
  have hpow : (∑ i ∈ Finset.range N, singularValues (A * B) i ^ p) ≤
      specNorm B ^ p * ∑ i ∈ Finset.range N, singularValues A i ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ (singularValues A i * specNorm B) ^ p :=
        Real.rpow_le_rpow (singularValues_nonneg _ i)
          (singularValues_mul_le_mul_specNorm A B i) hp.le
      _ = _ := by rw [Real.mul_rpow (singularValues_nonneg _ i) (specNorm_nonneg B)]; ring
  rw [schattenNormReal_eq_sum_range_rpow_of_min_le (A * B) hNAB hp,
    schattenNormReal_eq_sum_range_rpow_of_min_le A hNA hp]
  calc
    _ ≤ (specNorm B ^ p * ∑ i ∈ Finset.range N, singularValues A i ^ p) ^ (1 / p) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValues_nonneg _ i) p) hpow (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg (specNorm_nonneg B) p) hSA, one_div,
        Real.rpow_rpow_inv (specNorm_nonneg B) hp.ne', mul_comm]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- The `(∞,p,p)` Schatten product endpoint for every positive finite exponent,
with exact constant one and all rank/empty-dimension cases. -/
theorem schattenNormReal_mul_le_specNorm_mul {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (B : Matrix n q 𝕜)
    {p : ℝ} (hp : 0 < p) : schattenNormReal (A * B) p ≤ specNorm A * schattenNormReal B p := by
  let N := max (min (Fintype.card n) (Fintype.card q)) (min (Fintype.card m) (Fintype.card q))
  have hNB : min (Fintype.card n) (Fintype.card q) ≤ N := le_max_left _ _
  have hNAB : min (Fintype.card m) (Fintype.card q) ≤ N := le_max_right _ _
  have hSB : 0 ≤ ∑ i ∈ Finset.range N, singularValues B i ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg _ i) p
  have hpow : (∑ i ∈ Finset.range N, singularValues (A * B) i ^ p) ≤
      specNorm A ^ p * ∑ i ∈ Finset.range N, singularValues B i ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ (specNorm A * singularValues B i) ^ p :=
        Real.rpow_le_rpow (singularValues_nonneg _ i)
          (singularValues_mul_le_specNorm_mul A B i) hp.le
      _ = _ := Real.mul_rpow (specNorm_nonneg A) (singularValues_nonneg _ i)
  rw [schattenNormReal_eq_sum_range_rpow_of_min_le (A * B) hNAB hp,
    schattenNormReal_eq_sum_range_rpow_of_min_le B hNB hp]
  calc
    _ ≤ (specNorm A ^ p * ∑ i ∈ Finset.range N, singularValues B i ^ p) ^ (1 / p) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValues_nonneg _ i) p) hpow (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg (specNorm_nonneg A) p) hSB, one_div,
        Real.rpow_rpow_inv (specNorm_nonneg A) hp.ne']

open scoped Matrix.Norms.L2Operator in
/-- Full Schatten product Hölder for extended norm exponents, including all
infinity endpoints. The reciprocal identity is Mathlib's `HolderTriple`.
atlas: schatten-norms-def -/
theorem schattenNorm_mul_le_mul (A : Matrix m n ℝ) (B : Matrix n q ℝ)
    {p s r : ℝ≥0∞} [ENNReal.HolderTriple p s r] (hp : 1 ≤ p) (hs : 1 ≤ s) (_hr : 1 ≤ r) :
    schattenNorm (A * B) r ≤ schattenNorm A p * schattenNorm B s := by
  by_cases hpTop : p = ∞
  · subst p
    have hr : r = s := ENNReal.HolderTriple.unique ∞ s r s
    subst r
    rw [schattenNorm_top]
    by_cases hsTop : s = ∞
    · subst s
      simp only [schattenNorm_top]
      exact specNorm_mul_le A B
    · rw [schattenNorm_eq_of_ne_top _ hsTop, schattenNorm_eq_of_ne_top _ hsTop]
      exact schattenNormReal_mul_le_specNorm_mul A B (ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hs)) hsTop)
  · by_cases hsTop : s = ∞
    · subst s
      have hr : r = p := ENNReal.HolderTriple.unique p ∞ r p
      subst r
      rw [schattenNorm_top, schattenNorm_eq_of_ne_top _ hpTop,
        schattenNorm_eq_of_ne_top _ hpTop]
      exact schattenNormReal_mul_le_mul_specNorm A B (ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpTop)
    · have hp0 := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpTop
      have hs0 := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hs)) hsTop
      have hreal := ENNReal.HolderTriple.toReal r hp0 hs0
      have hrTop : r ≠ ∞ := (ENNReal.toReal_pos_iff.mp hreal.pos').2.ne
      rw [schattenNorm_eq_of_ne_top _ hrTop, schattenNorm_eq_of_ne_top _ hpTop,
        schattenNorm_eq_of_ne_top _ hsTop]
      exact schattenNormReal_mul_le_mul A B hreal

open scoped Matrix.Norms.L2Operator in
omit [Fintype q] [DecidableEq q] in
/-- Full trace Hölder for extended conjugate Schatten exponents, including
both `(1,∞)` and `(∞,1)` endpoints and every empty matrix shape.
atlas: schatten-norms-def -/
theorem abs_frobInner_le_schattenNorm_mul (A B : Matrix m n ℝ)
    {p s : ℝ≥0∞} [ENNReal.HolderConjugate p s] :
    |frobInner A B| ≤ schattenNorm A p * schattenNorm B s := by
  by_cases hpTop : p = ∞
  · subst p
    have hs : s = 1 := (ENNReal.HolderTriple.unique ∞ s 1 s).symm
    subst s
    simp only [schattenNorm_top]
    rw [schattenNorm_eq_of_ne_top _ (by simp), ENNReal.toReal_one, schattenNormReal_one]
    exact abs_frobInner_le_specNorm_mul_nuclearNorm A B
  · by_cases hsTop : s = ∞
    · subst s
      have hp : p = 1 := (ENNReal.HolderTriple.unique p ∞ 1 p).symm
      subst p
      simp only [schattenNorm_top]
      rw [schattenNorm_eq_of_ne_top _ (by simp), ENNReal.toReal_one, schattenNormReal_one]
      exact abs_frobInner_le_nuclearNorm_mul_specNorm A B
    · rw [schattenNorm_eq_of_ne_top _ hpTop, schattenNorm_eq_of_ne_top _ hsTop]
      exact abs_frobInner_le_schattenNormReal_mul A B
        (ENNReal.HolderConjugate.toReal_of_ne_top hpTop hsTop)

end NLAlib
