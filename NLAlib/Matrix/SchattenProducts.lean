import NLAlib.Matrix.SchattenNorms
import NLAlib.Matrix.HornPowerSums

/-!
# Schatten Hölder for compatible products

Horn power sums and scalar Hölder give the product inequality with constant
one. Native singular-value ideal bounds handle the infinity endpoints.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators ENNReal

namespace NLAlib

/-- Native singular values vanish past the smaller matrix dimension. -/
theorem toEuclideanLin_singularValues_eq_zero_of_min_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) {i : ℕ}
    (hi : min (Fintype.card m) (Fintype.card n) ≤ i) : A.toEuclideanLin.singularValues i = 0 := by
  rw [← singularValues_reindex_eq_toEuclideanLin_singularValues A i]
  exact singularValues_eq_zero_of_min_le _ hi

/-- Zero padding a positive-exponent singular-value power sum leaves it unchanged. -/
theorem sum_range_toEuclideanLin_singularValues_rpow_eq_of_min_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) {N : ℕ}
    (hN : min (Fintype.card m) (Fintype.card n) ≤ N) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ Finset.range N, A.toEuclideanLin.singularValues i ^ p) =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), A.toEuclideanLin.singularValues i ^ p := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro i _ hi
  rw [toEuclideanLin_singularValues_eq_zero_of_min_le A (by
    simpa only [Finset.mem_range, not_lt] using hi), Real.zero_rpow hp.ne']

/-- Schatten norms may be written with any sufficiently long zero-padded
singular-value list, including empty shapes. -/
theorem schattenNorm_eq_sum_range_rpow_of_min_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) {N : ℕ}
    (hN : min (Fintype.card m) (Fintype.card n) ≤ N) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p = (∑ i ∈ Finset.range N, A.toEuclideanLin.singularValues i ^ p) ^ (1 / p) := by
  rw [sum_range_toEuclideanLin_singularValues_rpow_eq_of_min_le A hN hp]
  rfl

/-- Finite-exponent Schatten product Hölder with sharp constant one, on
arbitrary finite compatible shapes. This actually covers every positive real
Hölder triple, including the usual norm exponents at least one.
atlas: schatten-norms-def (partial) -/
theorem schattenNorm_mul_le_mul {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ) (B : Matrix n q ℝ) {p s r : ℝ}
    (hpsr : Real.HolderTriple p s r) : schattenNorm (A * B) r ≤ schattenNorm A p * schattenNorm B s := by
  let N := max (min (Fintype.card m) (Fintype.card n))
    (max (min (Fintype.card n) (Fintype.card q)) (min (Fintype.card m) (Fintype.card q)))
  have hNA : min (Fintype.card m) (Fintype.card n) ≤ N := le_max_left _ _
  have hNB : min (Fintype.card n) (Fintype.card q) ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNAB : min (Fintype.card m) (Fintype.card q) ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hp := hpsr.left_pos
  have hs := hpsr.right_pos
  have hr := hpsr.pos'
  have hpow := (sum_range_toEuclideanLin_singularValues_mul_rpow_le A B N hr).trans
    (Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg (Finset.range N) hpsr
      (fun i _ => LinearMap.singularValues_nonneg _ i) (fun i _ => LinearMap.singularValues_nonneg _ i))
  have hSA : 0 ≤ ∑ i ∈ Finset.range N, A.toEuclideanLin.singularValues i ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (LinearMap.singularValues_nonneg _ i) p)
  have hSB : 0 ≤ ∑ i ∈ Finset.range N, B.toEuclideanLin.singularValues i ^ s :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (LinearMap.singularValues_nonneg _ i) s)
  rw [schattenNorm_eq_sum_range_rpow_of_min_le (A * B) hNAB hr,
    schattenNorm_eq_sum_range_rpow_of_min_le A hNA hp, schattenNorm_eq_sum_range_rpow_of_min_le B hNB hs]
  calc
    _ ≤ ((∑ i ∈ Finset.range N, A.toEuclideanLin.singularValues i ^ p) ^ (r / p) *
          (∑ i ∈ Finset.range N, B.toEuclideanLin.singularValues i ^ s) ^ (r / s)) ^ (1 / r) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (LinearMap.singularValues_nonneg _ i) r) hpow (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hSA _) (Real.rpow_nonneg hSB _),
        ← Real.rpow_mul hSA, ← Real.rpow_mul hSB]
      congr 1 <;> congr 1 <;> field_simp

/-- Native right-ideal singular-value bound for every padded index. -/
theorem toEuclideanLin_singularValues_mul_le_mul_specNorm {m n q : Type*}
    [Fintype m] [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q]
    (A : Matrix m n ℝ) (B : Matrix n q ℝ) (i : ℕ) :
    (A * B).toEuclideanLin.singularValues i ≤ A.toEuclideanLin.singularValues i * specNorm B := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let eq := Fintype.equivFin q
  have h := singularValues_mul_le_mul_specNorm (A.reindex em en) (B.reindex en eq) i
  have hmul : A.reindex em en * B.reindex en eq = (A * B).reindex em eq := by
    simpa only [Matrix.reindex_apply] using Matrix.submatrix_mul_equiv A B em.symm en.symm eq.symm
  rw [hmul, specNorm_reindex] at h
  simpa only [em, en, eq, singularValues_reindex_eq_toEuclideanLin_singularValues] using h

/-- Native left-ideal singular-value bound for every padded index. -/
theorem toEuclideanLin_singularValues_mul_le_specNorm_mul {m n q : Type*}
    [Fintype m] [Fintype n] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq q]
    (A : Matrix m n ℝ) (B : Matrix n q ℝ) (i : ℕ) :
    (A * B).toEuclideanLin.singularValues i ≤ specNorm A * B.toEuclideanLin.singularValues i := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let eq := Fintype.equivFin q
  have h := singularValues_mul_le_specNorm_mul (A.reindex em en) (B.reindex en eq) i
  have hmul : A.reindex em en * B.reindex en eq = (A * B).reindex em eq := by
    simpa only [Matrix.reindex_apply] using Matrix.submatrix_mul_equiv A B em.symm en.symm eq.symm
  rw [hmul, specNorm_reindex] at h
  simpa only [em, en, eq, singularValues_reindex_eq_toEuclideanLin_singularValues] using h

end NLAlib
