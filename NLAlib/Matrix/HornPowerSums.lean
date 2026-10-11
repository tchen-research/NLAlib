import NLAlib.Matrix.MajorizationConvex
import NLAlib.Matrix.ProductSingularValues
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Horn product inequalities imply power-sum inequalities

Logarithmic weak majorization and the increasing convex function
`u ↦ exp (p u)` turn all prefix-product comparisons into power-sum comparisons.
Zero singular values are handled by the actual rank support, rather than by a
full-rank assumption or an unjustified logarithm of zero.
Source: Horn–Johnson (1991), §3.3; Bhatia (1997), §IV.2.
Atlas: `horn-product-inequality`, `schatten-norms-def`.
-/

noncomputable section
open scoped BigOperators Matrix

namespace NLAlib

/-- For positive decreasing finite prefixes, all prefix-product comparisons
imply every positive-exponent power-sum comparison. Logarithmic majorization. -/
theorem sum_range_rpow_le_of_pos_of_prod_le (x y : ℕ → ℝ) {N : ℕ}
    (hx : ∀ i < N, 0 < x i) (hy : ∀ i < N, 0 < y i)
    (hxa : Antitone x) (hya : Antitone y)
    (hprod : ∀ k ≤ N, (∏ i ∈ Finset.range k, x i) ≤ ∏ i ∈ Finset.range k, y i)
    {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ Finset.range N, x i ^ p) ≤ ∑ i ∈ Finset.range N, y i ^ p := by
  let a : Fin N → ℝ := fun i => Real.log (x i)
  let b : Fin N → ℝ := fun i => Real.log (y i)
  have ha : Antitone a := fun i j hij => Real.log_le_log (hx j j.isLt) (hxa hij)
  have hb : Antitone b := fun i j hij => Real.log_le_log (hy j j.isLt) (hya hij)
  have hab : WeaklyMajorized a b := by
    intro k hk
    have hkN : k ≤ N := by simpa using hk
    rw [sumLargest_eq_prefix_of_antitone a ha, sumLargest_eq_prefix_of_antitone b hb]
    rw [sum_fin_ite_lt_eq_sum_range hkN (fun i => Real.log (x i)),
      sum_fin_ite_lt_eq_sum_range hkN (fun i => Real.log (y i))]
    have hlog := Real.log_le_log (Finset.prod_pos (fun i hi => hx i (by
      exact lt_of_lt_of_le (Finset.mem_range.mp hi) hkN))) (hprod k hkN)
    rw [Real.log_prod (fun i hi => (hx i (lt_of_lt_of_le (Finset.mem_range.mp hi) hkN)).ne'),
      Real.log_prod (fun i hi => (hy i (lt_of_lt_of_le (Finset.mem_range.mp hi) hkN)).ne')] at hlog
    exact hlog
  have hmono : Monotone (fun u : ℝ => Real.exp (p * u)) :=
    fun u v huv => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huv hp.le)
  have hconv : ConvexOn ℝ Set.univ (fun u : ℝ => Real.exp (p * u)) := by
    convert! ConvexOn.comp_linearMap convexOn_exp (LinearMap.mul ℝ ℝ p) using 1
  have h := hab.sum_monotone_convex_le hmono hconv
  have heX (i : Fin N) : Real.exp (p * a i) = x i ^ p := by
    rw [Real.rpow_def_of_pos (hx i i.isLt)]
    dsimp [a]
    rw [mul_comm]
  have heY (i : Fin N) : Real.exp (p * b i) = y i ^ p := by
    rw [Real.rpow_def_of_pos (hy i i.isLt)]
    dsimp [b]
    rw [mul_comm]
  simp_rw [heX, heY] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => x i ^ p) N,
    Fin.sum_univ_eq_sum_range (fun i => y i ^ p) N] at h
  exact h

/-- Nonnegative decreasing sequences obey the power-sum comparison even when
the left sequence has zeros. The support hypotheses merely specify its actual
positive prefix and permit zero padding. -/
theorem sum_range_rpow_le_of_nonneg_of_prod_le (x y : ℕ → ℝ) {r : ℕ}
    (_hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i)
    (hxpos : ∀ i < r, 0 < x i) (hxzero : ∀ i, r ≤ i → x i = 0)
    (hxa : Antitone x) (hya : Antitone y)
    (hprod : ∀ k, (∏ i ∈ Finset.range k, x i) ≤ ∏ i ∈ Finset.range k, y i)
    (N : ℕ) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ Finset.range N, x i ^ p) ≤ ∑ i ∈ Finset.range N, y i ^ p := by
  let s := min r N
  have hsN : s ≤ N := min_le_right r N
  have hsr : s ≤ r := min_le_left r N
  have hxs (i : ℕ) (hi : i < s) : 0 < x i := hxpos i (hi.trans_le hsr)
  have hxp : 0 < ∏ i ∈ Finset.range s, x i := Finset.prod_pos fun i hi => hxs i (Finset.mem_range.mp hi)
  have hyp : 0 < ∏ i ∈ Finset.range s, y i := hxp.trans_le (hprod s)
  have hys (i : ℕ) (hi : i < s) : 0 < y i := by
    by_contra h
    have hyi : y i = 0 := le_antisymm (le_of_not_gt h) (hy0 i)
    have hzero : (∏ j ∈ Finset.range s, y j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hi) hyi
    rw [hzero] at hyp
    exact (lt_irrefl 0) hyp
  have hpower := sum_range_rpow_le_of_pos_of_prod_le x y hxs hys hxa hya
    (fun k _ => hprod k) hp
  have hleft : (∑ i ∈ Finset.range s, x i ^ p) = ∑ i ∈ Finset.range N, x i ^ p := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr hsN)
    intro i hi hni
    have hir : r ≤ i := by
      simp only [Finset.mem_range] at hi hni
      dsimp [s] at hni
      omega
    rw [hxzero i hir, Real.zero_rpow hp.ne']
  rw [hleft] at hpower
  exact hpower.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr hsN) (fun i _ _ => Real.rpow_nonneg (hy0 i) p))

/-- Horn's full singular-value product inequality implies every positive
power-sum prefix comparison, including rank-deficient matrices and all padded
prefixes. Horn–Johnson (1991), §3.3; Bhatia (1997), §IV.2.
atlas: horn-product-inequality (partial) -/
theorem sum_range_singularValues_mul_rpow_le {m n q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin q) ℝ)
    (N : ℕ) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ Finset.range N, singularValues (A * B) i ^ p) ≤
      ∑ i ∈ Finset.range N, (singularValues A i * singularValues B i) ^ p := by
  apply sum_range_rpow_le_of_nonneg_of_prod_le
    (singularValues (A * B)) (fun i => singularValues A i * singularValues B i)
    (r := (A * B).rank) (singularValues_nonneg _)
    (fun i => mul_nonneg (singularValues_nonneg A i) (singularValues_nonneg B i))
    (fun i hi => (singularValues_pos_iff _ i).mpr hi)
    (fun i hi => singularValues_eq_zero_of_rank_le _ hi) (singularValues_antitone _)
    (fun i j hij => mul_le_mul (singularValues_antitone A hij) (singularValues_antitone B hij)
      (singularValues_nonneg B j) (singularValues_nonneg A i))
    (prod_singularValues_mul_le A B) N hp

/-- The full positive-power Horn prefix comparison in native linear-map
singular values, for arbitrary finite compatible matrix indices. All padded
prefixes, empty shapes and rank defects are included.
atlas: horn-product-inequality (partial) -/
theorem sum_range_toEuclideanLin_singularValues_mul_rpow_le {m n q : Type*}
    [Fintype m] [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q]
    (A : Matrix m n ℝ) (B : Matrix n q ℝ) (N : ℕ) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ Finset.range N, (A * B).toEuclideanLin.singularValues i ^ p) ≤
      ∑ i ∈ Finset.range N, (A.toEuclideanLin.singularValues i * B.toEuclideanLin.singularValues i) ^ p := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let eq := Fintype.equivFin q
  have h := sum_range_singularValues_mul_rpow_le (A.reindex em en) (B.reindex en eq) N hp
  have hmul : A.reindex em en * B.reindex en eq = (A * B).reindex em eq := by
    simpa only [Matrix.reindex_apply] using Matrix.submatrix_mul_equiv A B em.symm en.symm eq.symm
  rw [hmul] at h
  simpa only [em, en, eq, singularValues_reindex_eq_toEuclideanLin_singularValues] using h

end NLAlib
