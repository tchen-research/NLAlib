import NLAlib.Matrix.Inequalities.Schur
import NLAlib.Matrix.Norms.SchattenNorms
import NLAlib.Matrix.Spectral.GramSpectralSums
import NLAlib.Matrix.Norms.SchattenNormalization
import Mathlib.Analysis.Matrix.PosDef

/-!
# Deterministic row-l2 versus Schatten-p lower comparison

For a rectangular matrix `A : Matrix m n K` over `ℝ` or `ℂ` (any `RCLike` field),
the `l2` energy of each row is the sum of the squared entry moduli
`rowSq A i = ∑ j, ‖A i j‖²`. Schur's diagonal majorization of the Gram matrix
`A * Aᴴ` shows that the power sum of the row energies at exponent `p / 2`
is bounded by the Schatten-power sum at exponent `p`:

`(∑ i, rowSq A i ^ (p / 2)) ≤ schattenNormReal A p ^ p` for every `2 ≤ p`.

Raising to `1 / p` gives the usual rooted Euclidean-row-norm comparison

`(∑ i, (√(rowSq A i)) ^ p) ^ (1 / p) ≤ schattenNormReal A p`,

and the entry `schattenNorm A (ENNReal.ofReal p)` interface via the existing
normalization bridge. At exponent infinity the maximum Euclidean row norm is
bounded by the spectral norm.

All statements keep empty shapes and zero rows (the zero-padding conventions of
`singularValues` and `schattenNormReal` make the sums vanish consistently).
This is the deterministic lower comparison only; the Gaussian upper estimates
and tail bounds are not proved here.

Source: Horn–Johnson (2013), Theorem 4.3.45 (Schur); Bhatia (1997), §IV.2.
-/

noncomputable section

open scoped Matrix ENNReal

namespace NLAlib

variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The squared Euclidean `l2` energy of a row of `A`: `∑ j, ‖A i j‖²`. -/
def rowSq (A : Matrix m n K) (i : m) : ℝ :=
  ∑ j, ‖A i j‖ ^ 2

/-- A deterministic lower comparison of the row-energy power sum with the
Schatten power sum at the same exponent: for every `2 ≤ p`,
`∑ i, rowSq A i ^ (p / 2) ≤ schattenNormReal A p ^ p`. This is Schur's
diagonal majorization applied to the Gram matrix `A * Aᴴ`, followed by the
eigenvalue–singular-value bridge. -/
theorem sum_rowSq_rpow_le_schattenNormReal_rpow (A : Matrix m n K) {p : ℝ}
    (hp : 2 ≤ p) :
    (∑ i, rowSq A i ^ (p / 2)) ≤ schattenNormReal A p ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hd : (fun i : m => RCLike.re ((A * A.conjTranspose) i i)) =
      fun i => rowSq A i := by
    funext i
    simp only [rowSq, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
      RCLike.mul_conj, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hm := (majorized_diagonal_eigenvalues
    (Matrix.isHermitian_mul_conjTranspose_self A)).1
  rw [hd] at hm
  have hp2 : 1 ≤ p / 2 := by linarith
  have hs := hm.sum_rpow_le (p := p / 2)
    (by intro i; exact Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun i => Matrix.eigenvalues_self_mul_conjTranspose_nonneg A i)
    hp2
  have hterm (i : ℕ) :
      (singularValues A i ^ 2) ^ (p / 2) = singularValues A i ^ p := by
    rw [← Real.rpow_natCast_mul (singularValues_nonneg A i) 2 (p / 2)]
    congr 1
    ring
  have heig :
      (∑ i, ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i) ^
        (p / 2)) =
        ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          singularValues A i ^ p := by
    rw [sum_eigenvalues_mul_adjoint_eq_adjoint_mul A (fun x => x ^ (p / 2))
      (Real.zero_rpow (ne_of_gt (div_pos hp0 (by norm_num))))]
    rw [sum_eigenvalues_gram_eq_sum_singularValues A (fun x => x ^ (p / 2))]
    simp_rw [hterm]
    exact sum_range_singularValues_map_eq_of_min_le A (fun x => x ^ p)
      (by simp [Real.zero_rpow hp0.ne']) (min_le_right (Fintype.card m) (Fintype.card n))
  rw [heig, (schattenNormReal_rpow_eq_sum A hp0).symm] at hs
  exact hs

/-- The usual rooted Euclidean-row-norm power comparison: for every `2 ≤ p`,
`∑ i, (√(rowSq A i)) ^ p ≤ schattenNormReal A p ^ p`. -/
theorem sum_rowNorm_rpow_le_schattenNormReal_rpow (A : Matrix m n K) {p : ℝ}
    (hp : 2 ≤ p) :
    (∑ i, (√(rowSq A i) : ℝ) ^ p) ≤ schattenNormReal A p ^ p := by
  have hs := sum_rowSq_rpow_le_schattenNormReal_rpow A hp
  have hterm (i : m) : (√(rowSq A i) : ℝ) ^ p = rowSq A i ^ (p / 2) := by
    have hx : 0 ≤ rowSq A i := Finset.sum_nonneg fun j _ => sq_nonneg _
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hx]
    congr 1
    rw [mul_comm, mul_one_div]
  simpa [hterm] using hs

/-- The rooted Euclidean-row-norm comparison for the finite Schatten norm:
for every `2 ≤ p`, `(∑ i, rowSq A i ^ (p / 2)) ^ (1 / p) ≤ schattenNormReal A p`. -/
theorem rowSq_sum_rpow_div_p_le_schattenNormReal (A : Matrix m n K) {p : ℝ}
    (hp : 2 ≤ p) :
    (∑ i, rowSq A i ^ (p / 2)) ^ (1 / p) ≤ schattenNormReal A p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have h := sum_rowSq_rpow_le_schattenNormReal_rpow A hp
  have hnonneg : 0 ≤ ∑ i, rowSq A i ^ (p / 2) := by
    exact Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) _
  have hroot :
      (∑ i, rowSq A i ^ (p / 2)) ^ (1 / p) ≤
        (schattenNormReal A p ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow hnonneg h
      (one_div_nonneg.mpr (lt_of_lt_of_le (by norm_num) hp).le)
  exact hroot.trans_eq (by
    rw [one_div, Real.rpow_rpow_inv (schattenNormReal_nonneg A p) hp0.ne'])

/-- The rooted Euclidean-row-norm comparison for the finite Schatten norm:
for every `2 ≤ p`, `(∑ i, (√(rowSq A i)) ^ p) ^ (1 / p) ≤ schattenNormReal A p`. -/
theorem rowNorm_sum_rpow_div_p_le_schattenNormReal (A : Matrix m n K) {p : ℝ}
    (hp : 2 ≤ p) :
    (∑ i, (√(rowSq A i) : ℝ) ^ p) ^ (1 / p) ≤ schattenNormReal A p := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have h := sum_rowNorm_rpow_le_schattenNormReal_rpow A hp
  have hnonneg : 0 ≤ ∑ i, (√(rowSq A i) : ℝ) ^ p := by
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hroot :
      (∑ i, (√(rowSq A i) : ℝ) ^ p) ^ (1 / p) ≤
        (schattenNormReal A p ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow hnonneg h
      (one_div_nonneg.mpr (lt_of_lt_of_le (by norm_num) hp).le)
  exact hroot.trans_eq (by
    rw [one_div, Real.rpow_rpow_inv (schattenNormReal_nonneg A p) hp0.ne'])

/-- The standard `schattenNorm A (ENNReal.ofReal p)` interface of the rooted
Euclidean-row-norm comparison, via the existing normalization bridge. -/
theorem rowNorm_sum_rpow_div_p_le_schattenNorm (A : Matrix m n K) {p : ℝ}
    (hp : 2 ≤ p) :
    (∑ i, (√(rowSq A i) : ℝ) ^ p) ^ (1 / p) ≤
      schattenNorm A (ENNReal.ofReal p) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 2) hp
  rw [schattenNorm_ofReal A hp0]
  exact rowNorm_sum_rpow_div_p_le_schattenNormReal A hp

/-- The squared Euclidean row energy is bounded by the squared spectral norm:
`rowSq A i ≤ specNorm A ^ 2`. This is the operator-norm bound applied to the
`i`-th unit coordinate vector, transported through `Aᴴ`. -/
theorem rowSq_le_specNorm_sq (A : Matrix m n K) (i : m) :
    rowSq A i ≤ specNorm A ^ 2 := by
  classical
  let e : m → K := Pi.single i (1 : K)
  have h := sum_norm_sq_mulVec_le_specNorm_sq A.conjTranspose e
  have hsingle : (∑ j, ‖e j‖ ^ 2) = 1 := by
    subst e
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      simp at hi
  rw [specNorm_conjTranspose, hsingle, mul_one] at h
  rw [Matrix.mulVec_single_one] at h
  simpa only [rowSq, Matrix.col, Matrix.transpose_apply, Matrix.conjTranspose_apply, norm_star] using h

/-- The Euclidean length of a row is bounded by the spectral norm:
`√(rowSq A i) ≤ specNorm A`. -/
theorem rowNorm_le_specNorm (A : Matrix m n K) (i : m) :
    Real.sqrt (rowSq A i) ≤ specNorm A := by
  exact (Real.sqrt_le_left (specNorm_nonneg A)).2 (rowSq_le_specNorm_sq A i)

/-- The `Pi`-sup norm of the squared row energies is bounded by the squared
spectral norm: `‖(fun i => rowSq A i)‖ ≤ specNorm A ^ 2`. -/
theorem pi_norm_rowSq_le_specNorm_sq (A : Matrix m n K) :
    ‖(fun i => rowSq A i)‖ ≤ specNorm A ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · exact rowSq_le_specNorm_sq A i
  · exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The maximum Euclidean row norm is bounded by the spectral norm:
`‖(fun i => √(rowSq A i))‖ ≤ specNorm A`. -/
theorem pi_norm_rowNorm_le_specNorm (A : Matrix m n K) :
    ‖(fun i => Real.sqrt (rowSq A i))‖ ≤ specNorm A := by
  rw [pi_norm_le_iff_of_nonneg (specNorm_nonneg A)]
  intro i
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · exact rowNorm_le_specNorm A i
  · exact Real.sqrt_nonneg _

end NLAlib
