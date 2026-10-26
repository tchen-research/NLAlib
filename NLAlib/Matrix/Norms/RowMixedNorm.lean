import NLAlib.Matrix.Norms.RowSchattenBounds
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Mixed Euclidean-row matrix norms

The actual `ℓ_p(ℓ₂)` matrix norm, including the maximum-row endpoint, is
represented by a finite `PiLp` space. This supplies the triangle inequality,
Frobenius Lipschitz control, and the deterministic Schatten lower comparison
used in Latała--van Handel--Youssef (2018), Corollary 1.4.
-/

noncomputable section
open scoped ENNReal
namespace NLAlib

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The mixed `ℓ_p(ℓ₂)` norm of a matrix, with the usual maximum Euclidean
row norm at `p = ∞`. -/
def rowMixedNorm (A : Matrix m n 𝕜) (p : ℝ≥0∞) : ℝ :=
  ‖(WithLp.toLp p (fun i =>
    (WithLp.toLp 2 (fun j => A i j) : EuclideanSpace 𝕜 n)) :
      PiLp p (fun _ : m => EuclideanSpace 𝕜 n))‖

/-- The native finite-exponent formula for the mixed row norm. -/
theorem rowMixedNorm_eq_sum (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 0 < p.toReal) :
    rowMixedNorm A p = (∑ i, Real.sqrt (rowSq A i) ^ p.toReal) ^ (1 / p.toReal) := by
  unfold rowMixedNorm
  rw [PiLp.norm_eq_sum hp]
  simp only [PiLp.norm_eq_of_L2, rowSq]

/-- The maximum Euclidean-row formula at the infinity endpoint. -/
theorem rowMixedNorm_top (A : Matrix m n 𝕜) :
    rowMixedNorm A ⊤ = ⨆ i, Real.sqrt (rowSq A i) := by
  unfold rowMixedNorm
  rw [PiLp.norm_eq_ciSup]
  simp only [PiLp.norm_eq_of_L2, rowSq]

/-- Mixed row norms are nonnegative at every exponent. -/
theorem rowMixedNorm_nonneg (A : Matrix m n 𝕜) (p : ℝ≥0∞) : 0 ≤ rowMixedNorm A p := by
  by_cases hp0 : p = 0
  · subst p
    rw [rowMixedNorm, PiLp.norm_eq_card]
    positivity
  by_cases hpt : p = ⊤
  · subst p
    exact norm_nonneg _
  rw [rowMixedNorm_eq_sum A (ENNReal.toReal_pos hp0 hpt)]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _) _

/-- The zero matrix has zero mixed row norm at every exponent at least one. -/
theorem rowMixedNorm_zero {p : ℝ≥0∞} (hp : 1 ≤ p) :
    rowMixedNorm (0 : Matrix m n 𝕜) p = 0 := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  exact norm_zero

/-- The triangle inequality for the actual mixed row norm. -/
theorem rowMixedNorm_add_le (A B : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    rowMixedNorm (A + B) p ≤ rowMixedNorm A p + rowMixedNorm B p := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  exact norm_add_le
    (WithLp.toLp p (fun i => (WithLp.toLp 2 (fun j => A i j) : EuclideanSpace 𝕜 n)))
    (WithLp.toLp p (fun i => (WithLp.toLp 2 (fun j => B i j) : EuclideanSpace 𝕜 n)))

/-- The reverse triangle inequality for the mixed row norm. -/
theorem abs_rowMixedNorm_sub_le (A B : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    |rowMixedNorm A p - rowMixedNorm B p| ≤ rowMixedNorm (A - B) p := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  exact abs_norm_sub_norm_le
    (WithLp.toLp p (fun i => (WithLp.toLp 2 (fun j => A i j) : EuclideanSpace 𝕜 n)))
    (WithLp.toLp p (fun i => (WithLp.toLp 2 (fun j => B i j) : EuclideanSpace 𝕜 n)))

/-- At exponent two, the mixed row norm is exactly the Frobenius norm. -/
theorem rowMixedNorm_two (A : Matrix m n 𝕜) : rowMixedNorm A 2 = frobNorm A := by
  unfold rowMixedNorm
  rw [PiLp.norm_eq_of_L2]
  simp only [PiLp.norm_eq_of_L2, Real.sq_sqrt
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [frobNorm, frobSq_eq_sum_norm_sq]

/-- Every mixed row norm of exponent at least two is bounded by the
Frobenius norm, including the infinity endpoint. -/
theorem rowMixedNorm_le_frobNorm (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    rowMixedNorm A p ≤ frobNorm A := by
  by_cases hpt : p = ⊤
  · subst p
    rw [rowMixedNorm_top]
    cases isEmpty_or_nonempty m with
    | inl h => simp [frobNorm_nonneg]
    | inr h =>
        apply ciSup_le
        intro i
        apply Real.sqrt_le_sqrt
        change (∑ j, ‖A i j‖ ^ 2) ≤ frobSq A
        rw [frobSq_eq_sum_norm_sq]
        exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg (‖A j k‖))
          (Finset.mem_univ i)
  · have hp2 : (2 : ℝ) ≤ p.toReal := by
      simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hpt hp
    rw [rowMixedNorm_eq_sum A (by linarith)]
    have h := sum_rpow_root_le_sum_rpow_root Finset.univ
      (fun i => Real.sqrt (rowSq A i)) (fun i _ => Real.sqrt_nonneg _)
      (by norm_num : (0 : ℝ) < 2) hp2
    apply h.trans_eq
    rw [← rowMixedNorm_two A, rowMixedNorm_eq_sum A (by norm_num)]
    simp

/-- The actual mixed row norm is Frobenius Lipschitz with constant one. -/
theorem abs_rowMixedNorm_sub_le_frobNorm (A B : Matrix m n 𝕜)
    {p : ℝ≥0∞} (hp : 2 ≤ p) :
    |rowMixedNorm A p - rowMixedNorm B p| ≤ frobNorm (A - B) :=
  (abs_rowMixedNorm_sub_le A B (le_trans (by norm_num) hp)).trans
    (rowMixedNorm_le_frobNorm _ hp)

/-- The actual mixed row norm is bounded by the native Schatten norm for
every finite exponent at least two and at infinity. -/
theorem rowMixedNorm_le_schattenNorm [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    rowMixedNorm A p ≤ schattenNorm A p := by
  by_cases hpt : p = ⊤
  · subst p
    rw [rowMixedNorm_top, schattenNorm_top]
    cases isEmpty_or_nonempty m with
    | inl h => simp [specNorm_nonneg]
    | inr h =>
        apply ciSup_le
        intro i
        exact (Real.sqrt_le_left (specNorm_nonneg _)).mpr (rowSq_le_specNorm_sq A i)
  · have hp2 : (2 : ℝ) ≤ p.toReal := by
      simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hpt hp
    rw [rowMixedNorm_eq_sum A (by linarith), schattenNorm_eq_of_ne_top A hpt]
    exact rowNorm_sum_rpow_div_p_le_schattenNormReal A hp2

/-- Independent row and column coordinate permutations preserve the actual
mixed row norm at every exponent at least one, including infinity. -/
theorem rowMixedNorm_submatrix_equiv
    {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m n 𝕜) (e : m' ≃ m) (f : n' ≃ n)
    {p : ℝ≥0∞} (hp : 1 ≤ p) : rowMixedNorm (A.submatrix e f) p = rowMixedNorm A p := by
  have hrow (i : m') : rowSq (A.submatrix e f) i = rowSq A (e i) :=
    f.sum_comp (fun j => ‖A (e i) j‖ ^ 2)
  by_cases hpt : p = ⊤
  · subst p
    simp only [rowMixedNorm_top, hrow]
    exact e.iSup_congr fun _ => rfl
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt
    rw [rowMixedNorm_eq_sum _ hpr, rowMixedNorm_eq_sum _ hpr]
    simp only [hrow]
    rw [e.sum_comp (fun i => Real.sqrt (rowSq A i) ^ p.toReal)]

/-- The finite native row norm power is the literal row-energy power sum. -/
theorem rowMixedNorm_ofReal_eq_sum_rowSq (A : Matrix m n 𝕜) {p : ℝ} (hp : 0 < p) :
    rowMixedNorm A (ENNReal.ofReal p) = (∑ i, rowSq A i ^ (p / 2)) ^ (1 / p) := by
  rw [rowMixedNorm_eq_sum A (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp only [ENNReal.toReal_ofReal hp.le]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hrow : 0 ≤ rowSq A i := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrow]
  congr 1
  ring

/-- The finite native row norm power is the literal row-energy power sum. -/
theorem rowMixedNorm_ofReal_rpow (A : Matrix m n 𝕜) {p : ℝ} (hp : 0 < p) :
    rowMixedNorm A (ENNReal.ofReal p) ^ p = ∑ i, rowSq A i ^ (p / 2) := by
  rw [rowMixedNorm_eq_sum A (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp only [ENNReal.toReal_ofReal hp.le, one_div]
  rw [Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _) hp.ne']
  apply Finset.sum_congr rfl
  intro i _
  have hrow : 0 ≤ rowSq A i := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hrow]
  congr 1
  ring

/-- Increasing every row square-energy increases the mixed norm at every
native exponent at least one, including infinity. -/
theorem rowMixedNorm_le_of_rowSq_le (A B : Matrix m n 𝕜) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hrow : ∀ i, rowSq A i ≤ rowSq B i) :
    rowMixedNorm A p ≤ rowMixedNorm B p := by
  by_cases hpt : p = ⊤
  · subst p
    rw [rowMixedNorm_top, rowMixedNorm_top]
    exact ciSup_mono (Set.finite_range _).bddAbove fun i => Real.sqrt_le_sqrt (hrow i)
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt
    rw [rowMixedNorm_eq_sum A hpr, rowMixedNorm_eq_sum B hpr]
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (Real.sqrt_nonneg _) _) _ (by positivity)
    exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (Real.sqrt_nonneg _)
      (Real.sqrt_le_sqrt (hrow i)) hpr.le

/-- The maximum Euclidean-row norm is bounded by every finite mixed row norm
of exponent at least one, with the infinity case included. -/
theorem rowMixedNorm_top_le (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    rowMixedNorm A ⊤ ≤ rowMixedNorm A p := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  rw [rowMixedNorm_top]
  cases isEmpty_or_nonempty m with
  | inl h => simp [rowMixedNorm_nonneg]
  | inr h =>
      apply ciSup_le
      intro i
      have hi := PiLp.norm_apply_le
        (WithLp.toLp p (fun i => (WithLp.toLp 2 (fun j => A i j) : EuclideanSpace 𝕜 n))) i
      unfold rowMixedNorm
      simpa only [PiLp.norm_eq_of_L2, rowSq] using hi

/-- Every matrix entry is bounded by the actual mixed row norm at every
native exponent at least one, including infinity. -/
theorem norm_entry_le_rowMixedNorm (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (i : m) (j : n) : ‖A i j‖ ≤ rowMixedNorm A p := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hrow := PiLp.norm_apply_le
    (WithLp.toLp 2 (fun j => A i j) : EuclideanSpace 𝕜 n) j
  have hout := PiLp.norm_apply_le
    (WithLp.toLp p (fun i => (WithLp.toLp 2 (fun j => A i j) : EuclideanSpace 𝕜 n))) i
  exact hrow.trans hout

end NLAlib
