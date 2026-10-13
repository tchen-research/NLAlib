import NLAlib.ForMathlib.Analysis.InnerProductSpace.GramSchmidt
import NLAlib.Matrix.Factorizations.QR
import NLAlib.Matrix.Norms.Core
/-!
# Classical Gram–Schmidt orthogonalisation

The column-oriented classical Gram–Schmidt process of Trefethen–Bau Alg. 7.1 on
`A : m × n`, as a total recursion:

* `gramSchmidtResidual A j = a_j − ∑_{i<j} (q_iᵀ a_j) q_i` (the vector `v_j`) and
  `gramSchmidtCol A j = v_j / ‖v_j‖` (the vector `q_j`; `0` when `v_j = 0`, by `0⁻¹ = 0`);
  `gramSchmidtQ A`, `gramSchmidtR A` (`r_ij = q_iᵀ a_j` for `i < j`, `r_jj = ‖v_j‖`).
* `GramSchmidtSucceeds A`: no residual vanishes. Breakdown theorem:
  `gramSchmidtResidual_eq_zero_iff` (`v_j = 0` iff `a_j ∈ span(a_i : i < j)`) and
  `gramSchmidtSucceeds_iff_linearIndependent`.
* Realisation: `gramSchmidtQ_mul_gramSchmidtR` (`QR = A` for every `A`, even after a breakdown)
  and `isQR_gramSchmidt` (thin QR with `r_jj > 0` when the process succeeds).
* `IsGradedColumnBasis A Q`: `Q` has orthonormal columns and its first `k + 1` columns span the
  first `k + 1` columns of `A` (the column flag), the analogue of `IsGradedKrylovBasis`
  (Krylov layer, not imported here) with `K_{k+1}(A, b)` replaced by `span(a_0, …, a_k)`.
  `isGradedColumnBasis_gramSchmidtQ`, and every thin QR with invertible `R` gives one
  (`IsQR.isGradedColumnBasis`).
* Bridge to Mathlib's `InnerProductSpace.gramSchmidtNormed` (`gramSchmidtCol_eq_gramSchmidtNormed`).

The modified process and its equality with this recursion are in
`NLAlib.Matrix.Factorizations.GramSchmidt`.

With the zero-skipping convention (`q_j = 0` after a breakdown) the columns of `Q` are always
pairwise orthogonal and of norm `0` or `1` (`transpose_gramSchmidtQ_mul_self`), and the span of
`q_0, …, q_k` is always the span of `a_0, …, a_k`; only `QᵀQ = I` needs success.

Sources: Trefethen–Bau 1997 [`tb97`], Lect. 7–8 (Alg. 7.1, 8.1, Thm 7.1–7.2);
Golub–Van Loan 2013 [`gvl13`], §5.2.7–5.2.8 (Alg. 5.2.5, 5.2.6).
Atlas: `gram-schmidt`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {m : Type*} [Fintype m] {n : ℕ}

/-! ### Classical Gram–Schmidt -/

/-- The `j`-th **Gram–Schmidt vector** `q_j = v_j / ‖v_j‖` with
`v_j = a_j − ∑_{i<j} (q_iᵀ a_j) q_i` (well-founded recursion on `j`). When `v_j = 0` (breakdown)
`q_j = 0` and the process continues. Trefethen–Bau 1997, Alg. 7.1; Golub–Van Loan 2013,
Alg. 5.2.5.
atlas: gram-schmidt -/
def gramSchmidtCol (A : Matrix m (Fin n) ℝ) (j : Fin n) : m → ℝ :=
  let v := A.col j - ∑ i : Finset.Iio j, (gramSchmidtCol A i ⬝ᵥ A.col j) • gramSchmidtCol A i
  (√(v ⬝ᵥ v))⁻¹ • v
termination_by j
decreasing_by exact Fin.lt_def.1 (Finset.mem_Iio.1 i.2)

/-- The **Gram–Schmidt residual** `v_j = a_j − ∑_{i<j} (q_iᵀ a_j) q_i`. Trefethen–Bau 1997,
Alg. 7.1 (the vector `v_j` before normalisation).
atlas: gram-schmidt -/
def gramSchmidtResidual (A : Matrix m (Fin n) ℝ) (j : Fin n) : m → ℝ :=
  A.col j - ∑ i : Finset.Iio j, (gramSchmidtCol A i ⬝ᵥ A.col j) • gramSchmidtCol A i

/-- Entrywise unfolding of the residual: `v_j(i) = a_ij − ∑_{k<j} (q_kᵀ a_j) q_k(i)`. -/
theorem gramSchmidtResidual_apply (A : Matrix m (Fin n) ℝ) (j : Fin n) (i : m) :
    gramSchmidtResidual A j i =
      A i j - ∑ k ∈ Finset.Iio j, (gramSchmidtCol A k ⬝ᵥ A.col j) * gramSchmidtCol A k i := by
  rw [gramSchmidtResidual, Pi.sub_apply, Finset.sum_apply,
    Finset.sum_coe_sort (Finset.Iio j)
      (fun k => ((gramSchmidtCol A k ⬝ᵥ A.col j) • gramSchmidtCol A k) i)]
  rfl

/-- Unfolding: `q_j = ‖v_j‖⁻¹ v_j`. -/
theorem gramSchmidtCol_eq (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    gramSchmidtCol A j =
      ‖(WithLp.toLp 2 (gramSchmidtResidual A j) : EuclideanSpace ℝ m)‖⁻¹ •
        gramSchmidtResidual A j := by
  rw [norm_toLp_eq_sqrt_dotProduct_self, gramSchmidtCol]; rfl

/-- `‖v_j‖ q_j = v_j` (also after a breakdown, where both sides vanish). -/
theorem norm_smul_gramSchmidtCol (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    ‖(WithLp.toLp 2 (gramSchmidtResidual A j) : EuclideanSpace ℝ m)‖ • gramSchmidtCol A j =
      gramSchmidtResidual A j := by
  rw [norm_toLp_eq_sqrt_dotProduct_self, gramSchmidtCol_eq, norm_toLp_eq_sqrt_dotProduct_self,
    smul_smul]
  by_cases h : √(gramSchmidtResidual A j ⬝ᵥ gramSchmidtResidual A j) = 0
  · rw [Real.sqrt_eq_zero (dotProduct_self_nonneg _)] at h
    rw [dotProduct_self_eq_zero.1 h, smul_zero]
  · rw [mul_inv_cancel₀ h, one_smul]

/-- The `Q` factor of classical Gram–Schmidt: column `j` is `q_j`. Trefethen–Bau 1997,
Alg. 7.1.
atlas: gram-schmidt -/
def gramSchmidtQ (A : Matrix m (Fin n) ℝ) : Matrix m (Fin n) ℝ :=
  Matrix.of fun i j => gramSchmidtCol A j i

/-- The `R` factor of classical Gram–Schmidt: `r_ij = q_iᵀ a_j` for `i < j`, `r_jj = ‖v_j‖`,
zero below the diagonal. Trefethen–Bau 1997, Alg. 7.1.
atlas: gram-schmidt -/
def gramSchmidtR (A : Matrix m (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i < j then gramSchmidtCol A i ⬝ᵥ A.col j
    else if i = j then √(gramSchmidtResidual A j ⬝ᵥ gramSchmidtResidual A j) else 0

/-- **Gram–Schmidt succeeds**: no residual `v_j` vanishes (every pivot `r_jj = ‖v_j‖` is
positive). Trefethen–Bau 1997, Lect. 7 (Thm 7.2, proof).
atlas: gram-schmidt -/
def GramSchmidtSucceeds (A : Matrix m (Fin n) ℝ) : Prop :=
  ∀ j, gramSchmidtResidual A j ≠ 0

/-- `R` is upper triangular (no hypothesis). Trefethen–Bau 1997, Alg. 7.1. -/
theorem isUpperTriangular_gramSchmidtR (A : Matrix m (Fin n) ℝ) :
    (gramSchmidtR A).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  simp only [gramSchmidtR, of_apply]
  rw [if_neg (not_lt.2 hij.le), if_neg (ne_of_gt hij)]

/-- The diagonal of `R` is nonnegative (no hypothesis). Trefethen–Bau 1997, Thm 7.1. -/
theorem gramSchmidtR_apply_self_nonneg (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    0 ≤ gramSchmidtR A j j := by
  simp only [gramSchmidtR, of_apply, lt_irrefl, if_false, if_true]
  exact Real.sqrt_nonneg _

/-- The diagonal of `R` is positive when Gram–Schmidt succeeds. Trefethen–Bau 1997, Thm 7.2. -/
theorem gramSchmidtR_apply_self_pos {A : Matrix m (Fin n) ℝ} (h : GramSchmidtSucceeds A)
    (j : Fin n) : 0 < gramSchmidtR A j j := by
  simp only [gramSchmidtR, of_apply, lt_irrefl, if_false, if_true]
  refine Real.sqrt_pos.2 (lt_of_le_of_ne (dotProduct_self_nonneg _) ?_)
  exact fun h0 => h j (dotProduct_self_eq_zero.1 h0.symm)

/-- **`QR = A` for classical Gram–Schmidt**, for every `A` (no success hypothesis: after a
breakdown `q_j = 0` and `r_jj = 0`, and `a_j` is still `∑_{i<j} r_ij q_i`).
Trefethen–Bau 1997, eq. (7.7)–(7.8).
atlas: gram-schmidt -/
theorem gramSchmidtQ_mul_gramSchmidtR (A : Matrix m (Fin n) ℝ) :
    gramSchmidtQ A * gramSchmidtR A = A := by
  ext i j
  have hv := congrFun (norm_smul_gramSchmidtCol A j) i
  rw [norm_toLp_eq_sqrt_dotProduct_self] at hv
  rw [Pi.smul_apply, smul_eq_mul, gramSchmidtResidual_apply] at hv
  simp only [mul_apply, gramSchmidtQ, gramSchmidtR, of_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.filter_filter]
  have h1 : Finset.univ.filter (fun k : Fin n => k < j) = Finset.Iio j := by
    ext k; simp
  have h2 : Finset.univ.filter (fun k : Fin n => ¬k < j ∧ k = j) = {j} := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ lt_irrefl _, h⟩⟩
  rw [h1, h2, Finset.sum_singleton]
  linear_combination hv + (Finset.sum_congr rfl fun k _ => mul_comm _ _ :
    ∑ k ∈ Finset.Iio j, gramSchmidtCol A k i * (gramSchmidtCol A k ⬝ᵥ A.col j) =
      ∑ k ∈ Finset.Iio j, (gramSchmidtCol A k ⬝ᵥ A.col j) * gramSchmidtCol A k i)

/-- Unfolding of the residual as a sum over `Finset.Iio j`. -/
theorem gramSchmidtResidual_eq_sum (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    gramSchmidtResidual A j =
      A.col j - ∑ k ∈ Finset.Iio j, (gramSchmidtCol A k ⬝ᵥ A.col j) • gramSchmidtCol A k := by
  rw [gramSchmidtResidual,
    Finset.sum_coe_sort (Finset.Iio j)
      (fun k => (gramSchmidtCol A k ⬝ᵥ A.col j) • gramSchmidtCol A k)]

/-- `q_jᵀ q_j` is `1` if `v_j ≠ 0` and `0` after a breakdown. Trefethen–Bau 1997, Alg. 7.1. -/
theorem gramSchmidtCol_dotProduct_self (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    gramSchmidtCol A j ⬝ᵥ gramSchmidtCol A j = if gramSchmidtResidual A j = 0 then 0 else 1 := by
  rw [gramSchmidtCol_eq, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  split_ifs with h
  · simp [h]
  · have hpos : 0 < gramSchmidtResidual A j ⬝ᵥ gramSchmidtResidual A j :=
      lt_of_le_of_ne (dotProduct_self_nonneg _) (fun h0 => h (dotProduct_self_eq_zero.1 h0.symm))
    rw [← mul_assoc, ← mul_inv, ← sq, norm_toLp_sq_eq_dotProduct_self, inv_mul_cancel₀ hpos.ne']

/-- **The Gram–Schmidt columns are pairwise orthogonal**, for every `A` (breakdowns included):
`q_iᵀ q_j = 0` for `i < j`. Trefethen–Bau 1997, Lect. 7; Golub–Van Loan 2013, §5.2.7.
Proof: induction on `j`; `q_iᵀ v_j = q_iᵀ a_j (1 − q_iᵀ q_i) = 0` since `q_iᵀ q_i ∈ {0, 1}` and
`q_i = 0` when it is `0`. -/
theorem gramSchmidtCol_dotProduct_of_lt (A : Matrix m (Fin n) ℝ) {i j : Fin n} (hij : i < j) :
    gramSchmidtCol A i ⬝ᵥ gramSchmidtCol A j = 0 := by
  suffices H : ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < k → i < j →
      gramSchmidtCol A i ⬝ᵥ gramSchmidtCol A j = 0 from H _ i j (Nat.lt_succ_self _) hij
  intro k
  induction k with
  | zero => intro i j hj; omega
  | succ k ih =>
    intro i j hj hij
    have hprev : ∀ a b : Fin n, a < j → b < j → a ≠ b →
        gramSchmidtCol A a ⬝ᵥ gramSchmidtCol A b = 0 := by
      intro a b ha hb hab
      rcases lt_or_gt_of_ne hab with h | h
      · exact ih a b (by have := Fin.lt_def.1 hb; omega) h
      · rw [dotProduct_comm]; exact ih b a (by have := Fin.lt_def.1 ha; omega) h
    rw [gramSchmidtCol_eq A j, dotProduct_smul, smul_eq_mul]
    suffices hv : gramSchmidtCol A i ⬝ᵥ gramSchmidtResidual A j = 0 by rw [hv, mul_zero]
    rw [gramSchmidtResidual_eq_sum, dotProduct_sub, dotProduct_sum]
    simp_rw [dotProduct_smul, smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_Iio.2 hij) fun b hb hbi =>
      by rw [hprev i b hij (Finset.mem_Iio.1 hb) (Ne.symm hbi), mul_zero],
      gramSchmidtCol_dotProduct_self]
    split_ifs with h
    · have : gramSchmidtCol A i = 0 := by rw [gramSchmidtCol_eq, h, smul_zero]
      simp [this]
    · simp

/-- **The Gram–Schmidt columns are orthonormal or zero**, for every `A`:
`QᵀQ = diag(1 if v_j ≠ 0, 0 if v_j = 0)`. Trefethen–Bau 1997, Lect. 7 (the `q_j` are
orthonormal); Golub–Van Loan 2013, §5.2.7. The zero-skipping form is ours (it makes the statement
unconditional).
atlas: gram-schmidt -/
theorem transpose_gramSchmidtQ_mul_self (A : Matrix m (Fin n) ℝ) :
    (gramSchmidtQ A)ᵀ * gramSchmidtQ A =
      diagonal fun j => if gramSchmidtResidual A j = 0 then 0 else 1 := by
  ext i j
  have hij : ((gramSchmidtQ A)ᵀ * gramSchmidtQ A) i j = gramSchmidtCol A i ⬝ᵥ gramSchmidtCol A j :=
    rfl
  rw [hij]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [gramSchmidtCol_dotProduct_of_lt A h, diagonal_apply_ne _ h.ne]
  · rw [gramSchmidtCol_dotProduct_self, diagonal_apply_eq]
  · rw [dotProduct_comm, gramSchmidtCol_dotProduct_of_lt A h, diagonal_apply_ne _ h.ne']

/-- `Q` has orthonormal columns when Gram–Schmidt succeeds. Trefethen–Bau 1997, Thm 7.1.
atlas: gram-schmidt -/
theorem hasOrthonormalCols_gramSchmidtQ {A : Matrix m (Fin n) ℝ} (h : GramSchmidtSucceeds A) :
    HasOrthonormalCols (gramSchmidtQ A) := by
  rw [hasOrthonormalCols_iff_conjTranspose_mul_self, Matrix.conjTranspose_eq_transpose_of_trivial,
    transpose_gramSchmidtQ_mul_self]
  simp [h _]

/-- **Realisation of classical Gram–Schmidt**: when it succeeds, `(gramSchmidtQ A,
gramSchmidtR A)` is a thin QR of `A` (with `r_jj > 0`, `gramSchmidtR_apply_self_pos`).
Trefethen–Bau 1997, Thm 7.1–7.2 (existence via Alg. 7.1); Golub–Van Loan 2013, §5.2.7.
atlas: gram-schmidt -/
theorem isQR_gramSchmidt {A : Matrix m (Fin n) ℝ} (h : GramSchmidtSucceeds A) :
    IsQR A (gramSchmidtQ A) (gramSchmidtR A) where
  eq := (gramSchmidtQ_mul_gramSchmidtR A).symm
  orth := hasOrthonormalCols_gramSchmidtQ h
  upper := isUpperTriangular_gramSchmidtR A

/-- `q_j ∈ span(a_0, …, a_j)` (every `A`). Trefethen–Bau 1997, eq. (7.1). -/
theorem gramSchmidtCol_mem_span (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    gramSchmidtCol A j ∈ Submodule.span ℝ (A.col '' Set.Iic j) := by
  suffices H : ∀ k : ℕ, ∀ j : Fin n, (j : ℕ) < k →
      gramSchmidtCol A j ∈ Submodule.span ℝ (A.col '' Set.Iic j) from H _ j (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    rw [gramSchmidtCol_eq, gramSchmidtResidual_eq_sum]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun l hl => ?_))
    · exact Submodule.subset_span ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩
    · have hlj := Finset.mem_Iio.1 hl
      refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (ih l ?_))
      · exact Set.image_mono (Set.Iic_subset_Iic.2 hlj.le)
      · have := Fin.lt_def.1 hlj; omega

/-- **A breakdown means a dependent column**: if `v_j = 0` then `a_j ∈ span(a_i : i < j)`.
Trefethen–Bau 1997, Lect. 7 (Thm 7.2, proof); Golub–Van Loan 2013, §5.2.7. -/
theorem mem_span_of_gramSchmidtResidual_eq_zero {A : Matrix m (Fin n) ℝ} {j : Fin n}
    (h : gramSchmidtResidual A j = 0) :
    A.col j ∈ Submodule.span ℝ (A.col '' Set.Iio j) := by
  rw [gramSchmidtResidual_eq_sum, sub_eq_zero] at h
  rw [h]
  refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
  exact Submodule.span_mono (Set.image_mono fun x hx =>
    Set.mem_Iio.2 (lt_of_le_of_lt (Set.mem_Iic.1 hx) (Finset.mem_Iio.1 hl)))
    (gramSchmidtCol_mem_span A l)

/-- `q_iᵀ q_j = 0` for `i ≠ j` (every `A`). Trefethen–Bau 1997, Lect. 7. -/
theorem gramSchmidtCol_dotProduct_of_ne (A : Matrix m (Fin n) ℝ) {i j : Fin n} (hij : i ≠ j) :
    gramSchmidtCol A i ⬝ᵥ gramSchmidtCol A j = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact gramSchmidtCol_dotProduct_of_lt A h
  · rw [dotProduct_comm]; exact gramSchmidtCol_dotProduct_of_lt A h

/-- `a_j ∈ span(q_0, …, q_j)` (every `A`). Trefethen–Bau 1997, eq. (7.2). -/
theorem col_mem_span_gramSchmidtCol (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    A.col j ∈ Submodule.span ℝ (gramSchmidtCol A '' Set.Iic j) := by
  have h : A.col j = gramSchmidtResidual A j +
      ∑ k ∈ Finset.Iio j, (gramSchmidtCol A k ⬝ᵥ A.col j) • gramSchmidtCol A k := by
    rw [gramSchmidtResidual_eq_sum]; abel
  rw [← norm_smul_gramSchmidtCol A j, norm_toLp_eq_sqrt_dotProduct_self] at h
  rw [h]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩))
    (Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l, Set.mem_Iic.2 (Finset.mem_Iio.1 hl).le, rfl⟩))

/-- Expansion in the Gram–Schmidt family: every `x ∈ span(q_i : i < j)` equals
`∑_{i<j} (q_iᵀ x) q_i` (the family is orthonormal or zero). -/
theorem eq_sum_of_mem_span_gramSchmidtCol (A : Matrix m (Fin n) ℝ) (j : Fin n) {x : m → ℝ}
    (hx : x ∈ Submodule.span ℝ (gramSchmidtCol A '' Set.Iio j)) :
    x = ∑ k ∈ Finset.Iio j, (gramSchmidtCol A k ⬝ᵥ x) • gramSchmidtCol A k := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_Iio.2 hl) fun k _ hkl => by
      rw [gramSchmidtCol_dotProduct_of_ne A hkl, zero_smul], gramSchmidtCol_dotProduct_self]
    split_ifs with h
    · rw [gramSchmidtCol_eq, h, smul_zero, zero_smul]
    · rw [one_smul]
  | zero => simp
  | add y z _ _ hy hz =>
    simp_rw [dotProduct_add, add_smul, Finset.sum_add_distrib]
    rw [← hy, ← hz]
  | smul c y _ hy =>
    simp_rw [dotProduct_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← hy]

/-- **Breakdown at step `j` iff `a_j` depends on the earlier columns**: `v_j = 0` iff
`a_j ∈ span(a_i : i < j)`, for every `A` (no assumption on the earlier steps).
Trefethen–Bau 1997, Lect. 7 (Thm 7.2, proof); Golub–Van Loan 2013, §5.2.7.
atlas: gram-schmidt -/
theorem gramSchmidtResidual_eq_zero_iff (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    gramSchmidtResidual A j = 0 ↔ A.col j ∈ Submodule.span ℝ (A.col '' Set.Iio j) := by
  refine ⟨mem_span_of_gramSchmidtResidual_eq_zero, fun hj => ?_⟩
  have hle : Submodule.span ℝ (A.col '' Set.Iio j) ≤
      Submodule.span ℝ (gramSchmidtCol A '' Set.Iio j) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact Submodule.span_mono (Set.image_mono fun x hx =>
      Set.mem_Iio.2 (lt_of_le_of_lt (Set.mem_Iic.1 hx) (Set.mem_Iio.1 hl)))
      (col_mem_span_gramSchmidtCol A l)
  rw [gramSchmidtResidual_eq_sum, sub_eq_zero]
  exact eq_sum_of_mem_span_gramSchmidtCol A j (hle hj)

/-- **Gram–Schmidt succeeds iff the columns of `A` are linearly independent.**
Trefethen–Bau 1997, Thm 7.2 (full rank case); Golub–Van Loan 2013, §5.2.7.
atlas: gram-schmidt -/
theorem gramSchmidtSucceeds_iff_linearIndependent (A : Matrix m (Fin n) ℝ) :
    GramSchmidtSucceeds A ↔ LinearIndependent ℝ A.col := by
  constructor
  · intro h
    have hQR := isQR_gramSchmidt h
    have hdet : IsUnit (gramSchmidtR A).det :=
      hQR.isUnit_det_iff.2 fun j => (gramSchmidtR_apply_self_pos h j).ne'
    have key : ((gramSchmidtR A)⁻¹ * (gramSchmidtQ A)ᵀ) * A = 1 := by
      have hR : (gramSchmidtQ A)ᵀ * A = gramSchmidtR A := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial (gramSchmidtQ A)] using
          hQR.conjTranspose_mul_eq
      rw [Matrix.mul_assoc, hR, Matrix.nonsing_inv_mul _ hdet]
    rw [← Matrix.mulVec_injective_iff]
    intro x y hxy
    have := congrArg (fun z => ((gramSchmidtR A)⁻¹ * (gramSchmidtQ A)ᵀ) *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, key, Matrix.one_mulVec] using this
  · intro hA j hj
    exact hA.notMem_span_image (lt_irrefl j) (mem_span_of_gramSchmidtResidual_eq_zero hj)

/-! ### Graded bases of the column flag -/

/-- `Q` is a **graded orthonormal basis of the column flag of `A`**: `Q` has orthonormal columns
and, for each `k`, its first `k + 1` columns span the first `k + 1` columns of `A`. The analogue
of `IsGradedKrylovBasis` (`NLAlib.Krylov.Processes.Arnoldi`) with `K_{k+1}(A, b)` replaced by
`span(a_0, …, a_k)`. Trefethen–Bau 1997, Lect. 7, eq. (7.1); Golub–Van Loan 2013, §5.2.
atlas: gram-schmidt -/
structure IsGradedColumnBasis (A Q : Matrix m (Fin n) ℝ) : Prop where
  /-- The columns are orthonormal. -/
  orth : HasOrthonormalCols Q
  /-- The first `k + 1` columns of `Q` span the first `k + 1` columns of `A`. -/
  nested : ∀ k : Fin n,
    Submodule.span ℝ (Set.range fun j : Fin (k + 1) => Q.col (Fin.castLE k.isLt j)) =
      Submodule.span ℝ (Set.range fun j : Fin (k + 1) => A.col (Fin.castLE k.isLt j))

/-- The first `k + 1` entries of a family on `Fin n`, as a `castLE` range, are its image of
`Iic k` (helper for the graded-basis form). -/
theorem range_castLE_eq_image_Iic {α : Type*} (f : Fin n → α) (k : Fin n) :
    Set.range (fun j : Fin (k + 1) => f (Fin.castLE k.isLt j)) = f '' Set.Iic k := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨_, Fin.le_def.2 (by simp only [Fin.val_castLE]; omega), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by have := Fin.le_def.1 hi; omega⟩, rfl⟩

/-- **Gram–Schmidt spans the column flag**: `span(q_0, …, q_k) = span(a_0, …, a_k)` for every
`k` and every `A` (zero columns after a breakdown do not change the span). Trefethen–Bau 1997,
eq. (7.1); Golub–Van Loan 2013, §5.2.7.
atlas: gram-schmidt -/
theorem span_gramSchmidtCol_image_Iic (A : Matrix m (Fin n) ℝ) (k : Fin n) :
    Submodule.span ℝ (gramSchmidtCol A '' Set.Iic k) =
      Submodule.span ℝ (A.col '' Set.Iic k) := by
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨l, hl, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hl))
      (gramSchmidtCol_mem_span A l)
  · exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hl))
      (col_mem_span_gramSchmidtCol A l)

/-- The column-flag property in the `IsGradedKrylovBasis` (`castLE`) form.
Trefethen–Bau 1997, eq. (7.1).
atlas: gram-schmidt -/
theorem span_gramSchmidtQ_castLE (A : Matrix m (Fin n) ℝ) (k : Fin n) :
    Submodule.span ℝ (Set.range fun j : Fin (k + 1) => (gramSchmidtQ A).col (Fin.castLE k.isLt j)) =
      Submodule.span ℝ (Set.range fun j : Fin (k + 1) => A.col (Fin.castLE k.isLt j)) := by
  rw [range_castLE_eq_image_Iic (gramSchmidtQ A).col, range_castLE_eq_image_Iic A.col]
  exact span_gramSchmidtCol_image_Iic A k

/-- **The Gram–Schmidt `Q` is the graded basis of the column flag** when the process succeeds.
Trefethen–Bau 1997, Lect. 7; Golub–Van Loan 2013, §5.2.7.
atlas: gram-schmidt -/
theorem isGradedColumnBasis_gramSchmidtQ {A : Matrix m (Fin n) ℝ} (h : GramSchmidtSucceeds A) :
    IsGradedColumnBasis A (gramSchmidtQ A) :=
  ⟨hasOrthonormalCols_gramSchmidtQ h, span_gramSchmidtQ_castLE A⟩

omit [Fintype m] in
/-- If `T` is upper triangular, column `j` of `Q T` lies in the span of the first `j + 1` columns
of `Q`. Golub–Van Loan 2013, §5.2 (column flags under triangular maps). -/
theorem col_mul_mem_span_image_Iic {Q : Matrix m (Fin n) ℝ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (j : Fin n) :
    (Q * T).col j ∈ Submodule.span ℝ (Q.col '' Set.Iic j) := by
  have h : (Q * T).col j = ∑ i, T i j • Q.col i := by
    ext r; simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [h]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hij : i ≤ j
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hij, rfl⟩)
  · rw [hT (lt_of_not_ge hij), zero_smul]; exact Submodule.zero_mem _

/-- **Every thin QR with invertible `R` is a graded basis of the column flag**: `A = QR` with
`R` upper triangular and `R_ii ≠ 0` gives `span(q_0, …, q_k) = span(a_0, …, a_k)`.
Trefethen–Bau 1997, eq. (7.1)–(7.2); Golub–Van Loan 2013, Thm 5.2.3. Proof: `A = QR` and
`Q = AR⁻¹` with `R⁻¹` upper triangular (`col_mul_mem_span_image_Iic`).
atlas: gram-schmidt -/
theorem IsQR.isGradedColumnBasis {A Q : Matrix m (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}
    (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) : IsGradedColumnBasis A Q := by
  have hdet : IsUnit R.det := h.isUnit_det_iff.2 hR
  have hQ : Q = A * R⁻¹ := by
    rw [h.eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hinv : R⁻¹.IsUpperTriangular := by
    have := R.invertibleOfIsUnitDet hdet; exact blockTriangular_inv_of_blockTriangular h.upper
  refine ⟨h.orth, fun k => ?_⟩
  rw [range_castLE_eq_image_Iic Q.col, range_castLE_eq_image_Iic A.col]
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨l, hl, rfl⟩
  · refine Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hl)) ?_
    rw [hQ]; exact col_mul_mem_span_image_Iic hinv l
  · refine Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hl)) ?_
    rw [h.eq]; exact col_mul_mem_span_image_Iic h.upper l

/-! ### Bridge to Mathlib -/

/-- **Bridge to Mathlib**: `q_j` is Mathlib's `gramSchmidtNormed` of the columns of `A`,
including every breakdown and zero-vector normalization.
Source: Trefethen–Bau, Algorithms 7.1 and 8.1; matrix toolkit rederivations, `sec:gs`.
Normalized rank-one projections identify the two recursions by strong induction.
atlas: gram-schmidt -/
theorem gramSchmidtCol_eq_gramSchmidtNormed (A : Matrix m (Fin n) ℝ) (j : Fin n) :
    gramSchmidtCol A j =
      (InnerProductSpace.gramSchmidtNormed ℝ (fun k => WithLp.toLp 2 (A.col k)) j).ofLp := by
  let f : Fin n → EuclideanSpace ℝ m := fun k => WithLp.toLp 2 (A.col k)
  suffices h : ∀ k : ℕ, ∀ j : Fin n, j.val < k →
      gramSchmidtCol A j = (InnerProductSpace.gramSchmidtNormed ℝ f j).ofLp from
    h (j.val + 1) j (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have hprev : ∀ i : Fin n, i < j →
        WithLp.toLp 2 (gramSchmidtCol A i) = InnerProductSpace.gramSchmidtNormed ℝ f i := by
      intro i hij
      rw [ih i (by have := Fin.lt_def.mp hij; omega), WithLp.toLp_ofLp]
    have hres : WithLp.toLp 2 (gramSchmidtResidual A j) = InnerProductSpace.gramSchmidt ℝ f j := by
      rw [gramSchmidtResidual_eq_sum, WithLp.toLp_sub, WithLp.toLp_sum,
        InnerProductSpace.gramSchmidt_def]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [starProjection_singleton_eq_inner_normalized_smul]
      change WithLp.toLp 2 ((gramSchmidtCol A i ⬝ᵥ A.col j) • gramSchmidtCol A i) =
        (inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ f i) (f j)) •
          InnerProductSpace.gramSchmidtNormed ℝ f i
      rw [WithLp.toLp_smul, ← hprev i (Finset.mem_Iio.mp hi)]
      simp only [f, EuclideanSpace.inner_toLp_toLp, star_trivial]
      rw [dotProduct_comm]
    have hnorm : ‖InnerProductSpace.gramSchmidt ℝ f j‖ =
        ‖(WithLp.toLp 2 (gramSchmidtResidual A j) : EuclideanSpace ℝ m)‖ := by
      rw [← hres]
    rw [gramSchmidtCol_eq, InnerProductSpace.gramSchmidtNormed, hnorm, ← hres,
      WithLp.ofLp_smul, WithLp.ofLp_toLp]
    simp only [RCLike.ofReal_real_eq_id, id_eq]

end NLAlib
