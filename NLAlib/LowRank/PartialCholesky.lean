import Mathlib.Analysis.Real.Sqrt
import NLAlib.Matrix.SchurComplement
import NLAlib.LowRank.Nystrom

/-!
# Partial (pivoted) Cholesky and the column Nyström approximation

`k` steps of pivoted Cholesky with an arbitrary pivot sequence `s : Fin k → n` (chosen in
advance or adaptively by the caller: greedy, uniform, RPCholesky; the pivot rule is not part of
the recursion):

* `choleskyStep A t = A − A(:,t) A(t,:) / A(t,t)` (total: a zero pivot leaves `A` unchanged);
* `partialCholeskyResidual A s`: the residual after eliminating `s 0, …, s (k−1)` in order;
* `partialCholeskyFactor A s : Matrix n (Fin k) ℝ`: column `j` is
  `R_j(:, s j) / √R_j(s j, s j)` with `R_j` the residual before step `j`.

Results, for positive semidefinite `A` and any pivot sequence (no positivity condition on the
pivots, repeated pivots allowed):

* the residual is PSD and vanishes on the rows and columns of the pivots
  (`posSemidef_partialCholeskyResidual`, `partialCholeskyResidual_apply_pivot_left/right`);
* `A − F Fᵀ = residual` (`sub_partialCholeskyFactor_mul_transpose`);
* `F Fᵀ = A(:,S) A(S,S)⁺ A(S,:)`, the column Nyström approximation
  `nystrom A (selectionMatrix s)` (`partialCholeskyFactor_mul_transpose_eq_nystrom`, the one
  scaffold of this file), so the residual is the generalized Schur complement
  `A − A(:,S) A(S,S)⁺ A(S,:)` of `A(S,S)` (`partialCholeskyResidual_eq_sub_nystrom`).

Sources: Chen–Epperly–Tropp–Webber 2023 (RPCholesky), §2 (label to verify); Golub–Van Loan
2013, §4.2.9. Atlas: `partial-cholesky-nystrom`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*}

/-- **One step of (pivoted) Cholesky elimination** on pivot `t`:
`A − A(:,t) A(t,:) / A(t,t)`, the Schur complement of `A(t,t)` padded with a zero row and column
at `t`. Total: for `A(t,t) = 0` it returns `A`. Golub–Van Loan 2013, §4.2.9; CETW 2023, §2. -/
def choleskyStep (A : Matrix n n ℝ) (t : n) : Matrix n n ℝ :=
  A - (A t t)⁻¹ • vecMulVec (fun i => A i t) fun j => A t j

/-- Entrywise form of a Cholesky step: `aᵢⱼ − aᵢₜ aₜⱼ / aₜₜ`. -/
@[simp]
theorem choleskyStep_apply (A : Matrix n n ℝ) (t i j : n) :
    choleskyStep A t i j = A i j - (A t t)⁻¹ * (A i t * A t j) := by
  simp [choleskyStep, vecMulVec_apply]

/-- The **residual of partial Cholesky** after the pivots `s 0, …, s (k−1)`, in this order.
CETW 2023, Alg. 1 (residual update); Golub–Van Loan 2013, §4.2.9.
atlas: partial-cholesky-nystrom (partial) -/
def partialCholeskyResidual (A : Matrix n n ℝ) : {k : ℕ} → (Fin k → n) → Matrix n n ℝ
  | 0, _ => A
  | k + 1, s => choleskyStep (partialCholeskyResidual A (Fin.init s)) (s (Fin.last k))

/-- The **partial Cholesky factor** `F ∈ ℝ^{n×k}`: column `j` is `R(:, s j) / √R(s j, s j)` with
`R` the residual after the first `j` pivots. CETW 2023, Alg. 1; Golub–Van Loan 2013, §4.2.9.
atlas: partial-cholesky-nystrom (partial) -/
def partialCholeskyFactor (A : Matrix n n ℝ) {k : ℕ} (s : Fin k → n) : Matrix n (Fin k) ℝ :=
  Matrix.of fun i j =>
    partialCholeskyResidual A (fun t : Fin j => s (Fin.castLE j.isLt.le t)) i (s j) /
      Real.sqrt (partialCholeskyResidual A (fun t : Fin j => s (Fin.castLE j.isLt.le t)) (s j)
        (s j))

/-- The first `k` columns of the factor for `k + 1` pivots are the factor for the first `k`
pivots. -/
theorem partialCholeskyFactor_castSucc (A : Matrix n n ℝ) {k : ℕ} (s : Fin (k + 1) → n)
    (i : n) (j : Fin k) :
    partialCholeskyFactor A s i j.castSucc = partialCholeskyFactor A (Fin.init s) i j := rfl

/-- The last column of the factor is the scaled pivot column of the current residual. -/
theorem partialCholeskyFactor_last (A : Matrix n n ℝ) {k : ℕ} (s : Fin (k + 1) → n) (i : n) :
    partialCholeskyFactor A s i (Fin.last k) =
      partialCholeskyResidual A (Fin.init s) i (s (Fin.last k)) /
        Real.sqrt (partialCholeskyResidual A (Fin.init s) (s (Fin.last k)) (s (Fin.last k))) :=
  rfl

variable [DecidableEq n]

/-- The **column-selection matrix** `[e_{s 0}, …, e_{s (k−1)}] ∈ ℝ^{n×k}`, so that
`A (selectionMatrix s) = A(:,S)` (`mul_selectionMatrix`) and the Nyström approximation with this
test matrix is the column Nyström approximation `A(:,S) A(S,S)⁺ A(S,:)`. -/
def selectionMatrix {k : ℕ} (s : Fin k → n) : Matrix n (Fin k) ℝ :=
  Matrix.of fun i j => if i = s j then 1 else 0

variable [Fintype n]

/-- Right multiplication by a selection matrix selects columns: `A (selectionMatrix s) = A(:,S)`. -/
theorem mul_selectionMatrix {m : Type*} {k : ℕ} (A : Matrix m n ℝ) (s : Fin k → n) :
    A * selectionMatrix s = A.submatrix id s := by
  ext i j; simp [selectionMatrix, Matrix.mul_apply]

/-- Left multiplication by the transpose of a selection matrix selects rows:
`(selectionMatrix s)ᵀ A = A(S,:)`. -/
theorem transpose_selectionMatrix_mul {m : Type*} [Fintype m] {k : ℕ} (A : Matrix n m ℝ)
    (s : Fin k → n) : (selectionMatrix s)ᵀ * A = A.submatrix s id := by
  ext i j; simp [selectionMatrix, Matrix.mul_apply]

/-- The Nyström approximation with a selection matrix is the column Nyström approximation
`A(:,S) A(S,S)⁺ A(S,:)`. CETW 2023, §2; Gittens–Mahoney 2016, §2. -/
theorem nystrom_selectionMatrix {k : ℕ} (A : Matrix n n ℝ) (s : Fin k → n) :
    nystrom A (selectionMatrix s) =
      A.submatrix id s * moorePenroseInverse (A.submatrix s s) * A.submatrix s id := by
  have h : (selectionMatrix s)ᵀ * A * selectionMatrix s = A.submatrix s s := by
    rw [transpose_selectionMatrix_mul, mul_selectionMatrix]; rfl
  rw [nystrom, mul_selectionMatrix, h, transpose_selectionMatrix_mul]

omit [DecidableEq n] in
/-- The quadratic form of a Cholesky step: `xᵀ (A − A(:,t) A(t,:) / A(t,t)) x =
xᵀ A x − (xᵀ A(:,t)) (A(t,:) x) / A(t,t)`. -/
theorem dotProduct_choleskyStep_mulVec (A : Matrix n n ℝ) (t : n) (x : n → ℝ) :
    x ⬝ᵥ choleskyStep A t *ᵥ x =
      x ⬝ᵥ A *ᵥ x - (A t t)⁻¹ * ((∑ i, x i * A i t) * ∑ j, A t j * x j) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  simp only [dotProduct, mulVec, choleskyStep_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- One Cholesky step preserves positive semidefiniteness, for any pivot (for `A(t,t) = 0` the
step is the identity). Proof: `xᵀ (choleskyStep A t) x = zᵀ A z` at
`z = x − (A(t,:) x / A(t,t)) eₜ`. Golub–Van Loan 2013, §4.2.8; special case of Albert 1969,
Thm 1 (atlas `generalized-schur-complement-psd`). -/
theorem posSemidef_choleskyStep {A : Matrix n n ℝ} (hA : A.PosSemidef) (t : n) :
    (choleskyStep A t).PosSemidef := by
  have hsym : ∀ i j, A i j = A j i := fun i j => by
    have := congrFun (congrFun hA.isHermitian j) i
    simpa using this
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, choleskyStep_apply]
    rw [hsym j i, hsym j t, hsym t i]; ring
  · set α := -((A t t)⁻¹ * ∑ j, A t j * x j) with hα
    have hx := (posSemidef_iff_dotProduct_mulVec.1 hA).2 (x + α • Pi.single t 1)
    have hexp : (x + α • Pi.single t 1) ⬝ᵥ A *ᵥ (x + α • Pi.single t 1) =
        x ⬝ᵥ A *ᵥ x + α * (∑ i, x i * A i t) + α * (∑ j, A t j * x j) + α ^ 2 * A t t := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      simp [dotProduct, mulVec, Pi.single_apply]
      ring
    have hs : ∑ i, x i * A i t = ∑ j, A t j * x j :=
      Finset.sum_congr rfl fun i _ => by rw [hsym i t, mul_comm]
    simp only [star_trivial] at hx ⊢
    rw [hexp, hs] at hx
    rw [dotProduct_choleskyStep_mulVec, hs]
    have key : α ^ 2 * A t t = (A t t)⁻¹ * ((∑ j, A t j * x j) * ∑ j, A t j * x j) := by
      rw [hα]
      by_cases ha : A t t = 0
      · simp [ha]
      · field_simp
    have key2 : α * ∑ j, A t j * x j = -((A t t)⁻¹ * ((∑ j, A t j * x j) * ∑ j, A t j * x j)) := by
      rw [hα]; ring
    linarith

/-- After a Cholesky step on a PSD matrix the pivot row vanishes. -/
theorem choleskyStep_apply_pivot_left {A : Matrix n n ℝ} (hA : A.PosSemidef) (t j : n) :
    choleskyStep A t t j = 0 := by
  rw [choleskyStep_apply]
  by_cases h : A t t = 0
  · rw [apply_eq_zero_of_posSemidef_of_apply_self_eq_zero' hA h j]; simp
  · field_simp; ring

/-- After a Cholesky step on a PSD matrix the pivot column vanishes. -/
theorem choleskyStep_apply_pivot_right {A : Matrix n n ℝ} (hA : A.PosSemidef) (t i : n) :
    choleskyStep A t i t = 0 := by
  rw [choleskyStep_apply]
  by_cases h : A t t = 0
  · rw [apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA h i]; simp
  · field_simp; ring

/-- The partial Cholesky residual of a PSD matrix is PSD (each step is a Schur complement).
CETW 2023, §2; Golub–Van Loan 2013, §4.2.9.
atlas: partial-cholesky-nystrom (partial) -/
theorem posSemidef_partialCholeskyResidual {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (s : Fin k → n) : (partialCholeskyResidual A s).PosSemidef := by
  induction k with
  | zero => exact hA
  | succ k ih => exact posSemidef_choleskyStep (ih _) _

omit [DecidableEq n] [Fintype n] in
/-- A Cholesky step keeps zero rows zero. -/
theorem choleskyStep_apply_eq_zero_of_row {A : Matrix n n ℝ} {u : n} (hu : ∀ j, A u j = 0)
    (t j : n) : choleskyStep A t u j = 0 := by
  simp [hu]

omit [DecidableEq n] [Fintype n] in
/-- A Cholesky step keeps zero columns zero. -/
theorem choleskyStep_apply_eq_zero_of_col {A : Matrix n n ℝ} {u : n} (hu : ∀ i, A i u = 0)
    (t i : n) : choleskyStep A t i u = 0 := by
  simp [hu]

/-- The partial Cholesky residual of a PSD matrix vanishes on the pivot rows.
CETW 2023, §2.
atlas: partial-cholesky-nystrom (partial) -/
theorem partialCholeskyResidual_apply_pivot_left {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (s : Fin k → n) (j : Fin k) (i : n) : partialCholeskyResidual A s (s j) i = 0 := by
  induction k generalizing i with
  | zero => exact j.elim0
  | succ k ih =>
    simp only [partialCholeskyResidual]
    induction j using Fin.lastCases with
    | last => exact choleskyStep_apply_pivot_left (posSemidef_partialCholeskyResidual hA _) _ _
    | cast j =>
      exact choleskyStep_apply_eq_zero_of_row (fun i => ih (Fin.init s) j i) _ _

/-- The partial Cholesky residual of a PSD matrix vanishes on the pivot columns.
CETW 2023, §2.
atlas: partial-cholesky-nystrom (partial) -/
theorem partialCholeskyResidual_apply_pivot_right {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {k : ℕ} (s : Fin k → n) (j : Fin k) (i : n) : partialCholeskyResidual A s i (s j) = 0 := by
  induction k generalizing i with
  | zero => exact j.elim0
  | succ k ih =>
    simp only [partialCholeskyResidual]
    induction j using Fin.lastCases with
    | last => exact choleskyStep_apply_pivot_right (posSemidef_partialCholeskyResidual hA _) _ _
    | cast j =>
      exact choleskyStep_apply_eq_zero_of_col (fun i => ih (Fin.init s) j i) _ _

/-- **Partial Cholesky residual identity**: `A − F Fᵀ` is the residual, for PSD `A` and any pivot
sequence. Proof: induction on `k`; the new column `f` satisfies
`f fᵀ = R(:,t) R(t,:) / R(t,t)` (`√x² = x` for the PSD diagonal, symmetry of `R`).
CETW 2023, §2; Golub–Van Loan 2013, §4.2.9.
atlas: partial-cholesky-nystrom (partial) -/
theorem sub_partialCholeskyFactor_mul_transpose {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (s : Fin k → n) :
    A - partialCholeskyFactor A s * (partialCholeskyFactor A s)ᵀ =
      partialCholeskyResidual A s := by
  induction k with
  | zero => ext i j; simp [partialCholeskyResidual]
  | succ k ih =>
    set R := partialCholeskyResidual A (Fin.init s) with hR
    set t := s (Fin.last k) with ht
    have hRpsd : R.PosSemidef := posSemidef_partialCholeskyResidual hA _
    have hsym : ∀ i j, R i j = R j i := fun i j => by
      have := congrFun (congrFun hRpsd.isHermitian j) i
      simpa using this
    have htt : 0 ≤ R t t := hRpsd.diag_nonneg
    have hsq : Real.sqrt (R t t) * Real.sqrt (R t t) = R t t := Real.mul_self_sqrt htt
    have hih := congrFun₂ (ih (Fin.init s))
    ext i j
    have hij := hih i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, transpose_apply] at hij ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [partialCholeskyFactor_castSucc, partialCholeskyFactor_last, ← hR, ← ht,
      partialCholeskyResidual, choleskyStep_apply]
    rw [← sub_sub, hij, div_mul_div_comm, hsq, hsym t j]
    ring

/-- SCAFFOLD: partial-cholesky-nystrom
**Partial Cholesky is column Nyström**: for PSD `A` and any pivot sequence `s`,
`F Fᵀ = A(:,S) A(S,S)⁺ A(S,:)`, the Nyström approximation with the selection matrix of `S`.
CETW 2023, §2 (label to verify); Golub–Van Loan 2013, §4.2.9.
Proof sketch: write `A = GᵀG` (`exists_eq_transpose_mul_of_posSemidef`). Partial Cholesky on
`A` is Gram–Schmidt on the columns `G(:, s 0), G(:, s 1), …` in order: by induction the
residual is `Gᵀ (I − Pⱼ) G` with `Pⱼ` the orthogonal projector onto the span of the first `j`
pivot columns of `G` (a zero pivot means the column is already in the span). Hence
`F Fᵀ = Gᵀ P_k G`, and `nystrom_eq_of_eq_transpose_mul` gives `nystrom A Ω = Gᵀ P G` with
`P` the projector onto `range (G Ω) = span {G(:, s j)}`.
atlas: partial-cholesky-nystrom -/
theorem partialCholeskyFactor_mul_transpose_eq_nystrom {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {k : ℕ} (s : Fin k → n) :
    partialCholeskyFactor A s * (partialCholeskyFactor A s)ᵀ = nystrom A (selectionMatrix s) := by
  sorry

/-- **The partial Cholesky residual is the generalized Schur complement**:
`R = A − A(:,S) A(S,S)⁺ A(S,:)`, for PSD `A` and any pivot sequence. With
`posSemidef_partialCholeskyResidual` and `partialCholeskyResidual_apply_pivot_left/right`, the
residual is PSD and zero on the rows and columns of `S`. CETW 2023, §2; Golub–Van Loan 2013,
§4.2.9.
atlas: partial-cholesky-nystrom -/
theorem partialCholeskyResidual_eq_sub_nystrom {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (s : Fin k → n) :
    partialCholeskyResidual A s =
      A - A.submatrix id s * moorePenroseInverse (A.submatrix s s) * A.submatrix s id := by
  rw [← sub_partialCholeskyFactor_mul_transpose hA,
    partialCholeskyFactor_mul_transpose_eq_nystrom hA, nystrom_selectionMatrix]

end NLAlib
