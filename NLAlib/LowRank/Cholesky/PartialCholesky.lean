/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Basic.SchurComplement
import NLAlib.Matrix.Basic.Selection
import NLAlib.Matrix.Factorizations.EliminationStep
import NLAlib.LowRank.Nystrom.Structural
import NLAlib.LowRank.Cholesky.CholeskyPivot
/-!
# Partial (pivoted) Cholesky and the column Nyström approximation

`k` steps of pivoted Cholesky with an arbitrary pivot sequence `s : Fin k → n` (chosen in
advance or adaptively by the caller: greedy, uniform, RPCholesky; the pivot rule is not part of
the recursion):

* the step `eliminationStep A t = A − A(:,t) A(t,:) / A(t,t)` (Matrix/Factorizations/EliminationStep;
  total: a zero pivot leaves `A` unchanged);
* `partialCholeskyResidual A s`: the residual after eliminating `s 0, …, s (k−1)` in order;
* `partialCholeskyFactor A s : Matrix n (Fin k) ℝ`: column `j` is
  `R_j(:, s j) / √R_j(s j, s j)` with `R_j` the residual before step `j`.

Results, for positive semidefinite `A` and any pivot sequence (no positivity condition on the
pivots, repeated pivots allowed):

* the residual is PSD and vanishes on the rows and columns of the pivots
  (`posSemidef_partialCholeskyResidual`, `partialCholeskyResidual_apply_pivot_left/right`);
* `A − F Fᵀ = residual` (`sub_partialCholeskyFactor_mul_transpose`);
* `F Fᵀ = A(:,S) A(S,S)⁺ A(S,:)`, the column Nyström approximation
  `nystrom A (selectionMatrix s)` (`partialCholeskyFactor_mul_transpose_eq_nystrom`), so the residual is the generalized
  Schur complement
  `A − A(:,S) A(S,S)⁺ A(S,:)` of `A(S,S)` (`partialCholeskyResidual_eq_sub_nystrom`).

Sources: Chen–Epperly–Tropp–Webber 2023 (RPCholesky), §2 (label to verify); Golub–Van Loan
2013, §4.2.9. Atlas: `partial-cholesky-nystrom`.
-/

noncomputable section

open scoped Matrix MatrixOrder
open Matrix

namespace NLAlib

variable {n : Type*}

/-- The **residual of partial Cholesky** after the pivots `s 0, …, s (k−1)`, in this order.
CETW 2023, Alg. 1 (residual update); Golub–Van Loan 2013, §4.2.9.
atlas: partial-cholesky-nystrom (partial) -/
def partialCholeskyResidual (A : Matrix n n ℝ) : {k : ℕ} → (Fin k → n) → Matrix n n ℝ
  | 0, _ => A
  | k + 1, s => eliminationStep (partialCholeskyResidual A (Fin.init s)) (s (Fin.last k))

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

variable [DecidableEq n] [Fintype n]

/-- The Nyström approximation with a selection matrix is the column Nyström approximation
`A(:,S) A(S,S)⁺ A(S,:)`. CETW 2023, §2; Gittens–Mahoney 2016, §2. -/
theorem nystrom_selectionMatrix {k : ℕ} (A : Matrix n n ℝ) (s : Fin k → n) :
    nystrom A (selectionMatrix s) =
      A.submatrix id s * moorePenroseInverse (A.submatrix s s) * A.submatrix s id := by
  have h : (selectionMatrix s)ᵀ * A * selectionMatrix s = A.submatrix s s := by
    rw [transpose_selectionMatrix_mul, mul_selectionMatrix]; rfl
  rw [nystrom, mul_selectionMatrix, h, transpose_selectionMatrix_mul]

/-- The partial Cholesky residual of a PSD matrix is PSD (each step is a Schur complement).
CETW 2023, §2; Golub–Van Loan 2013, §4.2.9.
atlas: partial-cholesky-nystrom (partial) -/
theorem posSemidef_partialCholeskyResidual {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (s : Fin k → n) : (partialCholeskyResidual A s).PosSemidef := by
  induction k with
  | zero => exact hA
  | succ k ih => exact posSemidef_eliminationStep (ih _) _

/-- Every partial Cholesky residual of a PSD matrix is bounded above by the matrix:
`A − R` is PSD. Source: manuscript `sa:rp-one-step`; CETW (2025), PSD order invariant. -/
theorem posSemidef_sub_partialCholeskyResidual {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (s : Fin k → n) : (A - partialCholeskyResidual A s).PosSemidef := by
  induction k with
  | zero =>
    simpa only [partialCholeskyResidual, sub_self] using (Matrix.PosSemidef.zero (n := n) (R := ℝ))
  | succ k ih =>
    have h := (ih (Fin.init s)).add
      (Matrix.le_iff.mp (eliminationStep_le (posSemidef_partialCholeskyResidual hA (Fin.init s))
        (s (Fin.last k))))
    convert h using 1
    dsimp only [partialCholeskyResidual]
    abel

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
    | last => exact eliminationStep_apply_pivot_left (posSemidef_partialCholeskyResidual hA _) _ _
    | cast j =>
      exact eliminationStep_apply_eq_zero_of_row (fun i => ih (Fin.init s) j i) _ _

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
    | last => exact eliminationStep_apply_pivot_right (posSemidef_partialCholeskyResidual hA _) _ _
    | cast j =>
      exact eliminationStep_apply_eq_zero_of_col (fun i => ih (Fin.init s) j i) _ _

/-- **Partial Cholesky residual identity**: `A − F Fᵀ` is the projResidual, for PSD `A` and any pivot
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
      partialCholeskyResidual, eliminationStep_apply]
    rw [← sub_sub, hij, div_mul_div_comm, hsq, hsym t j]
    ring

omit [DecidableEq n] [Fintype n] in
/-- A PSD matrix bordered by its selected rows and columns remains PSD. This is the
selection case used in the variational proof of the Nyström residual. -/
private theorem posSemidef_fromBlocks_choleskySelection {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {k : ℕ} (s : Fin k → n) :
    (Matrix.fromBlocks (A.submatrix s s) (A.submatrix s id)
      (A.submatrix s id)ᴴ A).PosSemidef := by
  have hblock : Matrix.fromBlocks (A.submatrix s s) (A.submatrix s id)
      (A.submatrix s id)ᴴ A = A.submatrix (Sum.elim s id) (Sum.elim s id) := by
    rw [Matrix.conjTranspose_submatrix, hA.isHermitian.eq]
    ext (i | i) (j | j) <;> rfl
  rw [hblock]
  exact hA.submatrix _

/-- The native Moore–Penrose compatibility identity makes every selected column of the
Nyström residual zero, including for singular cores and repeated selections. -/
private theorem sub_nystrom_choleskySelection_apply {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {k : ℕ} (s : Fin k → n) (i : n) (j : Fin k) :
    (A - nystrom A (selectionMatrix s)) i (s j) = 0 := by
  have h := one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef
    (posSemidef_fromBlocks_choleskySelection hA s)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  have ht := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_submatrix,
    hA.isHermitian.eq, (Matrix.IsHermitian.moorePenroseInverse (hA.submatrix s).isHermitian).eq,
    (hA.submatrix s).isHermitian.eq, ← Matrix.mul_assoc] at ht
  rw [nystrom_selectionMatrix, Matrix.sub_apply, sub_eq_zero]
  exact congrFun₂ ht i j

/-- The Nyström residual is the largest PSD matrix below the input whose selected columns
vanish. This is the native-Moore–Penrose translation of the frontend variational argument. -/
private theorem le_sub_nystrom_choleskySelection {A M : Matrix n n ℝ}
    (hM : M.PosSemidef) {k : ℕ} (s : Fin k → n) (hMA : M ≤ A)
    (hMe : ∀ i j, M i (s j) = 0) : M ≤ A - nystrom A (selectionMatrix s) := by
  have hMe' : ∀ j i, M (s j) i = 0 := fun j i => by
    rw [← hM.isHermitian.apply, hMe, star_zero]
  have h1 : (A - M).submatrix id s = A.submatrix id s := by
    ext i j
    simp [hMe]
  have h2 : (A - M).submatrix s id = A.submatrix s id := by
    ext j i
    simp [hMe']
  have h3 : (A - M).submatrix s s = A.submatrix s s := by
    ext j j'
    simp [hMe]
  have h := posSemidef_sub_nystrom (Matrix.le_iff.mp hMA) (selectionMatrix s)
  rw [nystrom_selectionMatrix, h1, h2, h3] at h
  rw [Matrix.le_iff, nystrom_selectionMatrix]
  have heq : A - A.submatrix id s * moorePenroseInverse (A.submatrix s s) *
      A.submatrix s id - M =
      A - M - A.submatrix id s * moorePenroseInverse (A.submatrix s s) * A.submatrix s id := by
    abel
  rw [heq]
  exact h

/-- Fin-indexed transfer of the frontend elimination-list theorem. The two Loewner bounds
use only PSD order and vanishing pivot columns; zero and repeated pivots require no exception. -/
private theorem partialCholeskyResidual_eq_sub_nystrom_selection {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {k : ℕ} (s : Fin k → n) :
    partialCholeskyResidual A s = A - nystrom A (selectionMatrix s) := by
  have hle : ∀ {k : ℕ} (s : Fin k → n), A - nystrom A (selectionMatrix s) ≤ A := by
    intro k s
    rw [Matrix.le_iff, sub_sub_cancel]
    exact posSemidef_nystrom hA _
  induction k with
  | zero =>
    ext i j
    simp [partialCholeskyResidual, nystrom]
  | succ k ih =>
    dsimp only [partialCholeskyResidual]
    rw [ih]
    have hR := posSemidef_sub_nystrom hA (selectionMatrix (Fin.init s))
    have hR' := posSemidef_sub_nystrom hA (selectionMatrix s)
    apply le_antisymm
    · refine le_sub_nystrom_choleskySelection (posSemidef_eliminationStep hR _) s
        ((eliminationStep_le hR _).trans (hle _)) ?_
      intro i j
      induction j using Fin.lastCases with
      | last => exact eliminationStep_apply_pivot_right hR _ i
      | cast j =>
        exact eliminationStep_apply_eq_zero_of_col
          (fun i => sub_nystrom_choleskySelection_apply hA (Fin.init s) i j) _ i
    · rw [eliminationStep_eq_sub_nystrom]
      change A - nystrom A (selectionMatrix s) ≤
        (A - nystrom A (selectionMatrix (Fin.init s))) -
          nystrom (A - nystrom A (selectionMatrix (Fin.init s)))
            (selectionMatrix (fun _ : Fin 1 => s (Fin.last k)))
      refine le_sub_nystrom_choleskySelection hR' (fun _ : Fin 1 => s (Fin.last k)) ?_
        (fun i _ => sub_nystrom_choleskySelection_apply hA s i (Fin.last k))
      exact le_sub_nystrom_choleskySelection hR' (Fin.init s) (hle s)
        (fun i j => sub_nystrom_choleskySelection_apply hA s i j.castSucc)

/-- **Partial Cholesky is column Nyström**: for PSD `A` and every pivot sequence `s`,
`F Fᵀ = A(:,S) A(S,S)⁺ A(S,:)`, including zero and repeated pivots.
CETW 2023, §2; Golub–Van Loan 2013, §4.2.9.
Proof transferred from `Matrix.PosSemidef.foldl_eliminationStep_eq_sub` in
`NLA-lib/NLAlib`, commit `6a845a2ec27f37c1a98118c107a06a13ce45273d`,
`NLAlib/Matrix/Factorizations/Nystrom.lean` (Apache 2.0, NLAlib contributors).
The source list induction is expressed using the existing native `Fin` recursion; the
variational characterization uses NLAlib's Moore–Penrose inverse without a rank assumption.
atlas: partial-cholesky-nystrom -/
theorem partialCholeskyFactor_mul_transpose_eq_nystrom {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {k : ℕ} (s : Fin k → n) :
    partialCholeskyFactor A s * (partialCholeskyFactor A s)ᵀ = nystrom A (selectionMatrix s) := by
  have h := sub_partialCholeskyFactor_mul_transpose hA s
  rw [partialCholeskyResidual_eq_sub_nystrom_selection hA s] at h
  exact sub_right_inj.mp h

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
