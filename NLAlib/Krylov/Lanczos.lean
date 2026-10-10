import NLAlib.Krylov.ArnoldiProcess

/-!
# The Arnoldi relation and the Lanczos three-term recurrence

For an Arnoldi decomposition `D : ArnoldiDecomp A b (q + 1)` (`NLAlib.Krylov.Arnoldi`) with
leading part `D_q = D.restrict _` (`Q_q`, `H_q`):

* `ArnoldiDecomp.mul_restrict_Q_eq_mul`: `A Q_q = Q_{q+1} H̲_q` with `H̲_q = Q_{q+1}ᵀ A Q_q`;
* `ArnoldiDecomp.mul_restrict_Q_eq_add_vecMulVec`, `ArnoldiDecomp.mul_restrict_Q_eq_add_smul`:
  the **Arnoldi relation** `A Q_q = Q_q H_q + h_{q+1,q} q_{q+1} e_qᵀ`;
* `ArnoldiDecomp.mul_Q_eq_mul_H_iff`: breakdown, `A Q_q = Q_q H_q ↔ q = krylovGrade A b`;
* `ArnoldiDecomp.mulVec_col_eq_sum`: the column form `A q_j = ∑ᵢ h_ij qᵢ`;
* `LanczosDecomp.mul_restrict_Q_eq_add_beta_smul`: the Lanczos form
  `A Q_q = Q_q T_q + β_q q_{q+1} e_qᵀ`;
* `LanczosDecomp.mulVec_vec_eq`: for symmetric `A`, the **Lanczos three-term recurrence**
  `A q_j = β_j q_{j−1} + α_j q_j + β_{j+1} q_{j+1}` with `α_j = t_jj`, `β_j = t_{j,j−1}`
  (`LanczosDecomp.alpha`, `LanczosDecomp.beta`), `β_j ≠ 0`, and `β_j > 0` for the canonical
  decomposition `arnoldiDecomp`;
* `LanczosDecomp.dotProduct_aeval_mulVec_eq`: Gauss–Lanczos quadrature through `T`,
  `bᵀ p(A) b = ‖b‖² (p(T_q))₁₁` for `deg p < 2q`.

Source: Saad (2003) [`saad03`], Props 6.5–6.6; Trefethen–Bau (1997) [`tb97`], Lect. 33 and 36;
Golub–Meurant (2010) [`gm10`], Ch. 4 (Thm 4.2) and Thm 6.6.
Atlas: `arnoldi-relation`, `lanczos-recurrence`, `lanczos-gauss-quadrature`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Column `j` of a product: `(M N)_{:,j} = M N_{:,j}`. Helper for `arnoldi-relation`. -/
theorem col_mul {k l : Type*} [Fintype k] (M : Matrix n k ℝ) (N : Matrix k l ℝ) (j : l) :
    (M * N).col j = M *ᵥ N.col j := by
  ext r
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]

namespace ArnoldiDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- **Column form of the Arnoldi relation**: `A q_j = ∑ᵢ h_ij qᵢ` whenever `j + 1 < q` (then
`A q_j ∈ K_{j+2} ⊆ K_q`); by `H_apply_eq_zero_of_add_one_lt` only `i ≤ j + 1` contribute.
Source: Saad (2003) [`saad03`], Prop. 6.5.
atlas: arnoldi-relation (partial) -/
theorem mulVec_col_eq_sum (D : ArnoldiDecomp A b q) {j : Fin q} (hj : (j : ℕ) + 1 < q) :
    A *ᵥ D.Q.col j = ∑ i, D.H i j • D.Q.col i := by
  have hmem : A *ᵥ D.Q.col j ∈ krylovSpace A b q :=
    krylovSpace_mono A b (show (j : ℕ) + 2 ≤ q by omega) (D.graded.mulVec_col_mem j)
  conv_lhs => rw [D.graded.eq_sum_of_mem hmem]
  simp only [H_apply]

/-- **`A Q_q = Q_{q+1} H̲_q`** with `H̲_q = Q_{q+1}ᵀ A Q_q` (the `(q+1) × q` Hessenberg matrix),
with no hypothesis beyond the decomposition of size `q + 1`. Source: Saad (2003) [`saad03`],
Prop. 6.5, eq. (6.8).
atlas: arnoldi-relation (partial) -/
theorem mul_restrict_Q_eq_mul (D : ArnoldiDecomp A b (q + 1)) :
    A * (D.restrict q.le_succ).Q = D.Q * (D.Qᵀ * A * (D.restrict q.le_succ).Q) := by
  ext r j
  have hmem : A *ᵥ (D.restrict q.le_succ).Q.col j ∈ LinearMap.range D.Q.mulVecLin := by
    rw [D.range_Q]
    exact krylovSpace_mono A b (show (j : ℕ) + 2 ≤ q + 1 by omega)
      ((D.restrict q.le_succ).graded.mulVec_col_mem j)
  have h := congrFun (mulVec_transpose_mulVec_of_mem_range D.hasOrthonormalCols hmem) r
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (A * (D.restrict q.le_succ).Q).col j r =
    (D.Q * D.Qᵀ * A * (D.restrict q.le_succ).Q).col j r
  rw [col_mul, col_mul, ← h]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **The Arnoldi relation** (outer-product form): `A Q_q = Q_q H_q + q_{q+1} h̲ᵀ` where
`h̲ = (h_{q+1,1}, …, h_{q+1,q})` is the last row of `H̲_q`. No hypothesis beyond the
decomposition of size `q + 1`; by the Hessenberg structure `h̲ = h_{q+1,q} e_q`
(`mul_restrict_Q_eq_add_smul`). Source: Saad (2003) [`saad03`], Prop. 6.5, eq. (6.7);
Trefethen–Bau (1997) [`tb97`], Lect. 33, eq. (33.13).
atlas: arnoldi-relation (partial) -/
theorem mul_restrict_Q_eq_add_vecMulVec (D : ArnoldiDecomp A b (q + 1)) :
    A * (D.restrict q.le_succ).Q = (D.restrict q.le_succ).Q * (D.restrict q.le_succ).H +
      vecMulVec (D.Q.col (Fin.last q)) (fun j => D.H (Fin.last q) j.castSucc) := by
  rw [mul_restrict_Q_eq_mul]
  ext r j
  rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mul_apply,
    vecMulVec_apply]
  congr 1

/-- **The Arnoldi relation** `A Q_q = Q_q H_q + h_{q+1,q} q_{q+1} e_qᵀ` (for `q ≥ 1`; `e_q` is
the last unit vector of `ℝ^q`). Source: Saad (2003) [`saad03`], Prop. 6.5, eq. (6.7);
Trefethen–Bau (1997) [`tb97`], Lect. 33; Golub–Meurant (2010) [`gm10`], Thm 4.2.
atlas: arnoldi-relation -/
theorem mul_restrict_Q_eq_add_smul (D : ArnoldiDecomp A b (q + 1)) (hq : 0 < q) :
    A * (D.restrict q.le_succ).Q = (D.restrict q.le_succ).Q * (D.restrict q.le_succ).H +
      D.H (Fin.last q) ⟨q - 1, by omega⟩ •
        vecMulVec (D.Q.col (Fin.last q)) (Pi.single (⟨q - 1, by omega⟩ : Fin q) 1) := by
  rw [mul_restrict_Q_eq_add_vecMulVec]
  congr 1
  ext r j
  rw [vecMulVec_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) = q - 1
  · have hj' : j.castSucc = ⟨q - 1, by omega⟩ := Fin.ext (by simp [hj])
    rw [Pi.single_apply, if_pos (Fin.ext hj), hj']
    ring
  · rw [Pi.single_eq_of_ne (fun h => hj (by rw [h])), mul_zero, mul_zero,
      D.H_apply_eq_zero_of_add_one_lt (by simp; omega), mul_zero]

/-- **Breakdown**: when `q` reaches the grade, `K_q` is `A`-invariant and the Arnoldi relation
closes, `A Q_q = Q_q H_q`. Source: Saad (2003) [`saad03`], Prop. 6.6.
atlas: arnoldi-relation (partial) -/
theorem mul_Q_eq_of_krylovGrade_le (D : ArnoldiDecomp A b q) (h : krylovGrade A b ≤ q) :
    A * D.Q = D.Q * D.H := by
  ext r j
  have hmem : A *ᵥ D.Q.col j ∈ LinearMap.range D.Q.mulVecLin := by
    rw [D.range_Q]
    have hj := krylovSpace_le_krylovSpace_krylovGrade A b _ (D.graded.col_mem j)
    rw [krylovSpace_eq_of_krylovGrade_le A b h]
    exact mulVec_mem_krylovSpace_krylovGrade A b hj
  have h := congrFun (mulVec_transpose_mulVec_of_mem_range D.hasOrthonormalCols hmem) r
  rw [H_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (A * D.Q).col j r = (D.Q * D.Qᵀ * A * D.Q).col j r
  rw [col_mul, col_mul, ← h]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Breakdown characterisation**: for `q ≥ 1`, the Arnoldi relation closes (`A Q_q = Q_q H_q`,
`K_q` is `A`-invariant) iff `q` is the grade of `b`. Source: Saad (2003) [`saad03`],
Prop. 6.6.
atlas: arnoldi-relation (partial) -/
theorem mul_Q_eq_mul_H_iff (D : ArnoldiDecomp A b q) (hq : 0 < q) :
    A * D.Q = D.Q * D.H ↔ krylovGrade A b = q := by
  refine ⟨fun h => le_antisymm ?_ D.le_krylovGrade, fun h => D.mul_Q_eq_of_krylovGrade_le h.le⟩
  -- `range Q = K_q` is `A`-invariant, so it contains every `A^i b`
  have hinv : ∀ x ∈ krylovSpace A b q, A *ᵥ x ∈ krylovSpace A b q := by
    intro x hx
    rw [← D.range_Q] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨D.H *ᵥ y, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]
  have hpow : ∀ i : ℕ, (A ^ i) *ᵥ b ∈ krylovSpace A b q := by
    intro i
    induction i with
    | zero => simpa using pow_mulVec_mem_krylovSpace A b hq
    | succ i ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hinv _ ih
  exact krylovGrade_le_of_pow_mulVec_mem A b (hpow q)

/-- Two vectors of `K_q(A, b)` with the same coordinates `qᵢ ⬝ x` in a graded basis are equal.
Atlas: `graded-krylov-basis-def`. -/
theorem eq_of_forall_col_dotProduct_eq (D : ArnoldiDecomp A b q) {x y : n → ℝ}
    (hx : x ∈ krylovSpace A b q) (hy : y ∈ krylovSpace A b q)
    (h : ∀ i, D.Q.col i ⬝ᵥ x = D.Q.col i ⬝ᵥ y) : x = y := by
  rw [D.graded.eq_sum_of_mem hx, D.graded.eq_sum_of_mem hy]
  simp only [h]

/-- The starting vector has coordinates supported on the first index: `(Q_qᵀ b)_i = 0` for
`i > 0` (`b ∈ K_1 ⊆ K_i ⟂ qᵢ`). Source: Saad (2003) [`saad03`], Alg. 6.1 (`q₁ = b/‖b‖`).
Atlas: `arnoldi-def`. -/
theorem transpose_Q_mulVec_apply_eq_zero (D : ArnoldiDecomp A b q) {i : Fin q}
    (hi : 0 < (i : ℕ)) : (D.Qᵀ *ᵥ b) i = 0 := by
  have hb : b ∈ krylovSpace A b i := by simpa using pow_mulVec_mem_krylovSpace A b (i := 0) hi
  exact D.graded.col_dotProduct_eq_zero i hb

/-- `(q_1 ⬝ b)² = ‖b‖²`, i.e. `q_1 = ± b/‖b‖`. Source: Saad (2003) [`saad03`], Alg. 6.1.
Atlas: `arnoldi-def`. -/
theorem sq_transpose_Q_mulVec_apply_zero (D : ArnoldiDecomp A b q) (hq : 0 < q) :
    (D.Qᵀ *ᵥ b) ⟨0, hq⟩ ^ 2 = b ⬝ᵥ b := by
  have hb : b ∈ LinearMap.range D.Q.mulVecLin := by
    rw [D.range_Q]; simpa using pow_mulVec_mem_krylovSpace A b (i := 0) hq
  have h1 : (D.Qᵀ *ᵥ b) ⬝ᵥ (D.Qᵀ *ᵥ b) = b ⬝ᵥ b := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      mulVec_transpose_mulVec_of_mem_range D.hasOrthonormalCols hb]
  rw [← h1, dotProduct, Finset.sum_eq_single (⟨0, hq⟩ : Fin q), sq]
  · intro i _ hi
    rw [D.transpose_Q_mulVec_apply_eq_zero (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)),
      mul_zero]
  · simp

end ArnoldiDecomp

/-- A quadratic form at a vector supported on one index: `c ⬝ M c = c_{i₀}² M_{i₀ i₀}`.
Helper for `lanczos-gauss-quadrature`. -/
theorem dotProduct_mulVec_eq_of_apply_eq_zero {k : Type*} [Fintype k] [DecidableEq k]
    (M : Matrix k k ℝ) {c : k → ℝ} (i₀ : k) (hc : ∀ i, i ≠ i₀ → c i = 0) :
    c ⬝ᵥ (M *ᵥ c) = c i₀ ^ 2 * M i₀ i₀ := by
  have hc' : c = Pi.single i₀ (c i₀) := by
    ext i
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi, hc i hi]
  rw [hc']
  simp only [Matrix.mulVec_single, Pi.single_eq_same]
  simp [dotProduct, Pi.single_apply]
  ring

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The Lanczos vector `q_j` indexed by `ℕ` (`0` for `j ≥ q`). Atlas: `lanczos-recurrence`. -/
def vec (D : LanczosDecomp A b q) (j : ℕ) : n → ℝ :=
  if h : j < q then D.Q.col ⟨j, h⟩ else 0

/-- The Lanczos diagonal coefficient `α_j = t_jj = q_jᵀ A q_j` (`0` for `j ≥ q`).
Source: Golub–Meurant (2010) [`gm10`], Alg. 4.1. Atlas: `lanczos-recurrence`. -/
def alpha (D : LanczosDecomp A b q) (j : ℕ) : ℝ :=
  if h : j < q then D.T ⟨j, h⟩ ⟨j, h⟩ else 0

/-- The Lanczos off-diagonal coefficient `β_j = t_{j,j−1} = q_jᵀ A q_{j−1}` (`β_0 = 0`, and `0`
for `j ≥ q`). Indexing: `A q_j = β_j q_{j−1} + α_j q_j + β_{j+1} q_{j+1}` (0-based columns).
Source: Golub–Meurant (2010) [`gm10`], Alg. 4.1 (there `η_j`). Atlas: `lanczos-recurrence`. -/
def beta (D : LanczosDecomp A b q) (j : ℕ) : ℝ :=
  if h : 0 < j ∧ j < q then D.T ⟨j, h.2⟩ ⟨j - 1, by omega⟩ else 0

/-- `vec j` is column `j` for `j < q`. Atlas: `lanczos-recurrence`. -/
theorem vec_of_lt (D : LanczosDecomp A b q) {j : ℕ} (hj : j < q) : D.vec j = D.Q.col ⟨j, hj⟩ :=
  dif_pos hj

/-- Every Lanczos vector lies in `K_q(A, b)`. Atlas: `lanczos-recurrence`. -/
theorem vec_mem (D : LanczosDecomp A b q) (j : ℕ) : D.vec j ∈ krylovSpace A b q := by
  unfold vec
  split_ifs with h
  · exact krylovSpace_mono A b (show j + 1 ≤ q by omega) (D.graded.col_mem ⟨j, h⟩)
  · exact Submodule.zero_mem _

/-- `q_i ⬝ q_k = δ_ik` in the `ℕ`-indexed form. Atlas: `lanczos-recurrence`. -/
theorem col_dotProduct_vec (D : LanczosDecomp A b q) (i : Fin q) (k : ℕ) :
    D.Q.col i ⬝ᵥ D.vec k = if (i : ℕ) = k then 1 else 0 := by
  unfold vec
  split_ifs with h1 h2 h2
  · rw [D.hasOrthonormalCols.col_dotProduct_col, if_pos (Fin.ext h2)]
  · rw [D.hasOrthonormalCols.col_dotProduct_col, if_neg (fun h => h2 (by rw [h]))]
  · exact absurd (h2 ▸ i.isLt) h1
  · exact dotProduct_zero _

/-- **The Lanczos three-term recurrence** (column form): for symmetric `A` and `j + 1 < q`,
`A q_j = β_j q_{j−1} + α_j q_j + β_{j+1} q_{j+1}` (with `β_0 = 0`). Together with
`ArnoldiDecomp.mul_restrict_Q_eq_add_smul` this is `A Q_q = Q_q T_q + β_q q_{q+1} e_qᵀ`.
Source: Golub–Meurant (2010) [`gm10`], Thm 4.2; Trefethen–Bau (1997) [`tb97`], Lect. 36,
eq. (36.3).
atlas: lanczos-recurrence, arnoldi-relation (partial) -/
theorem mulVec_vec_eq (D : LanczosDecomp A b q) (hA : A.IsSymm) {j : ℕ} (hj : j + 1 < q) :
    A *ᵥ D.vec j =
      D.beta j • D.vec (j - 1) + D.alpha j • D.vec j + D.beta (j + 1) • D.vec (j + 1) := by
  have hmemA : A *ᵥ D.vec j ∈ krylovSpace A b q := by
    rw [D.vec_of_lt (by omega)]
    exact krylovSpace_mono A b (show j + 2 ≤ q by omega) (D.graded.mulVec_col_mem ⟨j, by omega⟩)
  have hmemR : D.beta j • D.vec (j - 1) + D.alpha j • D.vec j + D.beta (j + 1) • D.vec (j + 1)
      ∈ krylovSpace A b q :=
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (D.vec_mem _))
      (Submodule.smul_mem _ _ (D.vec_mem _))) (Submodule.smul_mem _ _ (D.vec_mem _))
  refine D.eq_of_forall_col_dotProduct_eq hmemA hmemR fun i => ?_
  rw [D.vec_of_lt (show j < q by omega), ← ArnoldiDecomp.H_apply]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ← D.vec_of_lt (show j < q by omega),
    col_dotProduct_vec, alpha, beta, dif_pos (show j < q by omega),
    dif_pos (show 0 < j + 1 ∧ j + 1 < q by omega)]
  have hS : (ArnoldiDecomp.H D).IsSymm := D.isSymm_T hA
  rcases Nat.lt_or_ge ((i : ℕ) + 1) j with h1 | h1
  · have h0 : ArnoldiDecomp.H D i ⟨j, by omega⟩ = 0 := by
      rw [← hS.apply]
      exact D.H_apply_eq_zero_of_add_one_lt (i := ⟨j, by omega⟩) (j := i) h1
    rw [h0]
    simp only [show (i : ℕ) ≠ j - 1 by omega, show (i : ℕ) ≠ j by omega,
      show (i : ℕ) ≠ j + 1 by omega, if_false, mul_zero, add_zero]
  rcases Nat.lt_or_ge (j + 1) i with h2 | h2
  · rw [D.H_apply_eq_zero_of_add_one_lt h2]
    simp only [show (i : ℕ) ≠ j - 1 by omega, show (i : ℕ) ≠ j by omega,
      show (i : ℕ) ≠ j + 1 by omega, if_false, mul_zero, add_zero]
  rcases (show (i : ℕ) + 1 = j ∨ (i : ℕ) = j ∨ (i : ℕ) = j + 1 by omega) with h | h | h
  · rw [show i = ⟨j - 1, by omega⟩ from Fin.ext (by simp; omega)]
    simp only [show j - 1 ≠ j by omega, show j - 1 ≠ j + 1 by omega, if_true, if_false,
      mul_zero, add_zero, mul_one, dif_pos (show 0 < j ∧ j < q by omega)]
    exact (hS.apply _ _).symm
  · rw [show i = ⟨j, by omega⟩ from Fin.ext h]
    simp only [show j ≠ j + 1 by omega, if_true, if_false, mul_zero, add_zero, mul_one]
    split_ifs with h0 h0' <;> try simp
    omega
  · rw [show i = ⟨j + 1, by omega⟩ from Fin.ext h]
    simp only [show j + 1 ≠ j - 1 by omega, show j + 1 ≠ j by omega, if_true, if_false,
      mul_zero, zero_add, mul_one]
    rfl

/-- **The Lanczos relation** `A Q_q = Q_q T_q + β_q q_{q+1} e_qᵀ` (for `q ≥ 1`), with
`β_q = t_{q,q−1}` and `q_{q+1}` the last column of a decomposition of size `q + 1`; together with
`T_apply_eq_zero_of_one_lt_dist` (`T_q` symmetric tridiagonal for symmetric `A`) and
`ArnoldiDecomp.hasOrthonormalCols`, `ArnoldiDecomp.range_Q` this is the Lanczos
tridiagonalisation. Source: Golub–Meurant (2010) [`gm10`], Thm 4.2; Chen–Trogdon–Ubaru (2021)
[`ctu21`], §2.
atlas: lanczos-recurrence -/
theorem mul_restrict_Q_eq_add_beta_smul (D : LanczosDecomp A b (q + 1)) (hq : 0 < q) :
    A * (D.restrict q.le_succ).Q =
      (D.restrict q.le_succ).Q * LanczosDecomp.T (D.restrict q.le_succ) +
        D.beta q • vecMulVec (D.vec q) (Pi.single (⟨q - 1, by omega⟩ : Fin q) 1) := by
  rw [ArnoldiDecomp.mul_restrict_Q_eq_add_smul D hq, D.vec_of_lt (Nat.lt_succ_self q), beta,
    dif_pos ⟨hq, Nat.lt_succ_self q⟩]
  rfl

/-- The Lanczos off-diagonal coefficients do not vanish below the grade: `β_j ≠ 0` for
`0 < j < q`. Source: Golub–Meurant (2010) [`gm10`], Thm 4.2 (no breakdown before the grade).
Atlas: `lanczos-recurrence`. -/
theorem beta_ne_zero (D : LanczosDecomp A b q) {j : ℕ} (h0 : 0 < j) (hj : j < q) :
    D.beta j ≠ 0 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [beta, dif_pos ⟨h0, hj⟩]
  simpa using D.H_succ_apply_ne_zero hj

/-- The canonical (Gram–Schmidt) decomposition has positive `β_j` for `0 < j < q`.
Source: Golub–Meurant (2010) [`gm10`], Alg. 4.1 (`η_j = ‖v_j‖ > 0`).
Atlas: `lanczos-recurrence`. -/
theorem beta_arnoldiDecomp_pos (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (h : q ≤ krylovGrade A b)
    {j : ℕ} (h0 : 0 < j) (hj : j < q) : 0 < LanczosDecomp.beta (arnoldiDecomp A b q h) j := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [beta, dif_pos ⟨h0, hj⟩]
  simpa using arnoldiDecomp_H_subdiag_pos A b h hj

/-- **Gauss–Lanczos quadrature through the Jacobi matrix**: for symmetric `A`, `q ≥ 1` and
`deg p < 2q`, `bᵀ p(A) b = ‖b‖² (p(T_q))₁₁`. Source: Golub–Meurant (2010) [`gm10`], Thm 6.6
and §7.1; Chen–Trogdon–Ubaru (2021) [`ctu21`], Thm 2.1. Deviation: the degree bound is
`p.degree < 2 * q` (no `natDegree`, no truncated subtraction).
atlas: lanczos-gauss-quadrature -/
theorem dotProduct_aeval_mulVec_eq (D : LanczosDecomp A b q) (hA : A.IsSymm) (hq : 0 < q)
    {p : Polynomial ℝ} (hp : p.degree < 2 * q) :
    b ⬝ᵥ (Polynomial.aeval A p *ᵥ b) =
      (b ⬝ᵥ b) * Polynomial.aeval D.T p ⟨0, hq⟩ ⟨0, hq⟩ := by
  have hp' : p.natDegree ≤ 2 * q - 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hp2 : p.degree < ((2 * q : ℕ) : WithBot ℕ) := by exact_mod_cast hp
      have := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hp2
      omega
  rw [dotProduct_aeval_mulVec_eq_of_krylovSpace_le hA D.hasOrthonormalCols b hq D.range_Q.ge hp',
    dotProduct_mulVec_eq_of_apply_eq_zero _ (⟨0, hq⟩ : Fin q) fun i hi =>
      D.transpose_Q_mulVec_apply_eq_zero (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)),
    D.sq_transpose_Q_mulVec_apply_zero hq]
  rfl

end LanczosDecomp

end NLAlib
