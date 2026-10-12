import NLAlib.Krylov.Processes.ArnoldiProcess
import NLAlib.Krylov.Spaces.Block
/-!
# Golub–Kahan bidiagonalization

For `A : m × n` and `b : ℝᵐ`, Golub–Kahan (Lanczos) bidiagonalization produces orthonormal
`U_{k+1} = [u₁ … u_{k+1}]`, `V_k = [v₁ … v_k]` and a lower bidiagonal `(k+1) × k` matrix `B_k`
with `A V_k = U_{k+1} B_k`. Following `docs/KRYLOV_DEFINITIONS.md` §3.11–3.12 and
`docs/ALGORITHM_CONVENTIONS.md`, the object is a predicate and the recursion is a witness:

* `GolubKahanDecomp A b k`: `U` is a graded Krylov basis of `(AAᵀ, b)` with `k + 1` columns and
  `V` one of `(AᵀA, Aᵀb)` with `k` columns; `B := Uᵀ A V`.
* Proved structure theorems: the Golub–Kahan relation `A V = U B` (`mul_V_eq_U_mul_B`), `B` is
  lower bidiagonal (`B_apply_eq_zero_of_lt`, `B_apply_eq_zero_of_add_one_lt`), `BᵀB` is the
  Lanczos tridiagonal matrix of `AᵀA` (`transpose_B_mul_B_eq_T`), and the columns `j < k` of
  `(I − VVᵀ) Aᵀ U` vanish (the second relation `AᵀU_{k+1} = V_k B_kᵀ + r e_{k+1}ᵀ`,
  `transpose_mulVec_U_col_mem_range_V`). Existence below the grades:
  `golubKahanDecomp` (from `arnoldiDecomp`).
* The recursion (Golub–Van Loan Alg. 10.4.1, Paige–Saunders form):
  `β₁u₁ = b`, `α₁v₁ = Aᵀu₁`, `β_{j+1}u_{j+1} = Av_j − α_ju_j`,
  `α_{j+1}v_{j+1} = Aᵀu_{j+1} − β_{j+1}v_j`,
  as `golubKahanRecurrence A b : ℕ → GolubKahanState` (zero-indexed: state `j` holds
  `u_{j+1}, v_{j+1}, α_{j+1}, β_{j+1}`), total via `x/0 = 0`; success predicate
  `GolubKahanSucceeds A b k` (all `α_j, β_j ≠ 0` up to `k`); realisation and breakdown are
  scaffolds (`isGradedKrylovBasis_golubKahanU_V`, `golubKahanSucceeds_iff`, the entries of `B`).

Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1 (Alg. 10.4.1); Trefethen–Bau (1997) [`tb97`],
Lect. 31; Paige–Saunders (1982), LSQR §3.
Atlas: `golub-kahan-bidiagonalization`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-! ### Krylov spaces of `AAᵀ` and `AᵀA` -/

/-- `A K_q(AᵀA, Aᵀb) ⊆ K_{q+1}(AAᵀ, b)`. Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1.
Helper for `golub-kahan-bidiagonalization`. -/
theorem mulVec_mem_krylovSpace_mul_transpose (A : Matrix m n ℝ) (b : m → ℝ) {q : ℕ}
    {x : n → ℝ} (hx : x ∈ krylovSpace (Aᵀ * A) (Aᵀ *ᵥ b) q) :
    A *ᵥ x ∈ krylovSpace (A * Aᵀ) b (q + 1) := by
  have h := mulVec_mem_krylovSpace_of_mul_eq (C := A) (B' := A * Aᵀ)
    (by simp only [Matrix.mul_assoc]) hx
  rw [Matrix.mulVec_mulVec] at h
  exact krylovSpace_mulVec_le_succ _ _ _ h

/-- `Aᵀ K_q(AAᵀ, b) ⊆ K_q(AᵀA, Aᵀb)`. Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1.
Helper for `golub-kahan-bidiagonalization`. -/
theorem transpose_mulVec_mem_krylovSpace (A : Matrix m n ℝ) (b : m → ℝ) {q : ℕ} {x : m → ℝ}
    (hx : x ∈ krylovSpace (A * Aᵀ) b q) : Aᵀ *ᵥ x ∈ krylovSpace (Aᵀ * A) (Aᵀ *ᵥ b) q :=
  mulVec_mem_krylovSpace_of_mul_eq (by simp only [Matrix.mul_assoc]) hx

/-! ### The decomposition -/

/-- A **Golub–Kahan decomposition** of `(A, b)` of size `k`: `U : m × (k+1)` is a graded
orthonormal Krylov basis of `(AAᵀ, b)` and `V : n × k` one of `(AᵀA, Aᵀb)`. Then
`A V = U B` with `B = UᵀAV` lower bidiagonal; `V` is the Lanczos basis of `(AᵀA, Aᵀb)` and `U`
that of `(AAᵀ, b)`. Unique up to column signs (`ArnoldiDecomp.exists_sign` on each factor);
exists when `k + 1 ≤ krylovGrade (AAᵀ) b` and `k ≤ krylovGrade (AᵀA) (Aᵀb)`
(`golubKahanDecomp`). Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1; Trefethen–Bau (1997)
[`tb97`], Lect. 31.
atlas: golub-kahan-bidiagonalization -/
structure GolubKahanDecomp (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ) where
  /-- The left basis `U_{k+1}`. -/
  U : Matrix m (Fin (k + 1)) ℝ
  /-- The right basis `V_k`. -/
  V : Matrix n (Fin k) ℝ
  /-- `U` is a graded orthonormal basis of `K_{k+1}(AAᵀ, b)`. -/
  gradedU : IsGradedKrylovBasis (A * Aᵀ) b U
  /-- `V` is a graded orthonormal basis of `K_k(AᵀA, Aᵀb)`. -/
  gradedV : IsGradedKrylovBasis (Aᵀ * A) (Aᵀ *ᵥ b) V

namespace GolubKahanDecomp

variable {A : Matrix m n ℝ} {b : m → ℝ} {k : ℕ}

/-- The bidiagonal matrix `B_k = U_{k+1}ᵀ A V_k : (k+1) × k`. Source: Golub–Van Loan (2013)
[`gvl13`], §10.4.1.
atlas: golub-kahan-bidiagonalization -/
def B (D : GolubKahanDecomp A b k) : Matrix (Fin (k + 1)) (Fin k) ℝ := D.Uᵀ * A * D.V

/-- `V` as a Lanczos decomposition of `(AᵀA, Aᵀb)`. Source: Golub–Van Loan (2013) [`gvl13`],
§10.4.1. Helper for `golub-kahan-bidiagonalization`. -/
def lanczosV (D : GolubKahanDecomp A b k) : LanczosDecomp (Aᵀ * A) (Aᵀ *ᵥ b) k :=
  ⟨D.V, D.gradedV⟩

/-- `range (A V_k) ⊆ range U_{k+1} = K_{k+1}(AAᵀ, b)`. Helper for
`golub-kahan-bidiagonalization`. -/
theorem range_mul_V_le (D : GolubKahanDecomp A b k) :
    LinearMap.range (A * D.V).mulVecLin ≤ LinearMap.range D.U.mulVecLin := by
  rw [D.gradedU.range_mulVecLin, Matrix.range_mulVecLin, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [col_mul_eq_mulVec_col]
  refine mulVec_mem_krylovSpace_mul_transpose A b ?_
  rw [← D.gradedV.range_mulVecLin]
  exact ⟨Pi.single j 1, by simp [Matrix.mulVec_single]⟩

/-- **The Golub–Kahan relation** `A V_k = U_{k+1} B_k`. Source: Golub–Van Loan (2013)
[`gvl13`], §10.4.1 (eq. 10.4.4); Trefethen–Bau (1997) [`tb97`], Lect. 31.
atlas: golub-kahan-bidiagonalization -/
theorem mul_V_eq_U_mul_B (D : GolubKahanDecomp A b k) : A * D.V = D.U * D.B := by
  rw [B, Matrix.mul_assoc, mul_transpose_mul_eq_of_range_le D.gradedU.orth D.range_mul_V_le]

/-- `B` is **lower bidiagonal**, upper part: `B_{ij} = 0` for `i < j` (`vⱼ ⟂ K_j(AᵀA, Aᵀb)`,
which contains `Aᵀuᵢ`). Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1.
atlas: golub-kahan-bidiagonalization -/
theorem B_apply_eq_zero_of_lt (D : GolubKahanDecomp A b k) {i : Fin (k + 1)} {j : Fin k}
    (h : (i : ℕ) < j) : D.B i j = 0 := by
  rw [B, transpose_mul_mul_apply_eq_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm]
  refine D.gradedV.col_dotProduct_eq_zero j ?_
  have hu := transpose_mulVec_mem_krylovSpace A b (D.gradedU.col_mem i)
  exact krylovSpace_mono _ _ (show (i : ℕ) + 1 ≤ j by omega) hu

/-- `B` is **lower bidiagonal**, lower part: `B_{ij} = 0` for `j + 1 < i` (`uᵢ ⟂ K_i(AAᵀ, b)`,
which contains `Avⱼ ∈ K_{j+2}`). Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1.
atlas: golub-kahan-bidiagonalization -/
theorem B_apply_eq_zero_of_add_one_lt (D : GolubKahanDecomp A b k) {i : Fin (k + 1)}
    {j : Fin k} (h : (j : ℕ) + 1 < i) : D.B i j = 0 := by
  rw [B, transpose_mul_mul_apply_eq_dotProduct]
  refine D.gradedU.col_dotProduct_eq_zero i ?_
  have hv := mulVec_mem_krylovSpace_mul_transpose A b (D.gradedV.col_mem j)
  exact krylovSpace_mono _ _ (show (j : ℕ) + 1 + 1 ≤ i by omega) hv

/-- **`BᵀB` is the Lanczos matrix of `AᵀA`**: `B_kᵀ B_k = V_kᵀ (AᵀA) V_k = T_k`, the Jacobi
matrix of the Lanczos process on `(AᵀA, Aᵀb)`. Source: Golub–Van Loan (2013) [`gvl13`],
§10.4.1; Trefethen–Bau (1997) [`tb97`], Lect. 31.
atlas: golub-kahan-bidiagonalization -/
theorem transpose_B_mul_B_eq_T (D : GolubKahanDecomp A b k) : D.Bᵀ * D.B = D.lanczosV.T := by
  have hU : D.Uᵀ * D.U = 1 := D.gradedU.orth
  change D.Bᵀ * D.B = D.Vᵀ * (Aᵀ * A) * D.V
  have h := D.mul_V_eq_U_mul_B
  calc D.Bᵀ * D.B = (D.U * D.B)ᵀ * (D.U * D.B) := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D.Uᵀ, hU, Matrix.one_mul]
    _ = D.Vᵀ * (Aᵀ * A) * D.V := by
        rw [← h, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

/-- **The second Golub–Kahan relation**, column form: for `j < k`, `Aᵀuⱼ ∈ range V_k`, i.e. the
columns `j < k` of `(I − VVᵀ) AᵀU_{k+1}` vanish and `AᵀU_{k+1} = V_k B_kᵀ + r e_{k+1}ᵀ` with
`r = (I − VVᵀ) Aᵀ u_{k+1}` (`= α_{k+1} v_{k+1}`). Source: Golub–Van Loan (2013) [`gvl13`],
§10.4.1 (eq. 10.4.5).
atlas: golub-kahan-bidiagonalization -/
theorem transpose_mulVec_U_col_mem_range_V (D : GolubKahanDecomp A b k) {j : Fin (k + 1)}
    (hj : (j : ℕ) < k) : Aᵀ *ᵥ D.U.col j ∈ LinearMap.range D.V.mulVecLin := by
  rw [D.gradedV.range_mulVecLin]
  exact krylovSpace_mono _ _ (show (j : ℕ) + 1 ≤ k by omega)
    (transpose_mulVec_mem_krylovSpace A b (D.gradedU.col_mem j))

end GolubKahanDecomp

/-- A Golub–Kahan decomposition exists below the two grades: from `arnoldiDecomp` of
`(AAᵀ, b)` (size `k + 1`) and of `(AᵀA, Aᵀb)` (size `k`), the canonical witnesses with positive
subdiagonals. Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1.
atlas: golub-kahan-bidiagonalization -/
def golubKahanDecomp (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ)
    (hU : k + 1 ≤ krylovGrade (A * Aᵀ) b) (hV : k ≤ krylovGrade (Aᵀ * A) (Aᵀ *ᵥ b)) :
    GolubKahanDecomp A b k where
  U := (arnoldiDecomp (A * Aᵀ) b (k + 1) hU).Q
  V := (arnoldiDecomp (Aᵀ * A) (Aᵀ *ᵥ b) k hV).Q
  gradedU := (arnoldiDecomp (A * Aᵀ) b (k + 1) hU).graded
  gradedV := (arnoldiDecomp (Aᵀ * A) (Aᵀ *ᵥ b) k hV).graded

/-! ### The recursion -/

/-- The state of the Golub–Kahan recursion: the current `u`, `v`, `α`, `β`. Source:
Golub–Van Loan (2013) [`gvl13`], Alg. 10.4.1. Helper for `golub-kahan-bidiagonalization`. -/
structure GolubKahanState (m n : Type*) where
  /-- The left vector `u_j`. -/
  u : m → ℝ
  /-- The right vector `v_j`. -/
  v : n → ℝ
  /-- The diagonal entry `α_j` of `B`. -/
  alpha : ℝ
  /-- The subdiagonal entry `β_j` of `B` (`β₁ = ‖b‖`). -/
  beta : ℝ

omit [DecidableEq m] [DecidableEq n] in
/-- The first state: `β₁ = ‖b‖`, `u₁ = b/β₁`, `α₁ = ‖Aᵀu₁‖`, `v₁ = Aᵀu₁/α₁` (junk `0` on
breakdown). Source: Golub–Van Loan (2013) [`gvl13`], Alg. 10.4.1. Helper for
`golub-kahan-bidiagonalization`. -/
def golubKahanInit (A : Matrix m n ℝ) (b : m → ℝ) : GolubKahanState m n :=
  let β := √(b ⬝ᵥ b)
  let u := β⁻¹ • b
  let w := Aᵀ *ᵥ u
  let α := √(w ⬝ᵥ w)
  ⟨u, α⁻¹ • w, α, β⟩

omit [DecidableEq m] [DecidableEq n] in
/-- One Golub–Kahan step: `β' u' = A v − α u`, `α' v' = Aᵀ u' − β' v`, with `α', β' ≥ 0` the
norms (junk `0` on breakdown). Source: Golub–Van Loan (2013) [`gvl13`], Alg. 10.4.1. Helper for
`golub-kahan-bidiagonalization`. -/
def golubKahanStep (A : Matrix m n ℝ) (s : GolubKahanState m n) : GolubKahanState m n :=
  let p := A *ᵥ s.v - s.alpha • s.u
  let β := √(p ⬝ᵥ p)
  let u := β⁻¹ • p
  let r := Aᵀ *ᵥ u - β • s.v
  let α := √(r ⬝ᵥ r)
  ⟨u, α⁻¹ • r, α, β⟩

omit [DecidableEq m] [DecidableEq n] in
/-- **The Golub–Kahan recursion**, zero-indexed: state `j` holds `u_{j+1}, v_{j+1}, α_{j+1},
β_{j+1}` in Golub–Van Loan's one-based notation. Total (`x/0 = 0`). Source: Golub–Van Loan
(2013) [`gvl13`], Alg. 10.4.1; Paige–Saunders (1982), §3.
atlas: golub-kahan-recurrence -/
def golubKahanRecurrence (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) : GolubKahanState m n :=
  (golubKahanStep A)^[j] (golubKahanInit A b)

omit [DecidableEq m] [DecidableEq n] in
/-- **Success predicate**: no breakdown in the first `k + 1` states, `α_j ≠ 0` and `β_j ≠ 0`.
Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1.
atlas: golub-kahan-recurrence -/
def GolubKahanSucceeds (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ) : Prop :=
  ∀ j ≤ k, (golubKahanRecurrence A b j).alpha ≠ 0 ∧ (golubKahanRecurrence A b j).beta ≠ 0

omit [DecidableEq m] [DecidableEq n] in
/-- The first `q` left vectors as a matrix `[u₁ … u_q]`. Helper for
`golub-kahan-bidiagonalization`. -/
def golubKahanU (A : Matrix m n ℝ) (b : m → ℝ) (q : ℕ) : Matrix m (Fin q) ℝ :=
  Matrix.of fun i j => (golubKahanRecurrence A b j).u i

omit [DecidableEq m] [DecidableEq n] in
/-- The first `q` right vectors as a matrix `[v₁ … v_q]`. Helper for
`golub-kahan-bidiagonalization`. -/
def golubKahanV (A : Matrix m n ℝ) (b : m → ℝ) (q : ℕ) : Matrix n (Fin q) ℝ :=
  Matrix.of fun i j => (golubKahanRecurrence A b j).v i

/-- SCAFFOLD: golub-kahan-bidiagonalization
**Realisation.** If the recursion does not break down through state `k`, then `[u₁ … u_{k+1}]`
is a graded orthonormal Krylov basis of `(AAᵀ, b)` and `[v₁ … v_{k+1}]` one of `(AᵀA, Aᵀb)`.
Source: Golub–Van Loan (2013) [`gvl13`], §10.4.1; Paige–Saunders (1982), §3. Proof sketch:
induction on `k` with the invariant "the two matrices are graded orthonormal bases"; membership
`u_{j+1} ∈ K_{j+2}(AAᵀ, b)` and `v_{j+1} ∈ K_{j+2}(AᵀA, Aᵀb)` from
`mulVec_mem_krylovSpace_mul_transpose`/`transpose_mulVec_mem_krylovSpace`; orthogonality of the
new `u` to `u_1..u_{j}` is the usual Lanczos short-recurrence argument
(`GolubKahanDecomp.B_apply_eq_zero_of_lt`/`…_of_add_one_lt` applied to the previous bases),
and `IsGradedKrylovBasis.of_mem`. Equivalently, it is Lanczos on
`[[0, A], [Aᵀ, 0]]` started at `(b, 0)` (D-E's `lanczosRecurrence`). Difficulty 3.
atlas: golub-kahan-recurrence -/
theorem isGradedKrylovBasis_golubKahanU_V {A : Matrix m n ℝ} {b : m → ℝ} {k : ℕ}
    (h : GolubKahanSucceeds A b k) :
    IsGradedKrylovBasis (A * Aᵀ) b (golubKahanU A b (k + 1)) ∧
      IsGradedKrylovBasis (Aᵀ * A) (Aᵀ *ᵥ b) (golubKahanV A b (k + 1)) := by
  sorry

/-- SCAFFOLD: golub-kahan-bidiagonalization
**Breakdown.** The recursion runs without breakdown through state `k` iff both Krylov grades
are at least `k + 1`: `GolubKahanSucceeds A b k ↔ k + 1 ≤ grade(AAᵀ, b) ∧
k + 1 ≤ grade(AᵀA, Aᵀb)`. (In particular `b = 0` or `Aᵀb = 0` fails at once.) Source:
Golub–Van Loan (2013) [`gvl13`], §10.4.1; Paige–Saunders (1982), §3. Proof sketch: the
interleaved sequence `u₁, v₁, u₂, v₂, …` is the Lanczos basis of `[[0, A], [Aᵀ, 0]]` from
`(b, 0)`, whose Krylov space of dimension `2j` (resp. `2j + 1`) is
`K_j(AAᵀ, b) ⊕ K_j(AᵀA, Aᵀb)` (resp. `K_{j+1}(AAᵀ, b) ⊕ K_j(AᵀA, Aᵀb)`); Lanczos breaks down
exactly at the grade (`krylovGrade`, `finrank_krylovSpace`), and the norms `α, β` are the
Lanczos `β`'s. Difficulty 3.
atlas: golub-kahan-recurrence -/
theorem golubKahanSucceeds_iff (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ) :
    GolubKahanSucceeds A b k ↔
      k + 1 ≤ krylovGrade (A * Aᵀ) b ∧ k + 1 ≤ krylovGrade (Aᵀ * A) (Aᵀ *ᵥ b) := by
  sorry

/-- SCAFFOLD: golub-kahan-bidiagonalization
**The entries of `B` are the recursion's `α, β`.** Without breakdown through state `k`:
`u_{j+1}ᵀ A v_{j+1} = α_{j+1}` for `j ≤ k` and `u_{j+2}ᵀ A v_{j+1} = β_{j+2}` for `j < k`, so the
`B` of the realised decomposition has diagonal `α` and subdiagonal `β` (all positive). Source:
Golub–Van Loan (2013) [`gvl13`], Alg. 10.4.1 and eq. (10.4.4). Proof sketch: from the
recursion, `Aᵀu_{j+1} = α_{j+1}v_{j+1} + β_{j+1}v_j` and
`Av_{j+1} = α_{j+1}u_{j+1} + β_{j+2}u_{j+2}`, then orthonormality
(`isGradedKrylovBasis_golubKahanU_V`). Difficulty 2 given the realisation.
atlas: golub-kahan-recurrence -/
theorem dotProduct_golubKahan_eq {A : Matrix m n ℝ} {b : m → ℝ} {k : ℕ}
    (h : GolubKahanSucceeds A b k) :
    (∀ j ≤ k, (golubKahanRecurrence A b j).u ⬝ᵥ (A *ᵥ (golubKahanRecurrence A b j).v) =
      (golubKahanRecurrence A b j).alpha) ∧
    (∀ j < k, (golubKahanRecurrence A b (j + 1)).u ⬝ᵥ (A *ᵥ (golubKahanRecurrence A b j).v) =
      (golubKahanRecurrence A b (j + 1)).beta) := by
  sorry

end NLAlib
