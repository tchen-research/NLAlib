import NLAlib.Matrix.Factorizations.Householder
import NLAlib.Matrix.Factorizations.Givens
/-!
# Reduction to upper Hessenberg form

* `IsHessenbergForm A Q H`: `Q` orthogonal, `A = Q H Qᵀ` and `H` upper Hessenberg
  (`IsUpperHessenberg`, from `NLAlib.Matrix.Factorizations.Givens`). Equivalently
  `QᵀAQ = H` (`IsHessenbergForm.transpose_mul_mul_eq`).
* The Householder recursion (`hessenbergReflectors`): on `A : (k+3) × (k+3)` reflect the
  subdiagonal part `A(1:, 0)` of the first column onto `e₁` with `P = diag(1, H_w)`, form `PAP`,
  and recurse on its trailing `(k+2) × (k+2)` block. It produces `n − 2` reflectors
  (`length_hessenbergReflectors`), all fixing `e₀`. `hessenbergQ A` is their product and
  `hessenbergH A := QᵀAQ`; the realisation theorem is `isHessenbergForm_hessenbergReduction`
  (no hypothesis), whence `exists_isHessenbergForm`.
* Symmetric `A`: `H` is symmetric tridiagonal (`IsHessenbergForm.isTridiagonal`).
* `IsUnreducedHessenberg H` (no zero subdiagonal entry) and the **implicit Q theorem**
  (`IsHessenbergForm.exists_sign`): two Hessenberg forms of `A` with the same first column of `Q`
  and unreduced `H` differ by a diagonal sign matrix.

The recursion never breaks down; there is no success predicate. Defining `H` as `QᵀAQ` rather than
by accumulating `PAP` in place is a deviation from Trefethen–Bau Alg. 26.1 in presentation only
(the two are equal by construction of `Q`).

The link with the Krylov layer (the columns of `Q` are the Arnoldi basis of `(A, q₁)`, and the
implicit Q theorem is `ArnoldiDecomp.exists_sign`) cannot be stated here (layer 0 does not import
`Krylov`); it belongs in `NLAlib.Krylov.Solvers`.

Sources: Trefethen–Bau 1997 [`tb97`], Lect. 26 (Alg. 26.1); Golub–Van Loan 2013 [`gvl13`],
§7.4.3 (Alg. 7.4.2), Thm 7.4.2 (implicit Q), §8.3.1 (tridiagonalisation).
Atlas: `hessenberg-reduction`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### The predicate -/

/-- `A = Q H Qᵀ` is a **Hessenberg form** of `A`: `Q` orthogonal and `H` upper Hessenberg.
Trefethen–Bau 1997, Lect. 26 (`A = Q H Q*`); Golub–Van Loan 2013, §7.4.3 (`QᵀAQ = H`).
atlas: hessenberg-reduction -/
structure IsHessenbergForm (A Q H : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- `Q` is orthogonal, `QᵀQ = I`. -/
  orth : HasOrthonormalCols Q
  /-- The similarity `A = Q H Qᵀ`. -/
  eq : A = Q * H * Qᵀ
  /-- `H` is upper Hessenberg. -/
  hess : IsUpperHessenberg H

/-- `H` has **no zero subdiagonal entry** (`H (j+1) j ≠ 0`) and is upper Hessenberg.
Golub–Van Loan 2013, §7.4.3 ("unreduced"); Trefethen–Bau 1997, Lect. 26.
atlas: hessenberg-reduction -/
def IsUnreducedHessenberg (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperHessenberg H ∧ ∀ i j : Fin n, (i : ℕ) = j + 1 → H i j ≠ 0

namespace IsHessenbergForm

variable {A Q H : Matrix (Fin n) (Fin n) ℝ}

/-- `Q Qᵀ = I`. Golub–Van Loan 2013, §2.1. -/
theorem mul_transpose_self (h : IsHessenbergForm A Q H) : Q * Qᵀ = 1 :=
  mul_eq_one_comm.mp h.orth

/-- `QᵀAQ = H`. Golub–Van Loan 2013, §7.4.3.
atlas: hessenberg-reduction -/
theorem transpose_mul_mul_eq (h : IsHessenbergForm A Q H) : Qᵀ * A * Q = H := by
  rw [h.eq, Matrix.mul_assoc, Matrix.mul_assoc, show Qᵀ * Q = 1 from h.orth, Matrix.mul_one,
    ← Matrix.mul_assoc, show Qᵀ * Q = 1 from h.orth, Matrix.one_mul]

/-- For symmetric `A` the Hessenberg form is symmetric. Golub–Van Loan 2013, §8.3.1. -/
theorem isSymm (h : IsHessenbergForm A Q H) (hA : A.IsSymm) : H.IsSymm := by
  rw [← h.transpose_mul_mul_eq]; exact isSymm_transpose_mul_mul hA Q

/-- **Symmetric ⇒ tridiagonal**: a Hessenberg form of a symmetric matrix is (symmetric)
tridiagonal. Trefethen–Bau 1997, Lect. 26 (the Hermitian case); Golub–Van Loan 2013, §8.3.1.
atlas: hessenberg-reduction -/
theorem isTridiagonal (h : IsHessenbergForm A Q H) (hA : A.IsSymm) : IsTridiagonal H :=
  h.hess.isTridiagonal_of_isSymm (h.isSymm hA)

end IsHessenbergForm

/-! ### The Householder recursion -/

/-- The **Householder reflector vectors of Hessenberg reduction**, padded to length `n`. On
`A : (k+3) × (k+3)`: `w = householderVector (A(1:, 0)) 0`, `u = (0, w)`, `P = H_u = diag(1, H_w)`;
recurse on the trailing block of `PAP` and pad its vectors with a leading zero. Matrices of
size `≤ 2` are already Hessenberg (no reflector). Trefethen–Bau 1997, Alg. 26.1;
Golub–Van Loan 2013, Alg. 7.4.2.
atlas: hessenberg-reduction -/
def hessenbergReflectors : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → List (Fin n → ℝ)
  | 0, _ => []
  | 1, _ => []
  | 2, _ => []
  | k + 3, A =>
    let u : Fin (k + 3) → ℝ := vecCons 0 (householderVector (fun i : Fin (k + 2) => A i.succ 0) 0)
    let B := householder u * A * householder u
    u :: (hessenbergReflectors (B.submatrix Fin.succ Fin.succ)).map (vecCons 0)

/-- The orthogonal factor of Hessenberg reduction: the product `P₁ P₂ ⋯ P_{n−2}` of the
reflectors. Trefethen–Bau 1997, Lect. 26.
atlas: hessenberg-reduction -/
def hessenbergQ (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((hessenbergReflectors A).map householder).prod

/-- The Hessenberg matrix `H = QᵀAQ` of the reduction. Trefethen–Bau 1997, Alg. 26.1.
atlas: hessenberg-reduction -/
def hessenbergH (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (hessenbergQ A)ᵀ * A * hessenbergQ A

/-- **Hessenberg reduction** `A ↦ (Q, H)` by Householder reflectors. Trefethen–Bau 1997,
Alg. 26.1; Golub–Van Loan 2013, Alg. 7.4.2.
atlas: hessenberg-reduction -/
def hessenbergReduction (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  (hessenbergQ A, hessenbergH A)

/-- Hessenberg reduction uses `n − 2` reflectors. Trefethen–Bau 1997, Alg. 26.1. -/
theorem length_hessenbergReflectors : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    (hessenbergReflectors A).length = n - 2
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | k + 3, A => by
    simp only [hessenbergReflectors, List.length_cons, List.length_map,
      length_hessenbergReflectors]
    omega

/-- Every reflector vector of the reduction has first entry `0` (so every reflector fixes
`e₀`). Trefethen–Bau 1997, Lect. 26. -/
theorem apply_zero_of_mem_hessenbergReflectors :
    ∀ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u : Fin (n + 1) → ℝ),
      u ∈ hessenbergReflectors A → u 0 = 0
  | 0, _, _, hu => by simp [hessenbergReflectors] at hu
  | 1, _, _, hu => by simp [hessenbergReflectors] at hu
  | k + 2, A, u, hu => by
    simp only [hessenbergReflectors, List.mem_cons, List.mem_map] at hu
    rcases hu with rfl | ⟨w, -, rfl⟩ <;> rfl

/-- **`Q e₀ = e₀`**: the first column of the Householder `Q` is `e₀` (so `q₁ = e₁` in
Trefethen–Bau's numbering, which fixes `Q` up to signs by the implicit Q theorem).
Golub–Van Loan 2013, §7.4.3.
atlas: hessenberg-reduction -/
theorem hessenbergQ_mulVec_single_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    hessenbergQ A *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  unfold hessenbergQ
  have key : ∀ l : List (Fin (n + 1) → ℝ), (∀ u ∈ l, u 0 = 0) →
      (l.map householder).prod *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro l hl
    induction l with
    | nil => rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]
    | cons u l ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
        ih fun v hv => hl v (List.mem_cons_of_mem _ hv)]
      apply householder_mulVec_of_dotProduct_eq_zero
      rw [dotProduct_single, hl u List.mem_cons_self, zero_mul]
  exact key _ (apply_zero_of_mem_hessenbergReflectors A)

/-- The Hessenberg `Q` is orthogonal (no hypothesis). Trefethen–Bau 1997, Lect. 26. -/
theorem hessenbergQ_transpose_mul_self (A : Matrix (Fin n) (Fin n) ℝ) :
    (hessenbergQ A)ᵀ * hessenbergQ A = 1 :=
  transpose_list_prod_mul_self _ fun M hM => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hM
    exact householder_transpose_mul_self v

/-- SCAFFOLD: hessenberg-reduction
**The reduction produces a Hessenberg matrix**: `QᵀAQ` is upper Hessenberg for the Householder
`Q`, for every `A`. Trefethen–Bau 1997, Lect. 26 (Alg. 26.1); Golub–Van Loan 2013, §7.4.3.
Proof sketch: induction on `n` (`k + 3`): with `P = diag(1, H_w)` and
`H_w (A(1:, 0)) = ρ e₀` (`householder_mulVec_householderVector`), the first column of `PAP` is
`(a₀₀, ρ, 0, …, 0)` (right multiplication by `P` does not touch column `0`); the recursive `Q'`
is `diag(1, Q'')`-shaped (`householder_vecCons_zero`), so `QᵀAQ` has first column
`(a₀₀, ρ, 0, …)` and trailing block `Q''ᵀ B' Q''`, Hessenberg by induction. Difficulty 3
(the bookkeeping of padded reflectors).
atlas: hessenberg-reduction -/
theorem isUpperHessenberg_hessenbergH (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUpperHessenberg (hessenbergH A) := by
  sorry

/-- **Realisation of Hessenberg reduction**: `(hessenbergQ A, hessenbergH A)` is a Hessenberg
form of every square `A`, with `Q` a product of `n − 2` Householder reflectors.
Trefethen–Bau 1997, Lect. 26, Alg. 26.1; Golub–Van Loan 2013, Alg. 7.4.2.
atlas: hessenberg-reduction -/
theorem isHessenbergForm_hessenbergReduction (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHessenbergForm A (hessenbergReduction A).1 (hessenbergReduction A).2 where
  orth := hessenbergQ_transpose_mul_self A
  eq := by
    have hQQ : hessenbergQ A * (hessenbergQ A)ᵀ = 1 :=
      mul_eq_one_comm.mp (hessenbergQ_transpose_mul_self A)
    simp only [hessenbergReduction, hessenbergH]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc, hQQ,
      Matrix.mul_one]
  hess := isUpperHessenberg_hessenbergH A

/-- **Every square matrix is orthogonally similar to an upper Hessenberg matrix**; if `A` is
symmetric, to a symmetric tridiagonal one (`IsHessenbergForm.isTridiagonal`).
Trefethen–Bau 1997, Lect. 26; Golub–Van Loan 2013, §7.4.3.
atlas: hessenberg-reduction -/
theorem exists_isHessenbergForm (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q H, IsHessenbergForm A Q H :=
  ⟨_, _, isHessenbergForm_hessenbergReduction A⟩

/-! ### The implicit Q theorem -/

/-- SCAFFOLD: hessenberg-reduction
**Implicit Q theorem**: if `A = Q₁H₁Q₁ᵀ = Q₂H₂Q₂ᵀ` are two Hessenberg forms with the same first
column of `Q` and `H₁` unreduced, then `Q₂ = Q₁ D` and `H₂ = D H₁ D` for a diagonal sign matrix
`D` (`d_i = ±1`, `d₀ = 1`). Golub–Van Loan 2013, Thm 7.4.2 (the unreduced case `k = n`; the
reduced case, where the conclusion holds up to the first zero subdiagonal entry, is not stated);
Trefethen–Bau 1997, Lect. 26 / 33 (uniqueness of the Arnoldi basis). Proof sketch: with
`W = Q₁ᵀQ₂`, `G = H₂`: `H₁ W = W G` and `W e₀ = e₀`; comparing columns,
`h_{k+1,k} w_{k+1} = H₁ w_k − ∑_{i ≤ k} g_{ik} w_i` shows by induction that `W` is upper
triangular; an orthogonal upper triangular matrix is diagonal with entries `±1`. This is the
Hessenberg-form shadow of `ArnoldiDecomp.exists_sign` (Krylov layer). Difficulty 3.
atlas: hessenberg-reduction -/
theorem IsHessenbergForm.exists_sign {A Q₁ H₁ Q₂ H₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h₁ : IsHessenbergForm A Q₁ H₁) (h₂ : IsHessenbergForm A Q₂ H₂)
    (hcol : Q₁.col 0 = Q₂.col 0) (hH : IsUnreducedHessenberg H₁) :
    ∃ d : Fin (n + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧
      Q₂ = Q₁ * diagonal d ∧ H₂ = diagonal d * H₁ * diagonal d := by
  sorry

end NLAlib
