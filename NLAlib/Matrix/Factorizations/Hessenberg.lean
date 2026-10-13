import NLAlib.Matrix.Factorizations.Householder
import NLAlib.Matrix.Structured.Hessenberg
import NLAlib.Matrix.Structured.BorderedSimilarity
import NLAlib.Matrix.Structured.HessenbergIntertwining
/-!
# Reduction to upper Hessenberg form

* `IsHessenbergForm A Q H`: `Q` orthogonal, `A = Q H Qᵀ` and `H` upper Hessenberg
  (`IsUpperHessenberg`, from `NLAlib.Matrix.Structured.Hessenberg`). Equivalently
  `QᵀAQ = H` (`IsHessenbergForm.transpose_mul_mul_eq`).
* The Householder recursion (`hessenbergReflectors`): on `A : (k+3) × (k+3)` reflect the
  subdiagonal part `A(1:, 0)` of the first column onto `e₁` with `P = diag(1, H_w)`, form `PAP`,
  and recurse on its trailing `(k+2) × (k+2)` block. It produces `n − 2` reflectors
  (`length_hessenbergReflectors`), all fixing `e₀`. `hessenbergQ A` is their product and
  `hessenbergH A := QᵀAQ`; the realisation theorem is `isHessenbergForm_hessenbergReduction`
  (no hypothesis), whence `exists_isHessenbergForm`.
* Symmetric `A`: `H` is symmetric tridiagonal (`IsHessenbergForm.isTridiagonal`).
* `IsUnreducedHessenberg H` (no zero subdiagonal entry, `NLAlib.Matrix.Structured.Hessenberg`)
  and the **implicit Q theorem**
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
theorem isHermitian (h : IsHessenbergForm A Q H) (hA : A.IsHermitian) : H.IsHermitian := by
  rw [← h.transpose_mul_mul_eq, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.isHermitian_conjTranspose_mul_mul Q hA

/-- **Symmetric ⇒ tridiagonal**: a Hessenberg form of a symmetric matrix is (symmetric)
tridiagonal. Trefethen–Bau 1997, Lect. 26 (the Hermitian case); Golub–Van Loan 2013, §8.3.1.
atlas: hessenberg-reduction -/
theorem isTridiagonal (h : IsHessenbergForm A Q H) (hA : A.IsHermitian) : IsTridiagonal H :=
  h.hess.isTridiagonal_of_isHermitian (h.isHermitian hA)

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
theorem hasOrthonormalCols_hessenbergQ (A : Matrix (Fin n) (Fin n) ℝ) :
    HasOrthonormalCols (hessenbergQ A) :=
  hasOrthonormalCols_list_prod _ fun M hM => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hM
    exact hasOrthonormalCols_householder v

/-- `QᵀQ = I` for the Hessenberg `Q` (proof-helper form of `hasOrthonormalCols_hessenbergQ`). -/
theorem hessenbergQ_transpose_mul_self (A : Matrix (Fin n) (Fin n) ℝ) :
    (hessenbergQ A)ᵀ * hessenbergQ A = 1 := by
  have h := (hasOrthonormalCols_hessenbergQ A).conjTranspose_mul_self
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The exact factor recursion is `Q(A) = P diag(1,Q(B'))`, where `B = PAP`
and `B'` is its trailing block. Trefethen–Bau, Algorithm 26.1. -/
theorem hessenbergQ_add_three (k : ℕ) (A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ) :
    hessenbergQ A =
      householder (vecCons 0 (householderVector (fun i : Fin (k + 2) => A i.succ 0) 0)) *
      borderedUpper (vecCons 1 0) (hessenbergQ
        ((householder (vecCons 0 (householderVector (fun i : Fin (k + 2) => A i.succ 0) 0)) *
          A * householder (vecCons 0
            (householderVector (fun i : Fin (k + 2) => A i.succ 0) 0))).submatrix
          Fin.succ Fin.succ)) := by
  rw [hessenbergQ, hessenbergReflectors, List.map_cons, List.prod_cons,
    prod_map_householder_map_vecCons_zero]
  rfl

/--
**The reduction produces a Hessenberg matrix**: `QᵀAQ` is upper Hessenberg for the Householder
`Q`, for every `A`. Trefethen–Bau 1997, Lect. 26 (Alg. 26.1); Golub–Van Loan 2013, §7.4.3.
The block recursion preserves the first-column support and reduces the trailing block dimension.
atlas: hessenberg-reduction -/
theorem isUpperHessenberg_hessenbergH : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    IsUpperHessenberg (hessenbergH A)
  | 0, _ => by intro i; exact i.elim0
  | 1, _ => by intro i j hij; have := i.isLt; omega
  | 2, _ => by intro i j hij; have := i.isLt; omega
  | k + 3, A => by
    let x : Fin (k + 2) → ℝ := fun i => A i.succ 0
    let w := householderVector x 0
    let P := householder (vecCons 0 w)
    let B := P * A * P
    let U := hessenbergQ (B.submatrix Fin.succ Fin.succ)
    let D := borderedUpper (vecCons 1 0) U
    have hQ : hessenbergQ A = P * D := hessenbergQ_add_three k A
    have hform : hessenbergH A = Dᵀ * B * D := by
      rw [hessenbergH, hQ, Matrix.transpose_mul]
      change (Dᵀ * Pᵀ) * A * (P * D) = Dᵀ * (P * A * P) * D
      rw [show Pᵀ = P from householder_transpose _]
      simp only [Matrix.mul_assoc]
    have hBcol : (fun i : Fin (k + 2) => B i.succ 0) =
        (-(householderSign (x 0) * ‖WithLp.toLp 2 x‖)) • Pi.single 0 1 := by
      calc
        _ = householder w *ᵥ x := by
          ext i
          simp [B, P, householder_vecCons_zero, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, Fin.sum_univ_succ, x]
        _ = _ := householder_mulVec_householderVector x 0
    have hU : U *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
      hessenbergQ_mulVec_single_zero _
    have hUt : Uᵀ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      calc
        _ = Uᵀ *ᵥ (U *ᵥ Pi.single 0 1) := by rw [hU]
        _ = _ := by rw [Matrix.mulVec_mulVec,
          show Uᵀ * U = 1 from hessenbergQ_transpose_mul_self _, Matrix.one_mulVec]
    have htail : (hessenbergH A).submatrix Fin.succ Fin.succ =
        hessenbergH (B.submatrix Fin.succ Fin.succ) := by
      rw [hform, submatrix_borderedUpper_transpose_mul_mul]
      rfl
    intro i j hij
    induction i using Fin.cases with
    | zero => simp at hij
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        rw [hform, borderedUpper_transpose_mul_mul_succ_zero, hBcol,
          Matrix.mulVec_smul, hUt, Pi.smul_apply]
        rw [Pi.single_eq_of_ne (show i ≠ 0 by intro h; subst i; simp at hij), smul_zero]
      | succ j =>
        have he := congrFun (congrFun htail i) j
        change hessenbergH A i.succ j.succ = _ at he
        rw [he]
        exact isUpperHessenberg_hessenbergH _ i j (by simpa using hij)

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

/-- **Implicit Q theorem**: two Hessenberg forms with equal first orthogonal columns and
an unreduced first Hessenberg matrix differ by a diagonal sign matrix, whose first entry is one.
Source: Golub–Van Loan 2013, Theorem 7.4.2; matrix toolkit rederivations, `lem:intertwine`.
The oriented equation `H₂(Q₂ᵀQ₁)=(Q₂ᵀQ₁)H₁` uses precisely the given unreduced matrix.
atlas: hessenberg-reduction -/
theorem IsHessenbergForm.exists_sign {A Q₁ H₁ Q₂ H₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h₁ : IsHessenbergForm A Q₁ H₁) (h₂ : IsHessenbergForm A Q₂ H₂)
    (hcol : Q₁.col 0 = Q₂.col 0) (hH : IsUnreducedHessenberg H₁) :
    ∃ d : Fin (n + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧
      Q₂ = Q₁ * diagonal d ∧ H₂ = diagonal d * H₁ * diagonal d := by
  let W := Q₂ᵀ * Q₁
  have hWOrth : HasOrthonormalCols W := by
    change Wᵀ * W = 1
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q₂ Q₂ᵀ Q₁, h₂.mul_transpose_self, Matrix.one_mul]
    exact h₁.orth
  have hleft : Q₂ᵀ * A = H₂ * Q₂ᵀ := by
    rw [h₂.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show Q₂ᵀ * Q₂ = 1 from h₂.orth, Matrix.one_mul]
  have hright : A * Q₁ = Q₁ * H₁ := by
    rw [h₁.eq, Matrix.mul_assoc, Matrix.mul_assoc,
      show Q₁ᵀ * Q₁ = 1 from h₁.orth, Matrix.mul_one]
  have hcomm : H₂ * W = W * H₁ := by
    dsimp [W]
    rw [← Matrix.mul_assoc, ← hleft, Matrix.mul_assoc, hright, ← Matrix.mul_assoc]
  have hWcol : W.col 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).col 0 := by
    ext i
    change (Q₂ᵀ * Q₁) i 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i 0
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    have hcols : ∀ k, Q₁ k 0 = Q₂ k 0 := fun k => congrFun hcol k
    simp_rw [hcols]
    have h := congrFun (congrFun (show Q₂ᵀ * Q₂ = 1 from h₂.orth) i) 0
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using h
  have hWU := isUpperTriangular_of_hessenberg_intertwines h₂.hess hH hcomm hWcol
  obtain ⟨d, hd, hdiag⟩ := exists_diagonal_sign_of_isUpperTriangular hWU hWOrth
  have hd0 : d 0 = 1 := by
    have h := congrFun hWcol 0
    rw [hdiag] at h
    simpa only [Matrix.col_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using h
  have hDsq : Matrix.diagonal d * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      rcases hd i with h | h <;> simp [h]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hQ₁ : Q₁ = Q₂ * Matrix.diagonal d := by
    rw [← hdiag]
    dsimp [W]
    rw [← Matrix.mul_assoc, h₂.mul_transpose_self, Matrix.one_mul]
  have hQ₂ : Q₂ = Q₁ * Matrix.diagonal d := by
    rw [hQ₁, Matrix.mul_assoc, hDsq, Matrix.mul_one]
  refine ⟨d, hd, hd0, hQ₂, ?_⟩
  rw [← h₂.transpose_mul_mul_eq, hQ₂, Matrix.transpose_mul, Matrix.diagonal_transpose]
  have heq : (Matrix.diagonal d * Q₁ᵀ) * A * (Q₁ * Matrix.diagonal d) =
      Matrix.diagonal d * (Q₁ᵀ * A * Q₁) * Matrix.diagonal d := by simp only [Matrix.mul_assoc]
  rw [heq, h₁.transpose_mul_mul_eq]

end NLAlib
