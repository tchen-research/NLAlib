import NLAlib.Matrix.Factorizations.QR
/-!
# Linear least squares in exact arithmetic

For `A : Matrix m n ℝ` and `b : m → ℝ`, `IsLeastSquaresSolution A b x` says that `x` minimises
`‖b - A x‖₂²` (written `(b - A x) ⬝ᵥ (b - A x)`). This file proves the classical
characterisations (Trefethen–Bau 1997, Lecture 11, Thm 11.1; Golub–Van Loan 2013, §5.3):

* `isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq`: minimiser iff the normal equations
  `Aᵀ A x = Aᵀ b`;
* `isLeastSquaresSolution_iff_forall_dotProduct_mulVec_eq_zero`: iff the residual `b - A x` is
  orthogonal to `range A`;
* `isLeastSquaresSolution_moorePenroseInverse_mulVec`: `x = A⁺ b` is a solution, for every `A`
  (any rank, any shape); `isLeastSquaresSolution_iff_mulVec_eq`: the fitted vector `A x = A A⁺ b`
  is the same for every solution;
* `existsUnique_isLeastSquaresSolution_iff`: the solution is unique iff `rank A = card n`
  (full column rank), and then it is `A⁺ b = (AᵀA)⁻¹Aᵀb`;
* `dotProduct_self_moorePenroseInverse_mulVec_le`: `A⁺ b` is the minimum-norm solution;
* the residual identities `‖b - A x‖² = ‖b‖² - ‖A x‖²` and `b - A x = (I - A A⁺) b`;
* the thin-QR corollary: if `A = Q R` with `QᵀQ = I` and `R` invertible then the solution is
  `R⁻¹ Qᵀ b` and `‖r‖² = ‖b‖² - ‖Qᵀ b‖²` (stated with explicit hypotheses, so it applies to any
  thin QR factorization), and its `IsQR` form (`IsQR.isLeastSquaresSolution_iff`,
  `IsQR.dotProduct_sub_mulVec_eq`) for `NLAlib.Matrix.Factorizations.QR`.

Atlas: `least-squares-normal-equations`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `x` is a (linear) least-squares solution of `A x ≈ b`: it minimises the squared residual
`‖b - A y‖₂² = (b - A y) ⬝ᵥ (b - A y)` over all `y`. Trefethen–Bau 1997, Lecture 11 (problem
(11.2)); Golub–Van Loan 2013, §5.3.1. Every `A` admits one
(`isLeastSquaresSolution_moorePenroseInverse_mulVec`).
atlas: least-squares-normal-equations (partial) -/
def IsLeastSquaresSolution (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  ∀ y : n → ℝ, (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) ≤ (b - A *ᵥ y) ⬝ᵥ (b - A *ᵥ y)

/-- The residual is orthogonal to `range A` iff `Aᵀ (b - A x) = 0`. Trefethen–Bau 1997,
Thm 11.1. -/
theorem transpose_mulVec_eq_zero_iff_forall_dotProduct_mulVec_eq_zero (A : Matrix m n ℝ)
    (r : m → ℝ) : Aᵀ *ᵥ r = 0 ↔ ∀ y : n → ℝ, r ⬝ᵥ A *ᵥ y = 0 := by
  constructor
  · intro h y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h, zero_dotProduct]
  · intro h
    have h1 := h (Aᵀ *ᵥ r)
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at h1
    exact dotProduct_self_eq_zero.mp h1

/-- Pythagoras for least squares: if the residual `r = b - A x` satisfies `Aᵀ r = 0` then
`‖b - A y‖² = ‖b - A x‖² + ‖A (x - y)‖²` for every `y`. Trefethen–Bau 1997, proof of Thm 11.1. -/
theorem dotProduct_sub_mulVec_eq_add_of_transpose_mulVec_eq_zero {A : Matrix m n ℝ}
    {b : m → ℝ} {x : n → ℝ} (h : Aᵀ *ᵥ (b - A *ᵥ x) = 0) (y : n → ℝ) :
    (b - A *ᵥ y) ⬝ᵥ (b - A *ᵥ y) =
      (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) + (A *ᵥ (x - y)) ⬝ᵥ (A *ᵥ (x - y)) := by
  have horth := (transpose_mulVec_eq_zero_iff_forall_dotProduct_mulVec_eq_zero A _).mp h (x - y)
  have hsplit : b - A *ᵥ y = (b - A *ᵥ x) + A *ᵥ (x - y) := by
    rw [Matrix.mulVec_sub]; abel
  rw [hsplit, add_dotProduct, dotProduct_add, dotProduct_add, horth, dotProduct_comm (A *ᵥ _),
    horth]
  ring

/-- **Normal equations.** `x` is a least-squares solution iff `Aᵀ A x = Aᵀ b`.
Trefethen–Bau 1997, Lecture 11, Thm 11.1; Golub–Van Loan 2013, §5.3.1. Proof: `(⇐)` Pythagoras
(`dotProduct_sub_mulVec_eq_add_of_transpose_mulVec_eq_zero`); `(⇒)` perturb `x` along
`g = Aᵀ(b - A x)`: `‖b - A(x + t g)‖² = ‖r‖² - 2t‖g‖² + t²‖Ag‖²`, minimal at `t = 0` only if
`g = 0`.
atlas: least-squares-normal-equations -/
theorem isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq (A : Matrix m n ℝ) (b : m → ℝ)
    (x : n → ℝ) : IsLeastSquaresSolution A b x ↔ Aᵀ *ᵥ (A *ᵥ x) = Aᵀ *ᵥ b := by
  have hiff : Aᵀ *ᵥ (A *ᵥ x) = Aᵀ *ᵥ b ↔ Aᵀ *ᵥ (b - A *ᵥ x) = 0 := by
    rw [Matrix.mulVec_sub, sub_eq_zero, eq_comm]
  rw [hiff]
  constructor
  · intro hmin
    set r := b - A *ᵥ x with hr
    set g := Aᵀ *ᵥ r
    set c := g ⬝ᵥ g
    set d := (A *ᵥ g) ⬝ᵥ (A *ᵥ g) with hddef
    have hc : 0 ≤ c := dotProduct_self_nonneg g
    have hd : 0 ≤ d := dotProduct_self_nonneg _
    have hrg : r ⬝ᵥ A *ᵥ g = c := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have key : ∀ t : ℝ, 0 ≤ -2 * t * c + t ^ 2 * d := by
      intro t
      have hres : b - A *ᵥ (x + t • g) = r - t • (A *ᵥ g) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hr]; abel
      have h1 : r ⬝ᵥ r ≤ (r - t • (A *ᵥ g)) ⬝ᵥ (r - t • (A *ᵥ g)) := by
        rw [← hres, hr]; exact hmin _
      clear_value r g c d
      have hexp :
          (r - t • (A *ᵥ g)) ⬝ᵥ (r - t • (A *ᵥ g)) = r ⬝ᵥ r - 2 * t * c + t ^ 2 * d := by
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          dotProduct_comm (A *ᵥ g) r, hrg]
        rw [hddef]; ring
      rw [hexp] at h1
      linarith
    have h2 := key (c / (d + 1))
    have hd1 : 0 < d + 1 := by linarith
    have h3 : 0 ≤ c ^ 2 * (-(d + 2)) / (d + 1) ^ 2 := by
      have : -2 * (c / (d + 1)) * c + (c / (d + 1)) ^ 2 * d =
          c ^ 2 * (-(d + 2)) / (d + 1) ^ 2 := by
        field_simp; ring
      linarith
    have h4 : c ^ 2 * (-(d + 2)) ≥ 0 := by
      have := mul_nonneg h3 (sq_nonneg (d + 1))
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    have hc0 : c = 0 := by nlinarith
    exact dotProduct_self_eq_zero.mp hc0
  · intro h y
    rw [dotProduct_sub_mulVec_eq_add_of_transpose_mulVec_eq_zero h y]
    exact le_add_of_nonneg_right (dotProduct_self_nonneg _)

/-- A least-squares solution is exactly a vector whose residual is orthogonal to `range A`:
`(b - A x) ⬝ (A y) = 0` for all `y`. Trefethen–Bau 1997, Lecture 11, Thm 11.1 (the condition
`r ⟂ range(A)`).
atlas: least-squares-normal-equations (partial) -/
theorem isLeastSquaresSolution_iff_forall_dotProduct_mulVec_eq_zero (A : Matrix m n ℝ)
    (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquaresSolution A b x ↔ ∀ y : n → ℝ, (b - A *ᵥ x) ⬝ᵥ A *ᵥ y = 0 := by
  rw [isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq,
    ← transpose_mulVec_eq_zero_iff_forall_dotProduct_mulVec_eq_zero, Matrix.mulVec_sub,
    sub_eq_zero, eq_comm]

/-- `Aᵀ (A A⁺) = Aᵀ`: the column-space projector fixes the rows of `Aᵀ`.
Stewart–Sun 1990, §III.1. -/
theorem transpose_mul_mul_moorePenroseInverse (A : Matrix m n ℝ) :
    Aᵀ * (A * moorePenroseInverse A) = Aᵀ := by
  rw [← (mul_moorePenroseInverse_isHermitian A).eq, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← Matrix.transpose_mul,
    mul_moorePenroseInverse_mul]

/-- **Pseudoinverse solution.** `A⁺ b` is a least-squares solution for every `A` (any rank,
any shape, including empty dimensions). Trefethen–Bau 1997, Lecture 11 (eq. (11.10)) and
Golub–Van Loan 2013, §5.5.2; proof by the normal equations and `Aᵀ A A⁺ = Aᵀ`.
atlas: least-squares-normal-equations (partial) -/
theorem isLeastSquaresSolution_moorePenroseInverse_mulVec (A : Matrix m n ℝ) (b : m → ℝ) :
    IsLeastSquaresSolution A b (moorePenroseInverse A *ᵥ b) := by
  rw [isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, transpose_mul_mul_moorePenroseInverse]

/-- A least-squares solution always exists. Trefethen–Bau 1997, Thm 11.1. -/
theorem exists_isLeastSquaresSolution (A : Matrix m n ℝ) (b : m → ℝ) :
    ∃ x, IsLeastSquaresSolution A b x :=
  ⟨_, isLeastSquaresSolution_moorePenroseInverse_mulVec A b⟩

/-- The fitted vector is unique: `x` is a least-squares solution iff `A x = A A⁺ b`, the
orthogonal projection of `b` onto `range A`. Trefethen–Bau 1997, Lecture 11, Thm 11.1
(`Ax = Pb`).
atlas: least-squares-normal-equations (partial) -/
theorem isLeastSquaresSolution_iff_mulVec_eq (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquaresSolution A b x ↔ A *ᵥ x = (A * moorePenroseInverse A) *ᵥ b := by
  have h0 := (isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq A b _).mp
    (isLeastSquaresSolution_moorePenroseInverse_mulVec A b)
  rw [isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq]
  constructor
  · intro h
    have hz : Aᵀ *ᵥ (A *ᵥ (x - moorePenroseInverse A *ᵥ b)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, h, h0, sub_self]
    have h1 := congrArg (dotProduct (x - moorePenroseInverse A *ᵥ b)) hz
    rw [dotProduct_zero, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_self_eq_zero, Matrix.mulVec_sub, sub_eq_zero, Matrix.mulVec_mulVec] at h1
    exact h1
  · intro h
    rw [h, Matrix.mulVec_mulVec, transpose_mul_mul_moorePenroseInverse]

/-- The least-squares residual is `(I - A A⁺) b`, for every least-squares solution.
Trefethen–Bau 1997, Lecture 11 (`r = (I - P) b`).
atlas: least-squares-normal-equations (partial) -/
theorem IsLeastSquaresSolution.sub_mulVec_eq [DecidableEq m] {A : Matrix m n ℝ} {b : m → ℝ}
    {x : n → ℝ} (h : IsLeastSquaresSolution A b x) :
    b - A *ᵥ x = (1 - A * moorePenroseInverse A) *ᵥ b := by
  rw [(isLeastSquaresSolution_iff_mulVec_eq A b x).mp h, Matrix.sub_mulVec, Matrix.one_mulVec]

/-- **Residual identity.** For a least-squares solution, `‖b - A x‖² = ‖b‖² - ‖A x‖²`
(Pythagoras, `b = A x + r` with `r ⟂ A x`). Trefethen–Bau 1997, Lecture 11; Golub–Van Loan
2013, §5.3.
atlas: least-squares-normal-equations (partial) -/
theorem IsLeastSquaresSolution.dotProduct_sub_mulVec_eq {A : Matrix m n ℝ} {b : m → ℝ}
    {x : n → ℝ} (h : IsLeastSquaresSolution A b x) :
    (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) = b ⬝ᵥ b - (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  have horth := (isLeastSquaresSolution_iff_forall_dotProduct_mulVec_eq_zero A b x).mp h x
  have hb : b = (b - A *ᵥ x) + A *ᵥ x := by abel
  conv_rhs => rw [hb]
  rw [add_dotProduct, dotProduct_add, dotProduct_add, horth, dotProduct_comm (A *ᵥ x), horth]
  ring

omit [Fintype m] in
/-- Full column rank as a kernel condition: `rank A = card n` iff `A v = 0 → v = 0`.
Rank–nullity (`LinearMap.finrank_range_add_finrank_ker`). -/
theorem rank_eq_card_iff_forall_mulVec_eq_zero (A : Matrix m n ℝ) :
    A.rank = Fintype.card n ↔ ∀ v : n → ℝ, A *ᵥ v = 0 → v = 0 := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [← Matrix.ker_mulVecLin_eq_bot_iff, ← Submodule.finrank_eq_zero]
  change Module.finrank ℝ (LinearMap.range A.mulVecLin) = Fintype.card n ↔ _
  omega

/-- Under full column rank the Gram matrix `Aᵀ A` is invertible. Golub–Van Loan 2013, §5.3.1. -/
theorem isUnit_transpose_mul_self_of_rank_eq [DecidableEq n] {A : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n) : IsUnit (Aᵀ * A) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  apply (rank_eq_card_iff_forall_mulVec_eq_zero A).mp hA
  have hAv' : Aᵀ *ᵥ (A *ᵥ v) = 0 := by rwa [Matrix.mulVec_mulVec]
  have h1 := congrArg (dotProduct v) hAv'
  rwa [dotProduct_zero, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    dotProduct_self_eq_zero] at h1

/-- **Uniqueness.** The least-squares solution is unique iff `A` has full column rank
(`rank A = card n`), for every right-hand side `b`. Trefethen–Bau 1997, Lecture 11, Thm 11.1
(uniqueness clause); Golub–Van Loan 2013, §5.3.1. The solution set is `A⁺ b + ker A`.
atlas: least-squares-normal-equations -/
theorem existsUnique_isLeastSquaresSolution_iff (A : Matrix m n ℝ) (b : m → ℝ) :
    (∃! x, IsLeastSquaresSolution A b x) ↔ A.rank = Fintype.card n := by
  rw [rank_eq_card_iff_forall_mulVec_eq_zero]
  set x₀ := moorePenroseInverse A *ᵥ b
  have h₀ := isLeastSquaresSolution_moorePenroseInverse_mulVec A b
  constructor
  · rintro ⟨x, -, hx⟩ v hv
    have h1 : IsLeastSquaresSolution A b (x₀ + v) := by
      rw [isLeastSquaresSolution_iff_mulVec_eq, Matrix.mulVec_add, hv, add_zero,
        Matrix.mulVec_mulVec]
    have h2 : x₀ + v = x₀ := (hx _ h1).trans (hx _ h₀).symm
    exact add_eq_left.mp h2
  · intro hinj
    refine ⟨x₀, h₀, fun y hy => ?_⟩
    have hy' := (isLeastSquaresSolution_iff_mulVec_eq A b y).mp hy
    rw [← Matrix.mulVec_mulVec] at hy'
    exact sub_eq_zero.mp (hinj _ (by rw [Matrix.mulVec_sub, hy', sub_self]))

/-- Under full column rank the least-squares solution is `A⁺ b`. Trefethen–Bau 1997,
Lecture 11 (eq. (11.10)).
atlas: least-squares-normal-equations (partial) -/
theorem isLeastSquaresSolution_iff_eq_moorePenroseInverse_mulVec {A : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n) (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquaresSolution A b x ↔ x = moorePenroseInverse A *ᵥ b := by
  obtain ⟨x₀, -, hu⟩ := (existsUnique_isLeastSquaresSolution_iff A b).mpr hA
  constructor
  · intro hx
    exact (hu x hx).trans (hu _ (isLeastSquaresSolution_moorePenroseInverse_mulVec A b)).symm
  · rintro rfl
    exact isLeastSquaresSolution_moorePenroseInverse_mulVec A b

/-- Under full column rank the least-squares solution is `(Aᵀ A)⁻¹ Aᵀ b` (`pinvL`), the solution
of the normal equations. Trefethen–Bau 1997, Lecture 11, eq. (11.9); Golub–Van Loan 2013,
§5.3.1.
atlas: least-squares-normal-equations (partial) -/
theorem isLeastSquaresSolution_iff_eq_pinvL_mulVec [DecidableEq n] {A : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n) (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquaresSolution A b x ↔ x = pinvL A *ᵥ b := by
  rw [isLeastSquaresSolution_iff_eq_moorePenroseInverse_mulVec hA,
    moorePenroseInverse_eq_pinvL A (isUnit_transpose_mul_self_of_rank_eq hA)]

/-- **Minimum-norm solution.** Among all least-squares solutions, `A⁺ b` has the smallest
Euclidean norm: `‖A⁺ b‖² ≤ ‖x‖²`, since `x = A⁺ b + z` with `A z = 0` and `A⁺ b ⟂ ker A`.
Golub–Van Loan 2013, §5.5.2 (eq. (5.5.6)); Trefethen–Bau 1997, Exercise 11.2.
atlas: least-squares-normal-equations (partial) -/
theorem IsLeastSquaresSolution.dotProduct_self_moorePenroseInverse_mulVec_le
    {A : Matrix m n ℝ} {b : m → ℝ} {x : n → ℝ} (h : IsLeastSquaresSolution A b x) :
    (moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b) ≤ x ⬝ᵥ x := by
  set A' := moorePenroseInverse A
  set x₀ := A' *ᵥ b
  set z := x - x₀ with hzdef
  have hz : A *ᵥ z = 0 := by
    have hx := (isLeastSquaresSolution_iff_mulVec_eq A b x).mp h
    rw [Matrix.mulVec_sub, hx, Matrix.mulVec_mulVec, sub_self]
  have horth : x₀ ⬝ᵥ z = 0 := by
    have hA' : A' = Aᵀ * A'ᵀ * A' := by
      rw [← Matrix.transpose_mul, ← Matrix.conjTranspose_eq_transpose_of_trivial,
        (moorePenroseInverse_mul_isHermitian A).eq,
        moorePenroseInverse_mul_moorePenroseInverse]
    have hx₀ : x₀ = Aᵀ *ᵥ ((A'ᵀ * A') *ᵥ b) := by
      change A' *ᵥ b = _
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← hA']
    rw [hx₀, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hz,
      zero_dotProduct]
  have hx : x = x₀ + z := by rw [hzdef]; abel
  rw [hx, add_dotProduct, dotProduct_add, dotProduct_add, horth, dotProduct_comm z, horth]
  linarith [dotProduct_self_nonneg z]

/-! ### The thin-QR solution -/

/-- **Least squares via thin QR.** If `A = Q R` with `QᵀQ = I` (`HasOrthonormalCols Q`) and `R`
square invertible, the least-squares solutions are exactly `x = R⁻¹ Qᵀ b`. Trefethen–Bau 1997,
Lecture 11, Algorithm 11.2; Golub–Van Loan 2013, §5.3.3. Stated with explicit hypotheses so that
any thin QR (Householder, Gram–Schmidt, `IsQR`) applies; invertibility of `R` is full column
rank. Proof: `AᵀA = RᵀR`, `Aᵀb = RᵀQᵀb`, cancel the invertible `Rᵀ`.
atlas: least-squares-normal-equations (partial) -/
theorem isLeastSquaresSolution_iff_eq_inv_mulVec_of_eq_mul [DecidableEq n]
    {A : Matrix m n ℝ} {Q : Matrix m n ℝ} {R : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (hA : A = Q * R) (hR : IsUnit R) (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquaresSolution A b x ↔ x = R⁻¹ *ᵥ (Qᵀ *ᵥ b) := by
  have hd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR
  have hdt : IsUnit Rᵀ.det := by rwa [Matrix.det_transpose]
  have hQ' : Qᵀ * Q = 1 := hQ
  have hG : Rᵀ * Qᵀ * (Q * R) = Rᵀ * R := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ', Matrix.one_mul]
  have e1 : Aᵀ *ᵥ (A *ᵥ x) = Rᵀ *ᵥ (R *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, hA, Matrix.transpose_mul, hG, ← Matrix.mulVec_mulVec]
  have e2 : Aᵀ *ᵥ b = Rᵀ *ᵥ (Qᵀ *ᵥ b) := by
    rw [hA, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  have hcT : ∀ v : n → ℝ, Rᵀ⁻¹ *ᵥ (Rᵀ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdt, Matrix.one_mulVec]
  have hc : ∀ v : n → ℝ, R⁻¹ *ᵥ (R *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  have hc' : ∀ v : n → ℝ, R *ᵥ (R⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  rw [isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq, e1, e2]
  constructor
  · intro h
    have hRx : R *ᵥ x = Qᵀ *ᵥ b := by rw [← hcT (R *ᵥ x), h, hcT]
    rw [← hRx, hc]
  · rintro rfl
    rw [hc']

/-- **Residual via thin QR.** If `A = Q R` with `QᵀQ = I` and `R` invertible, the least-squares
residual satisfies `‖b - A x‖² = ‖b‖² - ‖Qᵀ b‖²`. Trefethen–Bau 1997, Lecture 11; Golub–Van Loan
2013, §5.3.3 (eq. (5.3.6)).
atlas: least-squares-normal-equations (partial) -/
theorem IsLeastSquaresSolution.dotProduct_sub_mulVec_eq_of_eq_mul [DecidableEq n]
    {A : Matrix m n ℝ} {Q : Matrix m n ℝ} {R : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (hA : A = Q * R) (hR : IsUnit R) {b : m → ℝ} {x : n → ℝ}
    (h : IsLeastSquaresSolution A b x) :
    (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) = b ⬝ᵥ b - (Qᵀ *ᵥ b) ⬝ᵥ (Qᵀ *ᵥ b) := by
  have hd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR
  have hx := (isLeastSquaresSolution_iff_eq_inv_mulVec_of_eq_mul hQ hA hR b x).mp h
  have hAx : A *ᵥ x = Q *ᵥ (Qᵀ *ᵥ b) := by
    rw [hx, hA, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
      Matrix.mul_one]
  rw [h.dotProduct_sub_mulVec_eq, hAx,
    show (Q *ᵥ (Qᵀ *ᵥ b)) ⬝ᵥ (Q *ᵥ (Qᵀ *ᵥ b)) = (Qᵀ *ᵥ b) ⬝ᵥ (Qᵀ *ᵥ b) from
      star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ _]

/-- **Least squares via `IsQR`.** For a thin QR factorization `IsQR A Q R` with nonzero diagonal
(`R_ii ≠ 0`, i.e. full column rank), the least-squares solution is `x = R⁻¹ Qᵀ b`.
Trefethen–Bau 1997, Lecture 11, Algorithm 11.2; Golub–Van Loan 2013, §5.3.3.
atlas: least-squares-normal-equations (partial) -/
theorem IsQR.isLeastSquaresSolution_iff {n : ℕ} {A Q : Matrix m (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) (b : m → ℝ)
    (x : Fin n → ℝ) : IsLeastSquaresSolution A b x ↔ x = R⁻¹ *ᵥ (Qᵀ *ᵥ b) :=
  isLeastSquaresSolution_iff_eq_inv_mulVec_of_eq_mul h.orth h.eq
    ((Matrix.isUnit_iff_isUnit_det R).mpr (h.isUnit_det_iff.mpr hR)) b x

/-- **Residual via `IsQR`.** For `IsQR A Q R` with nonzero diagonal and a least-squares solution
`x`, `‖b - A x‖² = ‖b‖² - ‖Qᵀ b‖²`. Trefethen–Bau 1997, Lecture 11; Golub–Van Loan 2013, §5.3.3.
atlas: least-squares-normal-equations (partial) -/
theorem IsQR.dotProduct_sub_mulVec_eq {n : ℕ} {A Q : Matrix m (Fin n) ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) {b : m → ℝ}
    {x : Fin n → ℝ} (hx : IsLeastSquaresSolution A b x) :
    (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) = b ⬝ᵥ b - (Qᵀ *ᵥ b) ⬝ᵥ (Qᵀ *ᵥ b) :=
  hx.dotProduct_sub_mulVec_eq_of_eq_mul h.orth h.eq
    ((Matrix.isUnit_iff_isUnit_det R).mpr (h.isUnit_det_iff.mpr hR))

end NLAlib
