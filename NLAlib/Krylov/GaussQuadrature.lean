import NLAlib.Krylov.Polynomial
import NLAlib.Krylov.SpectralMeasure
import NLAlib.Matrix.Projections

/-!
# Gauss (Lanczos) quadrature: exactness and error

Let `A` be symmetric, `b` a vector and `Q` a matrix with orthonormal columns whose range contains
the Krylov space `K_q(A, b)`, `q ≥ 1`. With the projected matrix `B = Qᵀ A Q` and `c = Qᵀ b`,
the "Lanczos quadrature" `cᵀ p(B) c` reproduces `bᵀ p(A) b` exactly for every polynomial of degree
at most `2q − 1`. This is the exactness of the `q`-node Gauss quadrature rule for the spectral
measure `μ_b` (`NLAlib.spectralMeasure`): when `Q` is the Lanczos basis, `B` is the Jacobi matrix
`T_q` and `c = ‖b‖ e₁`.

## Main results

* `NLAlib.dotProduct_aeval_mulVec_eq_of_krylovSpace_le`: exactness for `deg p ≤ 2q − 1`.
* `NLAlib.dotProduct_cfc_mulVec_eq_sum_eigenvalues_le` and friends: Rayleigh bounds and the
  fact that the eigenvalues of `Qᵀ A Q` stay in any interval containing those of `A`.
* `NLAlib.abs_dotProduct_cfc_mulVec_sub_le_of_krylovSpace_le`: the quadrature error
  `|bᵀ f(A) b − cᵀ f(B) c| ≤ 2 E ‖b‖²` when `|f − p| ≤ E` on an interval containing the spectrum
  of `A`, for some `p` of degree at most `2q − 1`.

Source: Golub–Meurant (2010) [`gm10`], Ch. 6–7 (Thm 6.6 exactness of Gauss quadrature);
Chen–Trogdon–Ubaru (2021) [`ctu21`], Thm 2.1. Atlas: `lanczos-gauss-quadrature`.
Deviation from the printed statements: any orthonormal `Q` with `K_q(A,b) ⊆ range Q` is
allowed, so neither tridiagonality nor the Lanczos recurrence is used.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq n] in
/-- If `Q` has orthonormal columns and `x ∈ range Q`, then `Q Qᵀ x = x`.
Atlas: `lanczos-gauss-quadrature` (helper; belongs in `NLAlib.Matrix.Projections`). -/
theorem mulVec_transpose_mulVec_of_mem_range {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    {x : n → ℝ} (hx : x ∈ LinearMap.range Q.mulVecLin) : Q *ᵥ (Qᵀ *ᵥ x) = x := by
  obtain ⟨y, rfl⟩ := hx
  have h : Qᵀ *ᵥ (Q *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec]
  simp only [Matrix.mulVecLin_apply, h]

/-- For a symmetric `M`, `v ⬝ (Mⁱ N) v = (Mⁱ v) ⬝ (N v)`. -/
private lemma dotProduct_pow_mul_mulVec {M : Matrix n n ℝ} (hM : M.IsSymm)
    (N : Matrix n n ℝ) (i : ℕ) (v : n → ℝ) :
    v ⬝ᵥ ((M ^ i * N) *ᵥ v) = (M ^ i *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    (hM.pow i).eq]

omit [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- The projected matrix `Qᵀ A Q` of a symmetric `A` is symmetric.
Atlas: `lanczos-gauss-quadrature` (helper). -/
theorem isSymm_transpose_mul_mul {A : Matrix n n ℝ} (hA : A.IsSymm) (Q : Matrix n k ℝ) :
    (Qᵀ * A * Q).IsSymm := by
  rw [IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
    Matrix.mul_assoc]

/-- Lifting the projected powers: if `K_q(A,b) ⊆ range Q` then `Q (QᵀAQ)ʲ Qᵀ b = Aʲ b` for
`j < q`. Atlas: `lanczos-gauss-quadrature` (helper). -/
theorem mulVec_pow_transpose_mul_mul_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {j : ℕ} (hj : j < q) :
    Q *ᵥ ((Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b)) = A ^ j *ᵥ b := by
  induction j with
  | zero =>
    simpa using mulVec_transpose_mulVec_of_mem_range hQ
      (hK (by simpa using pow_mulVec_mem_krylovSpace A b hj))
  | succ j ih =>
    have ih := ih (Nat.lt_of_succ_lt hj)
    have hstep : (Qᵀ * A * Q) ^ (j + 1) *ᵥ (Qᵀ *ᵥ b) = Qᵀ *ᵥ (A ^ (j + 1) *ᵥ b) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        show A *ᵥ (A ^ j *ᵥ b) = A ^ (j + 1) *ᵥ b by rw [Matrix.mulVec_mulVec, ← pow_succ']]
    rw [hstep]
    exact mulVec_transpose_mulVec_of_mem_range hQ (hK (pow_mulVec_mem_krylovSpace A b hj))

/-- Exactness on monomials `X^m`, `m ≤ 2q − 1`. -/
private lemma dotProduct_pow_mulVec_eq {A : Matrix n n ℝ} (hA : A.IsSymm) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {m : ℕ} (hm : m ≤ 2 * q - 1) :
    b ⬝ᵥ (A ^ m *ᵥ b) = (Qᵀ *ᵥ b) ⬝ᵥ ((Qᵀ * A * Q) ^ m *ᵥ (Qᵀ *ᵥ b)) := by
  set B := Qᵀ * A * Q with hBdef
  set c := Qᵀ *ᵥ b
  have hB : B.IsSymm := isSymm_transpose_mul_mul hA Q
  have hlift := fun {j : ℕ} (hj : j < q) => mulVec_pow_transpose_mul_mul_mulVec_eq hQ b hK hj
  have hQQ : ∀ x y : k → ℝ, (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y := fun x y => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec]
  have hBv : ∀ w : k → ℝ, B *ᵥ w = Qᵀ *ᵥ (A *ᵥ (Q *ᵥ w)) := fun w => by
    simp only [hBdef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hQt : ∀ (x : k → ℝ) (z : n → ℝ), x ⬝ᵥ (Qᵀ *ᵥ z) = (Q *ᵥ x) ⬝ᵥ z := fun x z => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  -- the two generic splittings
  have hsplit0 : ∀ i j, i < q → j < q →
      b ⬝ᵥ (A ^ (i + j) *ᵥ b) = c ⬝ᵥ (B ^ (i + j) *ᵥ c) := fun i j hi hj => by
    rw [pow_add, pow_add, dotProduct_pow_mul_mulVec hA, dotProduct_pow_mul_mulVec hB,
      ← hlift hi, ← hlift hj, hQQ]
  have hsplit1 : ∀ i j, i < q → j < q →
      b ⬝ᵥ (A ^ (i + 1 + j) *ᵥ b) = c ⬝ᵥ (B ^ (i + 1 + j) *ᵥ c) := fun i j hi hj => by
    rw [add_assoc, pow_add A, pow_add A 1, pow_one, pow_add B, pow_add B 1, pow_one,
      dotProduct_pow_mul_mulVec hA,
      dotProduct_pow_mul_mulVec hB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBv, hQt,
      hlift hi, hlift hj]
  rcases Nat.lt_or_ge m (2 * q - 1) with hlt | hge
  · obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < q ∧ j < q ∧ m = i + j :=
      ⟨min m (q - 1), m - min m (q - 1), by omega, by omega, by omega⟩
    exact hsplit0 i j hi hj
  · obtain rfl : m = (q - 1) + 1 + (q - 1) := by omega
    exact hsplit1 _ _ (by omega) (by omega)

/-- **Gauss (Lanczos) quadrature is exact for degree `≤ 2q − 1`.** If `A` is symmetric,
`Q` has orthonormal columns, `q ≥ 1` and `K_q(A,b) ⊆ range Q`, then for every polynomial `p`
with `natDegree p ≤ 2q − 1`, `bᵀ p(A) b = (Qᵀb)ᵀ p(QᵀAQ) (Qᵀb)`.
Source: Golub–Meurant (2010) [`gm10`], Thm 6.6 and §7.1; Chen–Trogdon–Ubaru (2021) [`ctu21`],
Thm 2.1. Atlas: `lanczos-gauss-quadrature`.
Deviation: any orthonormal `Q` whose range contains `K_q(A,b)`; with the Lanczos basis,
`Qᵀb = ‖b‖e₁` and the right side is `‖b‖² (p(T_q))₁₁`. The hypothesis `0 < q` is needed (at
`q = 0` the degree bound is `≤ 0` in ℕ and the claim fails unless `b ∈ range Q`).
atlas: lanczos-gauss-quadrature -/
theorem dotProduct_aeval_mulVec_eq_of_krylovSpace_le {A : Matrix n n ℝ} (hA : A.IsSymm)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {p : Polynomial ℝ}
    (hp : p.natDegree ≤ 2 * q - 1) :
    b ⬝ᵥ (Polynomial.aeval A p *ᵥ b) =
      (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec,
    Matrix.sum_mulVec, dotProduct_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
    dotProduct_pow_mulVec_eq hA hQ b hq hK
      ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)).trans hp)]

/-! ### Rayleigh bounds and the quadrature error -/

/-- Rayleigh bounds from an eigenvalue enclosure: if every eigenvalue of the symmetric `A` lies
in `[a, c]`, then `a ‖x‖² ≤ xᵀ A x ≤ c ‖x‖²`. Lower half.
Source: Horn–Johnson (2013), Thm 4.2.2 (Rayleigh–Ritz). Atlas: `lanczos-gauss-quadrature`
(helper; belongs in `NLAlib.Matrix`). -/
theorem mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a : ℝ} (ha : ∀ i, a ≤ hA.eigenvalues i) (x : n → ℝ) :
    a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have h := dotProduct_cfc_mulVec_eq_sum hA id x
  rw [cfc_id ℝ A] at h
  rw [h, ← sum_sq_eigenvectorBasis_dotProduct hA x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)

/-- Upper Rayleigh bound from an eigenvalue enclosure: `xᵀ A x ≤ c ‖x‖²` if every eigenvalue is
at most `c`. Source: Horn–Johnson (2013), Thm 4.2.2. Atlas: `lanczos-gauss-quadrature`
(helper). -/
theorem dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, hA.eigenvalues i ≤ c) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x) := by
  have h := dotProduct_cfc_mulVec_eq_sum hA id x
  rw [cfc_id ℝ A] at h
  rw [h, ← sum_sq_eigenvectorBasis_dotProduct hA x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

/-- An eigenvalue is the Rayleigh quotient of its unit eigenvector: `λᵢ = uᵢᵀ A uᵢ`.
Atlas: `lanczos-gauss-quadrature` (helper). -/
theorem eigenvalues_eq_dotProduct_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i =
      (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (A *ᵥ (hA.eigenvectorBasis i : n → ℝ)) := by
  simpa [dotProduct_comm] using hA.eigenvalues_eq i

/-- The eigenvector basis consists of unit vectors: `uᵢ ⬝ uᵢ = 1`. Atlas:
`lanczos-gauss-quadrature` (helper). -/
theorem eigenvectorBasis_dotProduct_self {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hA.eigenvectorBasis i : n → ℝ) = 1 := by
  have h := hA.eigenvectorBasis.orthonormal.1 i
  have h2 : inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h, one_pow]
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
  simpa using h2

/-- The eigenvalues of the projected matrix `Qᵀ A Q` (`Q` with orthonormal columns) lie in any
interval `[a, c]` containing the eigenvalues of `A` (Ritz values interlace inside the spectral
interval). Source: Golub–Meurant (2010) [`gm10`], Ch. 4; Parlett (1998), Thm 10.1.1 (weak form).
Atlas: `lanczos-gauss-quadrature` (helper). -/
theorem eigenvalues_transpose_mul_mul_mem_Icc {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (hB : (Qᵀ * A * Q).IsHermitian) {a c : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c) (j : k) :
    hB.eigenvalues j ∈ Set.Icc a c := by
  set w : k → ℝ := (hB.eigenvectorBasis j).ofLp
  have hw : w ⬝ᵥ w = 1 := eigenvectorBasis_dotProduct_self hB j
  have hQw : (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) = 1 := by
    rw [mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ, hw]
  have hval : hB.eigenvalues j = (Q *ᵥ w) ⬝ᵥ (A *ᵥ (Q *ᵥ w)) := by
    rw [eigenvalues_eq_dotProduct_mulVec hB j, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec w Qᵀ, Matrix.vecMul_transpose]
  have h1 := mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues hA (fun i => (hspec i).1)
    (Q *ᵥ w)
  have h2 := dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues hA (fun i => (hspec i).2)
    (Q *ᵥ w)
  rw [hQw, mul_one] at h1 h2
  exact ⟨hval ▸ h1, hval ▸ h2⟩

/-- A function bounded by `E` on the eigenvalues gives a quadratic form bounded by `E ‖v‖²`:
`|vᵀ g(A) v| ≤ E (v ⬝ v)`. Atlas: `lanczos-gauss-quadrature` (helper; the `cfc` form of
`polynomial-spectral-bound`). -/
theorem abs_dotProduct_cfc_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {g : ℝ → ℝ}
    {E : ℝ} (hg : ∀ i, |g (hA.eigenvalues i)| ≤ E) (v : n → ℝ) :
    |v ⬝ᵥ (cfc g A *ᵥ v)| ≤ E * (v ⬝ᵥ v) := by
  rw [dotProduct_cfc_mulVec_eq_sum hA g v, ← sum_sq_eigenvectorBasis_dotProduct hA v,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_sq]
  exact mul_le_mul_of_nonneg_right (hg i) (sq_nonneg _)

/-- `vᵀ f(A) v − vᵀ p(A) v = ∑ᵢ (f(λᵢ) − p(λᵢ)) (uᵢ ⬝ v)²`, bounded by `E ‖v‖²`. -/
private lemma abs_dotProduct_cfc_sub_aeval_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {p : Polynomial ℝ} {E : ℝ} (hfp : ∀ i, |f (hA.eigenvalues i) -
      p.eval (hA.eigenvalues i)| ≤ E) (v : n → ℝ) :
    |v ⬝ᵥ (cfc f A *ᵥ v) - v ⬝ᵥ (Polynomial.aeval A p *ᵥ v)| ≤ E * (v ⬝ᵥ v) := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint, dotProduct_cfc_mulVec_eq_sum hA,
    dotProduct_cfc_mulVec_eq_sum hA, ← Finset.sum_sub_distrib,
    ← sum_sq_eigenvectorBasis_dotProduct hA v, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul, abs_sq]
  exact mul_le_mul_of_nonneg_right (hfp i) (sq_nonneg _)

/-- **Error of Gauss (Lanczos) quadrature.** Let `A` be symmetric with spectrum in `[a, c]`, `Q`
with orthonormal columns, `q ≥ 1`, `K_q(A,b) ⊆ range Q`, and `p` a polynomial of degree at most
`2q − 1` with `|f − p| ≤ E` on `[a, c]`. Then
`|bᵀ f(A) b − (Qᵀb)ᵀ f(QᵀAQ) (Qᵀb)| ≤ 2 E ‖b‖²`.
Source: Golub–Meurant (2010) [`gm10`], §6.2 (error of Gauss quadrature via best approximation);
Chen–Trogdon–Ubaru (2021) [`ctu21`], Lem. 2.2; Ubaru–Chen–Saad (2017) [`ucs17`], proof of Thm 4.1.
Atlas: `lanczos-gauss-quadrature`.
Deviation: stated with an arbitrary approximant `p` (the source takes the best uniform
approximation, `E = E_{2q−1}(f)`); any orthonormal `Q` with `K_q ⊆ range Q`.
atlas: lanczos-gauss-quadrature -/
theorem abs_dotProduct_cfc_mulVec_sub_le_of_krylovSpace_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hq : 0 < q) (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {f : ℝ → ℝ}
    {p : Polynomial ℝ} (hp : p.natDegree ≤ 2 * q - 1) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) :
    |b ⬝ᵥ (cfc f A *ᵥ b) - (Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b))| ≤
      2 * E * (b ⬝ᵥ b) := by
  have hAs : A.IsSymm := by
    rw [IsSymm, ← conjTranspose_eq_transpose_of_trivial]; exact hA
  have hB : (Qᵀ * A * Q).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact isSymm_transpose_mul_mul hAs Q
  have hexact := dotProduct_aeval_mulVec_eq_of_krylovSpace_le hAs hQ b hq hK hp
  have hbmem : b ∈ LinearMap.range Q.mulVecLin :=
    hK (by simpa using pow_mulVec_mem_krylovSpace A b hq)
  have hcc : (Qᵀ *ᵥ b) ⬝ᵥ (Qᵀ *ᵥ b) = b ⬝ᵥ b := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      mulVec_transpose_mulVec_of_mem_range hQ hbmem]
  have h1 := abs_dotProduct_cfc_sub_aeval_le hA (fun i => hfp _ (hspec i)) b
  have h2 := abs_dotProduct_cfc_sub_aeval_le hB
    (fun j => hfp _ (eigenvalues_transpose_mul_mul_mem_Icc hA hQ hB hspec j)) (Qᵀ *ᵥ b)
  rw [hcc] at h2
  have : b ⬝ᵥ (cfc f A *ᵥ b) - (Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b)) =
      (b ⬝ᵥ (cfc f A *ᵥ b) - b ⬝ᵥ (Polynomial.aeval A p *ᵥ b)) -
        ((Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b)) -
          (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b))) := by
    rw [hexact]; ring
  rw [this]
  refine (abs_sub _ _).trans ?_
  linarith

end NLAlib
