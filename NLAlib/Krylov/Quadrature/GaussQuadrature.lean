import NLAlib.Krylov.Spaces.Polynomial
import NLAlib.Krylov.Quadrature.SpectralMeasure
import NLAlib.Matrix.Subspaces.Projections
/-!
# Gauss (Lanczos) quadrature: exactness and error

Let `A` be symmetric, `b` a vector and `Q` a matrix with orthonormal columns whose range contains
the Krylov space `K_q(A, b)`. With the projected matrix `B = Qᵀ A Q` and `c = Qᵀ b`, the
"Lanczos quadrature" `cᵀ p(B) c` reproduces `bᵀ p(A) b` exactly for every polynomial of degree
`< 2q`. This is the exactness of the `q`-node Gauss quadrature rule for the spectral
measure `μ_b` (`NLAlib.spectralMeasure`): when `Q` is the Lanczos basis, `B` is the Jacobi matrix
`T_q` and `c = ‖b‖ e₁`.

## Main results

* `NLAlib.dotProduct_aeval_mulVec_eq_of_degree_lt_two_mul`: exactness for `deg p < 2q` (any
  `q`, no `natDegree` form).
* `NLAlib.transpose_mulVec_pow_mulVec_eq`, `NLAlib.transpose_mulVec_aeval_mulVec_eq`:
  compression commutes with polynomials of degree `≤ q`, `Qᵀ p(A) b = p(QᵀAQ) Qᵀ b`.
* `NLAlib.eigenvalues_transpose_mul_mul_mem_Icc`: the eigenvalues of `Qᵀ A Q` stay in any
  interval containing those of `A`.
* `NLAlib.abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul`: the quadrature error
  `|bᵀ f(A) b − cᵀ f(B) c| ≤ 2 E ‖b‖²` when `|f − p| ≤ E` on an interval containing the spectrum
  of `A`, for some `p` of degree `< 2q`.

Source: Golub–Meurant (2010) [`gm10`], Ch. 6–7 (Thm 6.6 exactness of Gauss quadrature);
Chen–Trogdon–Ubaru (2021) [`ctu21`], Thm 2.1; Saad (1992) [`saad92`], Lemma 3.1 (compression).
Atlas: `lanczos-gauss-quadrature`, `krylov-polynomial-exactness` (partial).
Deviation from the printed statements: any orthonormal `Q` with `K_q(A,b) ⊆ range Q` is
allowed, so neither tridiagonality nor the Lanczos recurrence is used.

The projection helpers `mulVec_conjTranspose_mulVec_of_mem_range` and `isSymm_transpose_mul_mul`
live in `NLAlib.Matrix.Subspaces.Projections`; the Rayleigh bounds and the eigen-expansion of
`cfc` used below live in `NLAlib.Matrix.Functions.CFCQuadratic`. The compression fact
`eigenvalues_transpose_mul_mul_mem_Icc` is a Matrix-level statement kept here until it lands in
`NLAlib.Matrix.Basic.QuadForm` (F4 request to M2).
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- For a symmetric `M`, `v ⬝ (Mⁱ N) v = (Mⁱ v) ⬝ (N v)`. -/
private lemma dotProduct_pow_mul_mulVec {M : Matrix n n ℝ} (hM : M.IsSymm)
    (N : Matrix n n ℝ) (i : ℕ) (v : n → ℝ) :
    v ⬝ᵥ ((M ^ i * N) *ᵥ v) = (M ^ i *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    (hM.pow i).eq]

/-- Lifting the projected powers: if `K_q(A,b) ⊆ range Q` then `Q (QᵀAQ)ʲ Qᵀ b = Aʲ b` for
`j < q`. Atlas: `lanczos-gauss-quadrature` (helper). -/
theorem mulVec_pow_transpose_mul_mul_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {j : ℕ} (hj : j < q) :
    Q *ᵥ ((Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b)) = A ^ j *ᵥ b := by
  induction j with
  | zero =>
    simpa using mulVec_conjTranspose_mulVec_of_mem_range hQ
      (hK (by simpa using pow_mulVec_mem_krylovSpace A b hj))
  | succ j ih =>
    have ih := ih (Nat.lt_of_succ_lt hj)
    have hstep : (Qᵀ * A * Q) ^ (j + 1) *ᵥ (Qᵀ *ᵥ b) = Qᵀ *ᵥ (A ^ (j + 1) *ᵥ b) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        show A *ᵥ (A ^ j *ᵥ b) = A ^ (j + 1) *ᵥ b by rw [Matrix.mulVec_mulVec, ← pow_succ']]
    rw [hstep]
    exact mulVec_conjTranspose_mulVec_of_mem_range hQ (hK (pow_mulVec_mem_krylovSpace A b hj))

/-- Compressed powers act like powers on `Qᵀ b` up to degree `q`: if `K_q(A,b) ⊆ range Q` and
`j ≤ q` then `Qᵀ Aʲ b = (QᵀAQ)ʲ Qᵀ b`. Source: Saad (1992) [`saad92`], Lemma 3.1.
Atlas: `krylov-polynomial-exactness` (helper). -/
theorem transpose_mulVec_pow_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {j : ℕ} (hj : j ≤ q) :
    Qᵀ *ᵥ (A ^ j *ᵥ b) = (Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmem := hK (pow_mulVec_mem_krylovSpace A b (show j < q by omega))
    calc Qᵀ *ᵥ (A ^ (j + 1) *ᵥ b) = Qᵀ *ᵥ (A *ᵥ (A ^ j *ᵥ b)) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec]
      _ = Qᵀ *ᵥ (A *ᵥ (Q *ᵥ (Qᵀ *ᵥ (A ^ j *ᵥ b)))) := by
          rw [← Matrix.conjTranspose_eq_transpose_of_trivial Q,
            mulVec_conjTranspose_mulVec_of_mem_range hQ hmem]
      _ = (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ (A ^ j *ᵥ b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (Qᵀ * A * Q) *ᵥ ((Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b)) := by rw [ih (by omega)]
      _ = (Qᵀ * A * Q) ^ (j + 1) *ᵥ (Qᵀ *ᵥ b) := by rw [Matrix.mulVec_mulVec, ← pow_succ']

open Polynomial in
/-- **Compression commutes with polynomials of degree `≤ q`.** If `Q` has orthonormal columns
and `K_q(A,b) ⊆ range Q`, then `Qᵀ p(A) b = p(QᵀAQ) Qᵀ b` for every `p` with `deg p ≤ q`, for
any square `A`. Source: Saad (1992) [`saad92`], Lemma 3.1.
atlas: krylov-polynomial-exactness (partial) -/
theorem transpose_mulVec_aeval_mulVec_eq {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {p : ℝ[X]} (hp : p.degree ≤ q) :
    Qᵀ *ᵥ (aeval A p *ᵥ b) = aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hnat : p.natDegree ≤ q := (natDegree_le_iff_degree_le).2 hp
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.sum_mulVec,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
    transpose_mulVec_pow_mulVec_eq hQ b hK
      ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)).trans hnat)]

/-- A real Hermitian matrix is symmetric. -/
private lemma isSymm_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) : A.IsSymm := by
  rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA

/-- Exactness on monomials `X^m`, `m < 2q`. -/
private lemma dotProduct_pow_mulVec_eq {A : Matrix n n ℝ} (hA' : A.IsHermitian) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {m : ℕ} (hm : m < 2 * q) :
    b ⬝ᵥ (A ^ m *ᵥ b) = (Qᵀ *ᵥ b) ⬝ᵥ ((Qᵀ * A * Q) ^ m *ᵥ (Qᵀ *ᵥ b)) := by
  have hA : A.IsSymm := isSymm_of_isHermitian hA'
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

/-- **Gauss (Lanczos) quadrature is exact for degree `< 2q`.** If `A` is symmetric, `Q` has
orthonormal columns and `K_q(A,b) ⊆ range Q`, then for every polynomial `p` with
`deg p < 2q`, `bᵀ p(A) b = (Qᵀb)ᵀ p(QᵀAQ) (Qᵀb)`. Valid for every `q` (at `q = 0`, `p = 0`).
Source: Golub–Meurant (2010) [`gm10`], Thm 6.6 and §7.1; Chen–Trogdon–Ubaru (2021) [`ctu21`],
Thm 2.1.
Deviation: any orthonormal `Q` whose range contains `K_q(A,b)`; with the Lanczos basis,
`Qᵀb = ‖b‖e₁` and the right side is `‖b‖² (p(T_q))₁₁`.
atlas: lanczos-gauss-quadrature -/
theorem dotProduct_aeval_mulVec_eq_of_degree_lt_two_mul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {p : Polynomial ℝ}
    (hp : p.degree < 2 * q) :
    b ⬝ᵥ (Polynomial.aeval A p *ᵥ b) =
      (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hnat : p.natDegree < 2 * q := by
    have := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 (by exact_mod_cast hp)
    exact this
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec,
    Matrix.sum_mulVec, dotProduct_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
    dotProduct_pow_mulVec_eq hA hQ b hK
      (lt_of_le_of_lt (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) hnat)]

/-! ### Rayleigh bounds and the quadrature error -/

/-- The eigenvalues of the compression `Qᵀ A Q` (`Q` with orthonormal columns) lie in any
interval `[a, c]` containing the eigenvalues of `A` (the Ritz values stay inside the spectral
interval). Source: Golub–Meurant (2010) [`gm10`], Ch. 4; Parlett (1998), Thm 10.1.1 (weak form).
Atlas: `lanczos-gauss-quadrature` (helper; Matrix-level, to move to `Matrix/Basic/QuadForm`). -/
theorem eigenvalues_transpose_mul_mul_mem_Icc {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) {a c : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c) (j : k) :
    (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ∈ Set.Icc a c := by
  have hB : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  change hB.eigenvalues j ∈ Set.Icc a c
  have hw : (hB.eigenvectorBasis j : k → ℝ) ⬝ᵥ (hB.eigenvectorBasis j : k → ℝ) = 1 := by
    simpa using eigenvectorBasis_dotProduct_eigenvectorBasis hB j j
  have hval := eigenvalues_eq_dotProduct_mulVec hB j
  generalize (hB.eigenvectorBasis j : k → ℝ) = w at hw hval
  have hQw : (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) = 1 := by
    have h := star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ w
    simp only [star_trivial] at h
    rw [h, hw]
  have hval' : hB.eigenvalues j = (Q *ᵥ w) ⬝ᵥ (A *ᵥ (Q *ᵥ w)) := by
    rw [hval]
    change w ⬝ᵥ ((Qᵀ * A * Q) *ᵥ w) = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec w Qᵀ, Matrix.vecMul_transpose]
  have h1 := mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues hA (fun i => (hspec i).1)
    (Q *ᵥ w)
  have h2 := dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues hA (fun i => (hspec i).2)
    (Q *ᵥ w)
  rw [hQw, mul_one] at h1 h2
  exact ⟨hval' ▸ h1, hval' ▸ h2⟩

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
with orthonormal columns, `K_q(A,b) ⊆ range Q`, and `p` a polynomial of degree `< 2q` with
`|f − p| ≤ E` on `[a, c]`. Then `|bᵀ f(A) b − (Qᵀb)ᵀ f(QᵀAQ) (Qᵀb)| ≤ 2 E ‖b‖²`. Valid for
every `q`.
Source: Golub–Meurant (2010) [`gm10`], §6.2 (error of Gauss quadrature via best approximation);
Chen–Trogdon–Ubaru (2021) [`ctu21`], Lem. 2.2; Ubaru–Chen–Saad (2017) [`ucs17`], proof of Thm 4.1.
Deviation: stated with an arbitrary approximant `p` (the source takes the best uniform
approximation, `E = E_{2q−1}(f)`); any orthonormal `Q` with `K_q ⊆ range Q`.
atlas: lanczos-gauss-quadrature -/
theorem abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) {f : ℝ → ℝ}
    {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) :
    |b ⬝ᵥ (cfc f A *ᵥ b) - (Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b))| ≤
      2 * E * ‖WithLp.toLp 2 b‖ ^ 2 := by
  rw [norm_toLp_sq_eq_dotProduct_self]
  have hB : (Qᵀ * A * Q).IsHermitian := (Matrix.isHermitian_conjTranspose_mul_mul Q hA)
  have hexact := dotProduct_aeval_mulVec_eq_of_degree_lt_two_mul hA hQ b hK hp
  have h1 := abs_dotProduct_cfc_sub_aeval_le hA (fun i => hfp _ (hspec i)) b
  have h2 := abs_dotProduct_cfc_sub_aeval_le hB
    (fun j => hfp _ (eigenvalues_transpose_mul_mul_mem_Icc hA hQ hspec j)) (Qᵀ *ᵥ b)
  have hcc : (Qᵀ *ᵥ b) ⬝ᵥ (Qᵀ *ᵥ b) ≤ b ⬝ᵥ b := by
    have h := sum_norm_sq_conjTranspose_mulVec_le hQ b
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs, sq_abs] at h
    simpa only [dotProduct, ← sq] using h
  have h2' : |(Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b)) -
      (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b))| ≤ E * (b ⬝ᵥ b) := by
    rcases le_or_gt 0 E with hE0 | hE0
    · exact h2.trans (mul_le_mul_of_nonneg_left hcc hE0)
    · have hbb0 : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hbb : b ⬝ᵥ b = 0 :=
        le_antisymm (by nlinarith [(abs_nonneg _).trans h1]) hbb0
      obtain rfl : b = 0 := dotProduct_self_eq_zero.1 hbb
      simp
  have : b ⬝ᵥ (cfc f A *ᵥ b) - (Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b)) =
      (b ⬝ᵥ (cfc f A *ᵥ b) - b ⬝ᵥ (Polynomial.aeval A p *ᵥ b)) -
        ((Qᵀ *ᵥ b) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b)) -
          (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b))) := by
    rw [hexact]; ring
  rw [this]
  refine (abs_sub _ _).trans ?_
  linarith

end NLAlib
