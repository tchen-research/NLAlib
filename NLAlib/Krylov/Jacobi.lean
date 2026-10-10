import NLAlib.Krylov.Lanczos
import NLAlib.Matrix.CourantFischer

/-!
# Jacobi matrices: orthogonal polynomials, Gauss rules, interlacing, continued fractions

For symmetric `A` and a Lanczos decomposition `D : LanczosDecomp A b q` (`T = Q_qᵀ A Q_q`,
`NLAlib.Krylov.Arnoldi`, `NLAlib.Krylov.Lanczos`), with `μ_b = spectralMeasure hA b`:

* **Lanczos polynomials** `LanczosDecomp.poly j` (`q_j = p_j(A) b`, `deg p_j = j`;
  `exists_col_eq_aeval`, `vec_eq_aeval_poly`, `degree_poly`), orthonormal in `μ_b`
  (`integral_poly_mul_poly`), with the three-term recurrence `X p_j = β_j p_{j−1} + α_j p_j +
  β_{j+1} p_{j+1}` (`X_mul_poly`) and the Christoffel–Darboux identity
  (`sub_mul_sum_eval_poly_mul`).
* **Characteristic polynomial**: `det(x I − T_q)` is monic of degree `q` and orthogonal in `μ_b`
  to all polynomials of degree `< q` (`charpoly_T_monic`, `integral_eval_charpoly_mul_eq_zero`),
  and `χ_j p_0 = β_1 ⋯ β_j p_j` (`charpoly_restrict_T_mul_poly_zero`).
* **Interlacing** of the eigenvalues of `T_{q'}` and `T_q`, `q' ≤ q`
  (`eigenvalues₀_restrict_T_le`, `eigenvalues₀_le_eigenvalues₀_restrict_T`).
* **Gauss nodes and weights** (Golub–Welsch): `e₁ᵀ f(T) e₁ = ∑ᵢ f(θᵢ) (uᵢ)₁²`
  (`cfc_T_apply_zero_zero`, `sum_sq_eigenvectorBasis_T_apply_zero`,
  `dotProduct_cfc_T_mulVec_eq_sum`), exact for `deg p < 2q` (`dotProduct_aeval_mulVec_eq_sum`).

The continued fraction `e₁ᵀ (x I − T_q)⁻¹ e₁` is in `NLAlib.Krylov.JacobiFraction`.

Source: Golub–Meurant (2010) [`gm10`], Ch. 2–4 and 6; Greenbaum (1997) [`greenbaum97`], §2.5;
Saad (2011) [`saad11`], §6.6; Horn–Johnson (2013) [`hj13`], Thm 4.3.17.
Atlas: `lanczos-orthogonal-polynomials`, `jacobi-matrix-identities`; uses
`lanczos-gauss-quadrature`, `cauchy-interlacing`, `spectral-measure`, `krylov-grade`.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix MeasureTheory Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Polynomials below the grade -/

/-- A polynomial of degree below the grade that annihilates `b` is zero: the vectors
`b, A b, …, A^{ν−1} b` are linearly independent. Helper for `krylov-grade` (belongs in
`NLAlib.Krylov.Grade`). -/
theorem eq_zero_of_aeval_mulVec_eq_zero {A : Matrix n n ℝ} {b : n → ℝ} {p : ℝ[X]}
    (hp : p.degree < krylovGrade A b) (h0 : aeval A p *ᵥ b = 0) : p = 0 := by
  set ν := krylovGrade A b
  have hli := (linearIndependent_pow_mulVec_iff_le_krylovGrade A b (q := ν)).2 le_rfl
  have hsum : ∑ i : Fin ν, p.coeff i • ((A ^ (i : ℕ)) *ᵥ b) = 0 := by
    rw [← h0]
    by_cases hp0 : p = 0
    · simp [hp0]
    have hnat : p.natDegree < ν := (natDegree_lt_iff_degree_lt hp0).2 hp
    conv_rhs => rw [p.as_sum_range' ν hnat]
    simp only [map_sum, Matrix.sum_mulVec, ← C_mul_X_pow_eq_monomial, map_mul, aeval_C,
      map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec]
    exact (Fin.sum_univ_eq_sum_range (fun i => p.coeff i • (A ^ i) *ᵥ b) ν)
  have hc := Fintype.linearIndependent_iff.1 hli _ hsum
  ext i
  rw [coeff_zero]
  by_cases hi : i < ν
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast not_lt.1 hi))

/-- For symmetric `A`, `∫ p p' dμ_b = (p(A) b) ⬝ (p'(A) b)`. Helper for `spectral-measure`
(belongs in `NLAlib.Krylov.SpectralMeasure`). -/
theorem integral_eval_mul_eval_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : n → ℝ) (p p' : ℝ[X]) :
    ∫ x, p.eval x * p'.eval x ∂spectralMeasure hA b = (aeval A p *ᵥ b) ⬝ᵥ (aeval A p' *ᵥ b) := by
  have h := integral_eval_spectralMeasure hA b (p * p')
  simp only [eval_mul] at h
  rw [h, map_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    transpose_aeval hA]

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-! ### Lanczos polynomials -/

/-- Each Lanczos vector is a polynomial of exact degree `j` in `A` applied to `b`:
`q_j = p_j(A) b` with `deg p_j = j`. Source: Golub–Meurant (2010) [`gm10`], Thm 4.2 (§4.1).
Atlas: `lanczos-orthogonal-polynomials`. -/
theorem exists_col_eq_aeval (D : LanczosDecomp A b q) (j : Fin q) :
    ∃ p : ℝ[X], p.degree = j ∧ D.Q.col j = aeval A p *ᵥ b := by
  obtain ⟨p, hp, hpj⟩ := (mem_krylovSpace_iff_degree A b _ _).1 (D.graded.col_mem j)
  refine ⟨p, ?_, hpj⟩
  have hnot : ¬ p.degree < j := fun hlt => by
    have h0 := D.graded.col_dotProduct_eq_zero j
      ((mem_krylovSpace_iff_degree A b _ _).2 ⟨p, hlt, hpj⟩)
    rw [D.hasOrthonormalCols.col_dotProduct_col, if_pos rfl] at h0
    exact one_ne_zero h0
  by_cases hp0 : p = 0
  · exact absurd (by rw [hp0, degree_zero]; exact WithBot.bot_lt_coe _) hnot
  have h1 : p.natDegree < (j : ℕ) + 1 := (natDegree_lt_iff_degree_lt hp0).2 hp
  have h2 : ¬ p.natDegree < (j : ℕ) := fun h => hnot ((natDegree_lt_iff_degree_lt hp0).1 h)
  rw [degree_eq_natDegree hp0]
  exact congrArg _ (show p.natDegree = (j : ℕ) by omega)

/-- The **Lanczos polynomial** `p_j` (indexed by `ℕ`, `0` for `j ≥ q`): the polynomial of degree
`j` with `q_j = p_j(A) b` (unique below the grade, `eq_zero_of_aeval_mulVec_eq_zero`).
Source: Golub–Meurant (2010) [`gm10`], §4.1 and Ch. 2. Atlas: `lanczos-orthogonal-polynomials`. -/
def poly (D : LanczosDecomp A b q) (j : ℕ) : ℝ[X] :=
  if h : j < q then Classical.choose (D.exists_col_eq_aeval ⟨j, h⟩) else 0

/-- `deg p_j = j` for `j < q`. Atlas: `lanczos-orthogonal-polynomials`. -/
theorem degree_poly (D : LanczosDecomp A b q) {j : ℕ} (hj : j < q) : (D.poly j).degree = j := by
  rw [poly, dif_pos hj]
  exact (Classical.choose_spec (D.exists_col_eq_aeval ⟨j, hj⟩)).1

/-- `q_j = p_j(A) b` (both sides `0` for `j ≥ q`). Atlas: `lanczos-orthogonal-polynomials`. -/
theorem vec_eq_aeval_poly (D : LanczosDecomp A b q) (j : ℕ) :
    D.vec j = aeval A (D.poly j) *ᵥ b := by
  rw [vec, poly]
  split_ifs with hj
  · exact (Classical.choose_spec (D.exists_col_eq_aeval ⟨j, hj⟩)).2
  · simp

/-- The Lanczos polynomials have degree at most `j` (exactly `j` for `j < q`). -/
theorem degree_poly_le (D : LanczosDecomp A b q) (j : ℕ) : (D.poly j).degree ≤ j := by
  by_cases hj : j < q
  · rw [D.degree_poly hj]
  · rw [poly, dif_neg hj, degree_zero]; exact bot_le

/-- **The Lanczos polynomials are orthonormal for the spectral measure**:
`∫ p_i p_j dμ_b = δ_ij` for `i < q` (and any `j`; `p_j = 0` for `j ≥ q`).
Source: Golub–Meurant (2010) [`gm10`], Thm 4.2 and §2.1; Greenbaum (1997) [`greenbaum97`], §2.5.
atlas: lanczos-orthogonal-polynomials -/
theorem integral_poly_mul_poly (D : LanczosDecomp A b q) (hA : A.IsHermitian) {i j : ℕ}
    (hi : i < q) :
    ∫ x, (D.poly i).eval x * (D.poly j).eval x ∂spectralMeasure hA b =
      if i = j then 1 else 0 := by
  rw [integral_eval_mul_eval_spectralMeasure, ← vec_eq_aeval_poly, ← vec_eq_aeval_poly,
    D.vec_of_lt hi, col_dotProduct_vec]

/-- The Jacobi matrix of a symmetric `A` is Hermitian. Atlas: `lanczos-recurrence`. -/
theorem isHermitian_T (D : LanczosDecomp A b q) (hA : A.IsHermitian) : D.T.IsHermitian :=
  isHermitian_transpose_mul_mul hA D.Q

/-- **Three-term recurrence of the Lanczos polynomials**: for symmetric `A` and `j + 1 < q`,
`X p_j = β_j p_{j−1} + α_j p_j + β_{j+1} p_{j+1}`, so the Jacobi matrix `T` holds the recurrence
coefficients of the orthonormal polynomials of `μ_b`. Source: Golub–Meurant (2010) [`gm10`],
Thm 2.1 and Thm 4.2.
atlas: lanczos-orthogonal-polynomials (partial) -/
theorem X_mul_poly (D : LanczosDecomp A b q) (hA : A.IsSymm) {j : ℕ} (hj : j + 1 < q) :
    X * D.poly j = C (D.beta j) * D.poly (j - 1) + C (D.alpha j) * D.poly j +
      C (D.beta (j + 1)) * D.poly (j + 1) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_aeval_mulVec_eq_zero (A := A) (b := b) ?_ ?_
  · refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      rw [degree_X]
      refine lt_of_le_of_lt (add_le_add le_rfl (D.degree_poly_le j)) ?_
      have : ((1 + j : ℕ) : WithBot ℕ) < krylovGrade A b := by
        exact_mod_cast (show 1 + j < krylovGrade A b by have := D.le_krylovGrade; omega)
      exact_mod_cast this
    · have hd : ∀ (c : ℝ) (k : ℕ), k ≤ j + 1 → (C c * D.poly k).degree < krylovGrade A b :=
        fun c k hk => lt_of_le_of_lt (degree_mul_le _ _) (lt_of_le_of_lt
          (add_le_add degree_C_le (D.degree_poly_le k)) (by
            rw [zero_add]
            exact_mod_cast (show k < krylovGrade A b by have := D.le_krylovGrade; omega)))
      exact lt_of_le_of_lt (degree_add_le _ _) (max_lt (lt_of_le_of_lt (degree_add_le _ _)
        (max_lt (hd _ _ (by omega)) (hd _ _ (by omega)))) (hd _ _ le_rfl))
  · simp only [map_sub, map_add, map_mul, aeval_X, aeval_C, Matrix.sub_mulVec, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← vec_eq_aeval_poly, D.mulVec_vec_eq hA hj,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

/-- **Christoffel–Darboux identity** for the Lanczos polynomials: for symmetric `A` and
`1 ≤ m < q`, `(x − y) ∑_{j<m} p_j(x) p_j(y) = β_m (p_m(x) p_{m−1}(y) − p_{m−1}(x) p_m(y))`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 2 (Christoffel–Darboux formula; label to
verify).
atlas: jacobi-matrix-identities (partial) -/
theorem sub_mul_sum_eval_poly_mul (D : LanczosDecomp A b q) (hA : A.IsSymm) {m : ℕ}
    (hm0 : 0 < m) (hm : m < q) (x y : ℝ) :
    (x - y) * ∑ j ∈ Finset.range m, (D.poly j).eval x * (D.poly j).eval y =
      D.beta m * ((D.poly m).eval x * (D.poly (m - 1)).eval y -
        (D.poly (m - 1)).eval x * (D.poly m).eval y) := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hrec := D.X_mul_poly hA (j := m) (by omega)
    have hx := congrArg (eval x) hrec
    have hy := congrArg (eval y) hrec
    simp only [eval_mul, eval_X, eval_C, eval_add] at hx hy
    rw [Finset.sum_range_succ, mul_add]
    rcases Nat.eq_zero_or_pos m with rfl | hm0'
    · have hb0 : D.beta 0 = 0 := by simp [beta]
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, hb0, zero_mul,
        Nat.sub_self] at hx hy ⊢
      linear_combination (D.poly 0).eval y * hx - (D.poly 0).eval x * hy
    · rw [ih hm0' (by omega)]
      simp only [Nat.add_sub_cancel]
      linear_combination (D.poly m).eval y * hx - (D.poly m).eval x * hy

/-! ### The characteristic polynomial of `T` -/

/-- Projected powers: `Q_qᵀ A^k b = T_q^k Q_qᵀ b` for `k ≤ q`. -/
theorem transpose_Q_mulVec_pow_mulVec (D : LanczosDecomp A b q) {k : ℕ} (hk : k ≤ q) :
    D.Qᵀ *ᵥ ((A ^ k) *ᵥ b) = (D.T ^ k) *ᵥ (D.Qᵀ *ᵥ b) := by
  have hQ := D.hasOrthonormalCols
  have hQQ : D.Qᵀ * D.Q = 1 := hQ
  have hlift : ∀ i, i < q → D.Q *ᵥ ((D.T ^ i) *ᵥ (D.Qᵀ *ᵥ b)) = (A ^ i) *ᵥ b := fun i hi =>
    mulVec_pow_transpose_mul_mul_mulVec_eq hQ b D.range_Q.ge hi
  rcases Nat.lt_or_ge k q with hlt | hge
  · rw [← hlift k hlt, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
  · obtain rfl : k = q := le_antisymm hk hge
    rcases k with _ | k
    · simp
    · rw [pow_succ', ← Matrix.mulVec_mulVec, ← hlift k (by omega), pow_succ',
        ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec_mulVec, ArnoldiDecomp.H_def, Matrix.mul_assoc]

/-- `Q_qᵀ p(A) b = p(T_q) Q_qᵀ b` for `deg p ≤ q`. -/
theorem transpose_Q_mulVec_aeval_mulVec (D : LanczosDecomp A b q) {p : ℝ[X]}
    (hp : p.natDegree ≤ q) : D.Qᵀ *ᵥ (aeval A p *ᵥ b) = aeval D.T p *ᵥ (D.Qᵀ *ᵥ b) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.mulVec_sum,
    Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
    D.transpose_Q_mulVec_pow_mulVec (by have := Finset.mem_range.1 hk; omega)]

/-- **`det(x I − T_q)` is the monic orthogonal polynomial of degree `q`**: for symmetric `A`,
`χ_q = charpoly T_q` (monic of degree `q`, `charpoly_T_monic`, `natDegree_charpoly_T`) is
orthogonal in `μ_b` to every polynomial of degree `< q`. Source: Golub–Meurant (2010)
[`gm10`], Thm 4.2 and §3.1 (`p_q` and `det(λI − J_q)` are proportional).
atlas: lanczos-orthogonal-polynomials (partial) -/
theorem integral_eval_charpoly_mul_eq_zero (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {r : ℝ[X]} (hr : r.degree < q) :
    ∫ x, D.T.charpoly.eval x * r.eval x ∂spectralMeasure hA b = 0 := by
  rw [integral_eval_mul_eval_spectralMeasure]
  -- `r(A) b ∈ K_q = range Q`
  obtain ⟨y, hy⟩ : aeval A r *ᵥ b ∈ LinearMap.range D.Q.mulVecLin := by
    rw [D.range_Q]; exact (mem_krylovSpace_iff_degree A b q _).2 ⟨r, hr, rfl⟩
  rw [← hy, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    D.transpose_Q_mulVec_aeval_mulVec (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]),
    aeval_self_charpoly, Matrix.zero_mulVec, zero_dotProduct]

/-- `charpoly T_q` is monic of degree `q`. Atlas: `lanczos-orthogonal-polynomials`. -/
theorem charpoly_T_monic (D : LanczosDecomp A b q) :
    D.T.charpoly.Monic ∧ D.T.charpoly.natDegree = q :=
  ⟨charpoly_monic _, by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]⟩

/-- Leading coefficients of the Lanczos polynomials: `lead(p_k) = β_{k+1} lead(p_{k+1})`. -/
private lemma leadingCoeff_poly_eq (D : LanczosDecomp A b q) (hA : A.IsSymm) {k : ℕ}
    (hk : k + 1 < q) :
    (D.poly k).leadingCoeff = D.beta (k + 1) * (D.poly (k + 1)).leadingCoeff := by
  have h := congrArg (fun p => coeff p (k + 1)) (D.X_mul_poly hA hk)
  simp only [coeff_add, coeff_C_mul, coeff_X_mul] at h
  have hdk : (D.poly k).natDegree = k := natDegree_eq_of_degree_eq_some (D.degree_poly (by omega))
  have hdk1 : (D.poly (k + 1)).natDegree = k + 1 :=
    natDegree_eq_of_degree_eq_some (D.degree_poly hk)
  have h1 : (D.poly (k - 1)).coeff (k + 1) = 0 :=
    coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (D.degree_poly_le _) (by exact_mod_cast (by omega)))
  have h2 : (D.poly k).coeff (k + 1) = 0 :=
    coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (D.degree_poly_le _) (by exact_mod_cast (by omega)))
  rw [h1, h2, mul_zero, mul_zero, zero_add, zero_add] at h
  rw [leadingCoeff, leadingCoeff, hdk, hdk1, h]

/-- `lead(p_0) = β_1 ⋯ β_j lead(p_j)`. -/
private lemma leadingCoeff_poly_zero_eq (D : LanczosDecomp A b q) (hA : A.IsSymm) {j : ℕ}
    (hj : j < q) :
    (D.poly 0).leadingCoeff = (∏ k ∈ Finset.Icc 1 j, D.beta k) * (D.poly j).leadingCoeff := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega), leadingCoeff_poly_eq D hA hj, Finset.prod_Icc_succ_top (by omega)]
    ring

/-- **`det(x I − T_j)` is proportional to the Lanczos polynomial `p_j`**:
`χ_j p_0 = β_1 ⋯ β_j p_j` with `χ_j = charpoly T_j` (`p_0 = ±1/‖b‖` is a constant; for
`‖b‖ = 1` and the canonical signs this is `det(x I − T_j) = β_1 ⋯ β_j p_j(x)`).
Source: Golub–Meurant (2010) [`gm10`], Ch. 3 and Thm 4.2 (labels to verify).
atlas: lanczos-orthogonal-polynomials -/
theorem charpoly_restrict_T_mul_poly_zero (D : LanczosDecomp A b q) (hA : A.IsSymm) {j : ℕ}
    (hj : j < q) :
    (LanczosDecomp.T (D.restrict hj.le)).charpoly * D.poly 0 =
      C (∏ k ∈ Finset.Icc 1 j, D.beta k) * D.poly j := by
  set D' : LanczosDecomp A b j := D.restrict hj.le
  set χ := (LanczosDecomp.T D').charpoly
  have hχdeg : χ.natDegree = j := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hχ0 : D'.Qᵀ *ᵥ (aeval A χ *ᵥ b) = 0 := by
    rw [D'.transpose_Q_mulVec_aeval_mulVec hχdeg.le, aeval_self_charpoly, Matrix.zero_mulVec]
  have hmem : aeval A χ *ᵥ b ∈ krylovSpace A b (j + 1) := by
    refine (mem_krylovSpace_iff_degree A b _ _).2 ⟨χ, ?_, rfl⟩
    rw [degree_eq_natDegree (charpoly_monic _).ne_zero, hχdeg]
    exact_mod_cast Nat.lt_succ_self j
  -- `χ(A) b = c q_j`
  set c := D.vec j ⬝ᵥ (aeval A χ *ᵥ b)
  have hvec : aeval A χ *ᵥ b = c • D.vec j := by
    refine D.eq_of_forall_col_dotProduct_eq (krylovSpace_mono A b (by omega) hmem)
      (Submodule.smul_mem _ _ (D.vec_mem j)) fun i => ?_
    rw [dotProduct_smul, col_dotProduct_vec, smul_eq_mul]
    rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
    · rw [if_neg hij.ne, mul_zero]
      have := congrFun hχ0 ⟨i, hij⟩
      exact this
    · rw [if_pos hij, mul_one]
      show _ = D.vec j ⬝ᵥ _
      rw [D.vec_of_lt hj]
      exact congrArg (fun k => D.Q.col k ⬝ᵥ _) (Fin.ext hij)
    · rw [if_neg hij.ne', mul_zero]
      exact D.graded.col_dotProduct_eq_zero i (krylovSpace_mono A b (by omega) hmem)
  -- hence `χ = c p_j`
  have hχ : χ = C c * D.poly j := by
    rw [← sub_eq_zero]
    refine eq_zero_of_aeval_mulVec_eq_zero (A := A) (b := b) ?_ ?_
    · refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · rw [degree_eq_natDegree (charpoly_monic _).ne_zero, hχdeg]
        exact_mod_cast (show j < krylovGrade A b by have := D.le_krylovGrade; omega)
      · refine lt_of_le_of_lt (degree_mul_le _ _) (lt_of_le_of_lt
          (add_le_add degree_C_le (D.degree_poly_le j)) ?_)
        rw [zero_add]
        exact_mod_cast (show j < krylovGrade A b by have := D.le_krylovGrade; omega)
    · rw [map_sub, Matrix.sub_mulVec, hvec, map_mul, aeval_C, ← Matrix.mulVec_mulVec,
        ← vec_eq_aeval_poly, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_self]
  -- leading coefficients
  have hlead : c * (D.poly j).leadingCoeff = 1 := by
    have := (charpoly_monic (LanczosDecomp.T D')).leadingCoeff
    rw [show (LanczosDecomp.T D').charpoly = χ from rfl, hχ, leadingCoeff_mul, leadingCoeff_C]
      at this
    exact this
  have hp0 : D.poly 0 = C (D.poly 0).leadingCoeff := by
    have hd : (D.poly 0).natDegree = 0 :=
      natDegree_eq_of_degree_eq_some (D.degree_poly (by omega))
    conv_lhs => rw [eq_C_of_natDegree_eq_zero hd]
    rw [leadingCoeff, hd]
  have hc : c * ((∏ k ∈ Finset.Icc 1 j, D.beta k) * (D.poly j).leadingCoeff) =
      ∏ k ∈ Finset.Icc 1 j, D.beta k := by
    linear_combination (∏ k ∈ Finset.Icc 1 j, D.beta k) * hlead
  rw [hχ, hp0, leadingCoeff_poly_zero_eq D hA hj, mul_right_comm, ← map_mul, hc]

/-! ### Interlacing -/

/-- `T_{q'} = Eᵀ T_q E` with `E` the first `q'` columns of the identity. -/
private lemma restrict_T_eq (D : LanczosDecomp A b q) {q' : ℕ} (h : q' ≤ q) :
    LanczosDecomp.T (D.restrict h) =
      ((1 : Matrix (Fin q) (Fin q) ℝ).submatrix id (Fin.castLE h))ᵀ * D.T *
        (1 : Matrix (Fin q) (Fin q) ℝ).submatrix id (Fin.castLE h) := by
  rw [T, ArnoldiDecomp.H_restrict]
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply]

/-- The first `q'` columns of the identity are orthonormal. -/
private lemma hasOrthonormalCols_submatrix_one {q' : ℕ} (h : q' ≤ q) :
    HasOrthonormalCols ((1 : Matrix (Fin q) (Fin q) ℝ).submatrix id (Fin.castLE h)) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj]

/-- **Cauchy interlacing, upper half**: the eigenvalues of `T_{q'}` (`q' ≤ q`, a leading
principal submatrix of `T_q`) satisfy `θ_i(T_{q'}) ≤ θ_i(T_q)` (eigenvalues in non-increasing
order). Source: Golub–Meurant (2010) [`gm10`], Ch. 3 (interlacing; label to verify);
Horn–Johnson (2013) [`hj13`], Thm 4.3.17. Deviation: non-strict.
atlas: jacobi-matrix-identities (partial) -/
theorem eigenvalues₀_restrict_T_le (D : LanczosDecomp A b q) (hA : A.IsHermitian) {q' : ℕ}
    (h : q' ≤ q) (i : Fin (Fintype.card (Fin q'))) :
    (isHermitian_T (D.restrict h) hA).eigenvalues₀ i ≤
      (D.isHermitian_T hA).eigenvalues₀ (Fin.castLE (by simpa using h) i) := by
  have hE := hasOrthonormalCols_submatrix_one h
  have key := eigenvalues₀_compression_le (D.isHermitian_T hA) hE
    (by rw [← restrict_T_eq]; exact isHermitian_T (D.restrict h) hA) i
  convert key using 2
  rw [restrict_T_eq]

/-- **Cauchy interlacing, lower half**: `θ_{i + (q − q')}(T_q) ≤ θ_i(T_{q'})` for `q' ≤ q`;
with `q' = q − 1` and the upper half, the eigenvalues of `T_{q−1}` interlace those of `T_q`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 3 (label to verify); Horn–Johnson (2013) [`hj13`],
Thm 4.3.17.
Deviation: non-strict.
atlas: jacobi-matrix-identities (partial) -/
theorem eigenvalues₀_le_eigenvalues₀_restrict_T (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {q' : ℕ} (h : q' ≤ q) (i : Fin (Fintype.card (Fin q'))) :
    (D.isHermitian_T hA).eigenvalues₀ ⟨i + (Fintype.card (Fin q) - Fintype.card (Fin q')),
      by have := i.isLt; simp only [Fintype.card_fin] at this ⊢; omega⟩ ≤
      (isHermitian_T (D.restrict h) hA).eigenvalues₀ i := by
  have hE := hasOrthonormalCols_submatrix_one h
  have key := eigenvalues₀_le_eigenvalues₀_compression (D.isHermitian_T hA) hE
    (by rw [← restrict_T_eq]; exact isHermitian_T (D.restrict h) hA) i
  convert key using 2
  rw [restrict_T_eq]

/-! ### Gauss nodes and weights (Golub–Welsch) -/

/-- **Golub–Welsch**: `e₁ᵀ f(T_q) e₁ = ∑ᵢ f(θᵢ) (uᵢ)₁²` with `(θᵢ, uᵢ)` the eigenpairs of
`T_q`: the Gauss rule has the eigenvalues of `T_q` as nodes and the squared first components
of its eigenvectors as weights. Source: Golub–Meurant (2010) [`gm10`], Ch. 6 (Golub–Welsch; label to
verify).
atlas: jacobi-matrix-identities (partial) -/
theorem cfc_T_apply_zero_zero (D : LanczosDecomp A b q) (hA : A.IsHermitian) (hq : 0 < q)
    (f : ℝ → ℝ) :
    cfc f D.T ⟨0, hq⟩ ⟨0, hq⟩ = ∑ i, f ((D.isHermitian_T hA).eigenvalues i) *
      ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 := by
  have h := dotProduct_cfc_mulVec_eq_sum (D.isHermitian_T hA) f (Pi.single ⟨0, hq⟩ 1)
  rw [dotProduct_mulVec_eq_of_apply_eq_zero _ (⟨0, hq⟩ : Fin q)
    fun i hi => Pi.single_eq_of_ne hi _] at h
  simpa only [Pi.single_eq_same, one_pow, one_mul, dotProduct_single, mul_one] using h

/-- The Gauss weights sum to one: `∑ᵢ (uᵢ)₁² = 1`. Source: Golub–Meurant (2010) [`gm10`],
Thm 6.6. Atlas: `jacobi-matrix-identities`. -/
theorem sum_sq_eigenvectorBasis_T_apply_zero (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    (hq : 0 < q) : ∑ i, ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 = 1 := by
  have h := sum_sq_eigenvectorBasis_dotProduct (D.isHermitian_T hA) (Pi.single ⟨0, hq⟩ 1)
  simpa [dotProduct_single] using h

/-- **The Lanczos quadrature value is a Gauss rule**: `(Q_qᵀ b)ᵀ f(T_q) (Q_qᵀ b) =
‖b‖² ∑ᵢ f(θᵢ) (uᵢ)₁²` for every `f`. Source: Golub–Meurant (2010) [`gm10`], Thm 6.6 and §7.1;
Ubaru–Chen–Saad (2017) [`ucs17`], §3.
atlas: jacobi-matrix-identities (partial), lanczos-gauss-quadrature (partial) -/
theorem dotProduct_cfc_T_mulVec_eq_sum (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    (hq : 0 < q) (f : ℝ → ℝ) :
    (D.Qᵀ *ᵥ b) ⬝ᵥ (cfc f D.T *ᵥ (D.Qᵀ *ᵥ b)) = (b ⬝ᵥ b) * ∑ i,
      f ((D.isHermitian_T hA).eigenvalues i) *
        ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 := by
  rw [dotProduct_mulVec_eq_of_apply_eq_zero _ (⟨0, hq⟩ : Fin q) fun i hi =>
      D.transpose_Q_mulVec_apply_eq_zero (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)),
    D.sq_transpose_Q_mulVec_apply_zero hq, cfc_T_apply_zero_zero D hA hq]

/-- **Gauss quadrature through the Jacobi matrix**: for symmetric `A`, `q ≥ 1` and
`deg p < 2q`, `bᵀ p(A) b = ‖b‖² ∑ᵢ p(θᵢ) (uᵢ)₁²` with nodes `θᵢ` the eigenvalues of `T_q` and
weights the squared first eigenvector components. Source: Golub–Meurant (2010) [`gm10`],
Thm 6.6; Chen–Trogdon–Ubaru (2021) [`ctu21`], Thm 2.1.
atlas: lanczos-gauss-quadrature, jacobi-matrix-identities (partial) -/
theorem dotProduct_aeval_mulVec_eq_sum (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    (hq : 0 < q) {p : ℝ[X]} (hp : p.degree < 2 * q) :
    b ⬝ᵥ (aeval A p *ᵥ b) = (b ⬝ᵥ b) * ∑ i,
      p.eval ((D.isHermitian_T hA).eigenvalues i) *
        ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 := by
  have hAs : A.IsSymm := by
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  rw [D.dotProduct_aeval_mulVec_eq hAs hq hp,
    ← cfc_polynomial p D.T (D.isHermitian_T hA).isSelfAdjoint, cfc_T_apply_zero_zero D hA hq]

end LanczosDecomp

end NLAlib
