import NLAlib.Krylov.Jacobi

/-!
# The Jacobi continued fraction

For symmetric `A` and `D : LanczosDecomp A b q`, the `(1,1)` entry of the resolvent of the
Jacobi matrix is the `q`-th convergent of the continued fraction of the Stieltjes transform of
`μ_b`:

* `jacobiMatrix a β m` (symmetric tridiagonal), `jacobiFraction a β x m k` (finite continued
  fraction), `T_eq_jacobiMatrix` (`T_q = jacobiMatrix α β q`);
* `det_smul_one_sub_jacobiMatrix` (three-term determinant recurrence), `inv_apply_zero_zero`
  (Cramer at `(0,0)`), `inv_smul_one_sub_jacobiMatrix_apply_zero_zero` (matrix level);
* `LanczosDecomp.inv_smul_one_sub_T_apply_zero_zero`:
  `e₁ᵀ (x I − T_q)⁻¹ e₁ = 1/(x − α₀ − β₁²/(x − α₁ − ⋯))` for `x` above the spectrum of `A`.

Source: Golub–Meurant (2010) [`gm10`], Ch. 3 (continued fractions) and Thm 4.2; Wall (1948), Ch. XI.
Atlas: `jacobi-matrix-identities`.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric tridiagonal (Jacobi) matrix with diagonal `a 0, …, a (m−1)` and
off-diagonal entries `(i, i+1)`, `(i+1, i)` equal to `β (i+1)`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 3. Atlas: `jacobi-matrix-identities`. -/
def jacobiMatrix (a β : ℕ → ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then a i else if (i : ℕ) + 1 = j then β j
    else if (j : ℕ) + 1 = i then β i else 0

/-- The finite Jacobi (Stieltjes) continued fraction with `m` levels starting at level `k`:
`jacobiFraction a β x 0 k = 0` and
`jacobiFraction a β x (m+1) k = 1 / (x − a k − β (k+1)² · jacobiFraction a β x m (k+1))`, so
`jacobiFraction a β x m 0 = 1/(x − a₀ − β₁²/(x − a₁ − ⋯ − β_{m−1}²/(x − a_{m−1})))`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 3. Atlas: `jacobi-matrix-identities`. -/
def jacobiFraction (a β : ℕ → ℝ) (x : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, k => 1 / (x - a k - β (k + 1) ^ 2 * jacobiFraction a β x m (k + 1))

/-- Shifting the start level of a Jacobi fraction shifts the coefficients. -/
theorem jacobiFraction_succ (a β : ℕ → ℝ) (x : ℝ) (m k : ℕ) :
    jacobiFraction a β x m (k + 1) =
      jacobiFraction (fun i => a (i + 1)) (fun i => β (i + 1)) x m k := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => simp only [jacobiFraction, ih (k + 1)]

/-- The trailing principal submatrix of a Jacobi matrix is the Jacobi matrix of the shifted
coefficients. -/
theorem submatrix_succ_jacobiMatrix (a β : ℕ → ℝ) (m : ℕ) :
    (jacobiMatrix a β (m + 1)).submatrix Fin.succ Fin.succ =
      jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) m := by
  ext i j
  simp only [jacobiMatrix, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Cramer's rule at `(0, 0)`: `(N⁻¹)₀₀ = det N_{[1:],[1:]} / det N` (no hypothesis; both sides
vanish when `N` is singular). -/
theorem inv_apply_zero_zero {m : ℕ} (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    N⁻¹ 0 0 = (N.submatrix Fin.succ Fin.succ).det / N.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, adjugate_fin_succ_eq_det_submatrix, Ring.inverse_eq_inv',
    smul_eq_mul]
  simp [div_eq_inv_mul]

/-- `(x − J)` restricted to the trailing block is `x − J'`. -/
private lemma submatrix_succ_smul_one_sub_jacobiMatrix (a β : ℕ → ℝ) (m : ℕ) (x : ℝ) :
    (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - jacobiMatrix a β (m + 1)).submatrix
        Fin.succ Fin.succ =
      x • (1 : Matrix (Fin m) (Fin m) ℝ) -
        jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) m := by
  rw [← submatrix_succ_jacobiMatrix]
  ext i j
  simp [Matrix.one_apply]

/-- Determinant recurrence of a Jacobi matrix along its first row:
`det(x − J) = (x − a₀) det(x − J') − β₁² det(x − J'')` with `J'`, `J''` the trailing blocks
(shifted coefficients). Source: Golub–Meurant (2010) [`gm10`], Ch. 3. -/
theorem det_smul_one_sub_jacobiMatrix (a β : ℕ → ℝ) (m : ℕ) (x : ℝ) :
    (x • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) - jacobiMatrix a β (m + 2)).det =
      (x - a 0) * (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) -
          jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) (m + 1)).det -
        β 1 ^ 2 * (x • (1 : Matrix (Fin m) (Fin m) ℝ) -
          jacobiMatrix (fun i => a (i + 2)) (fun i => β (i + 2)) m).det := by
  set N := x • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) - jacobiMatrix a β (m + 2)
  have hN : ∀ i j : Fin (m + 2),
      N i j = (if i = j then x else 0) - jacobiMatrix a β (m + 2) i j :=
    fun i j => by simp [N, Matrix.one_apply]
  have hsub1 := submatrix_succ_smul_one_sub_jacobiMatrix a β (m + 1) x
  have hsub2 : N.submatrix (fun k => Fin.succ (Fin.succ k)) (fun k => Fin.succ (Fin.succ k)) =
      x • (1 : Matrix (Fin m) (Fin m) ℝ) -
        jacobiMatrix (fun i => a (i + 2)) (fun i => β (i + 2)) m := by
    rw [← submatrix_succ_smul_one_sub_jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)),
      ← hsub1, Matrix.submatrix_submatrix]
    rfl
  -- the `(0, 1)` minor, expanded along its first column
  have hminor : (N.submatrix Fin.succ (Fin.succ (0 : Fin (m + 1))).succAbove).det =
      N (Fin.succ 0) 0 *
        (N.submatrix (fun k => Fin.succ (Fin.succ k)) fun k => Fin.succ (Fin.succ k)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fintype.sum_eq_zero]
    · simp only [Fin.val_zero, pow_zero, one_mul, add_zero, Matrix.submatrix_apply,
        Matrix.submatrix_submatrix, Fin.succAbove_zero, Fin.succ_succAbove_zero]
      congr 2
    · intro i
      rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero, hN]
      simp [jacobiMatrix, Fin.succ_ne_zero]
  have hzero : ∀ j : Fin m, (-1) ^ ((Fin.succ (Fin.succ j) : Fin (m + 2)) : ℕ) *
      N 0 (Fin.succ (Fin.succ j)) *
        (N.submatrix Fin.succ (Fin.succ (Fin.succ j)).succAbove).det = 0 := by
    intro j
    rw [hN]
    simp only [jacobiMatrix, Matrix.of_apply, Fin.val_zero, Fin.val_succ,
      if_neg (Fin.succ_ne_zero _).symm, show (0 : ℕ) ≠ (j : ℕ) + 1 + 1 by omega,
      show 0 + 1 ≠ (j : ℕ) + 1 + 1 by omega, show (j : ℕ) + 1 + 1 + 1 ≠ 0 by omega, if_false,
      sub_zero, mul_zero, zero_mul]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fintype.sum_eq_zero _ hzero,
    hminor, Fin.succAbove_zero, hsub1, hsub2, hN, hN, hN]
  simp [jacobiMatrix]
  ring

/-- **The `(1,1)` entry of the resolvent of a Jacobi matrix is a continued fraction**: if
`x − J` is positive definite (so every trailing block is nonsingular), then
`((x − J)⁻¹)₀₀ = 1/(x − a₀ − β₁²/(x − a₁ − ⋯ − β_m²/(x − a_m)))`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 3 (continued fractions; label to verify);
Wall (1948), Ch. XI. -/
theorem inv_smul_one_sub_jacobiMatrix_apply_zero_zero (a β : ℕ → ℝ) (m : ℕ) {x : ℝ}
    (hx : (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - jacobiMatrix a β (m + 1)).PosDef) :
    (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - jacobiMatrix a β (m + 1))⁻¹ 0 0 =
      jacobiFraction a β x (m + 1) 0 := by
  induction m generalizing a β with
  | zero =>
    rw [inv_apply_zero_zero, det_fin_one]
    simp [jacobiFraction, jacobiMatrix]
  | succ m ih =>
    have hx' := hx.submatrix (Fin.succ_injective _)
    rw [submatrix_succ_smul_one_sub_jacobiMatrix] at hx'
    have hd1 := hx'.det_pos
    have ih' := ih _ _ hx'
    rw [inv_apply_zero_zero, submatrix_succ_smul_one_sub_jacobiMatrix] at ih'
    rw [inv_apply_zero_zero, submatrix_succ_smul_one_sub_jacobiMatrix,
      det_smul_one_sub_jacobiMatrix, jacobiFraction, jacobiFraction_succ, ← ih']
    have hd1' := hd1.ne'
    field_simp

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- For symmetric `A`, `T_q` is the Jacobi matrix of its recurrence coefficients:
`T_q = jacobiMatrix α β q`. Source: Golub–Meurant (2010) [`gm10`], Thm 4.2.
Atlas: `jacobi-matrix-identities`. -/
theorem T_eq_jacobiMatrix (D : LanczosDecomp A b q) (hA : A.IsSymm) :
    D.T = jacobiMatrix D.alpha D.beta q := by
  have hS : D.T.IsSymm := D.isSymm_T hA
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · rw [alpha, dif_pos i.isLt]
    rw [show j = i from Fin.ext h1.symm]
  · rw [beta, dif_pos ⟨by omega, j.isLt⟩, ← hS.apply]
    congr 1
    exact Fin.ext (by simp; omega)
  · rw [beta, dif_pos ⟨by omega, i.isLt⟩]
    congr 1
    exact Fin.ext (by simp; omega)
  · refine D.T_apply_eq_zero_of_one_lt_dist hA ?_
    rw [lt_abs]
    omega

/-- For `x` above the spectrum of `A`, `x I − T_q` is positive definite. -/
theorem posDef_smul_one_sub_T (D : LanczosDecomp A b q) (hA : A.IsHermitian) {x : ℝ}
    (hx : ∀ i, hA.eigenvalues i < x) :
    (x • (1 : Matrix (Fin q) (Fin q) ℝ) - D.T).PosDef := by
  -- strict Rayleigh bound for `A`
  have hray : ∀ w : n → ℝ, w ≠ 0 → w ⬝ᵥ (A *ᵥ w) < x * (w ⬝ᵥ w) := by
    intro w hw
    have h1 := quadForm_eq_sum_eigenvalues hA w
    have h2 := sum_sq_eigenvectorBasis_dotProduct hA w
    change w ⬝ᵥ (A *ᵥ w) = _ at h1
    rw [h1, ← h2, Finset.mul_sum, ← sub_pos, ← Finset.sum_sub_distrib]
    have hww : 0 < w ⬝ᵥ w :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
        (fun h => hw (dotProduct_self_eq_zero.1 h.symm))
    rw [← h2] at hww
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_nonpos hcon
      linarith
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · nlinarith [hx j, sq_nonneg ((hA.eigenvectorBasis j : n → ℝ) ⬝ᵥ w)]
    · nlinarith [hx i]
  have hQ := D.hasOrthonormalCols
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · change (x • (1 : Matrix (Fin q) (Fin q) ℝ) - D.T)ᴴ = _
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, (D.isHermitian_T hA).eq,
      star_trivial]
  · have hw : D.Q *ᵥ v ≠ 0 := fun h0 => hv (by
      have := congrArg (fun u => D.Qᵀ *ᵥ u) h0
      simpa [Matrix.mulVec_mulVec, show D.Qᵀ * D.Q = 1 from hQ] using this)
    have hvv : v ⬝ᵥ v = (D.Q *ᵥ v) ⬝ᵥ (D.Q *ᵥ v) :=
      (mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ v).symm
    have hvT : v ⬝ᵥ (D.T *ᵥ v) = (D.Q *ᵥ v) ⬝ᵥ (A *ᵥ (D.Q *ᵥ v)) := by
      rw [T, ArnoldiDecomp.H_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hvT, hvv, sub_pos]
    exact hray _ hw

/-- **The resolvent entry is the Jacobi continued fraction**: for symmetric `A`, `q ≥ 1` and
`x` above the spectrum of `A`, `e₁ᵀ (x I − T_q)⁻¹ e₁ = 1/(x − α₀ − β₁²/(x − α₁ − ⋯ −
β_{q−1}²/(x − α_{q−1})))`, the `q`-th convergent of the continued fraction of the Stieltjes
transform `∫ dμ_b(t)/(x − t)` (for `‖b‖ = 1`). Source: Golub–Meurant (2010) [`gm10`], Ch. 3
(continued fractions; label to verify) and Thm 4.2. Deviation: real `x` above the spectrum
(so every trailing block is nonsingular); complex `x` off the real axis is not covered.
atlas: jacobi-matrix-identities (partial) -/
theorem inv_smul_one_sub_T_apply_zero_zero (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    (hq : 0 < q) {x : ℝ} (hx : ∀ i, hA.eigenvalues i < x) :
    (x • (1 : Matrix (Fin q) (Fin q) ℝ) - D.T)⁻¹ ⟨0, hq⟩ ⟨0, hq⟩ =
      jacobiFraction D.alpha D.beta x q 0 := by
  have hAs : A.IsSymm := by
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  have hpd := D.posDef_smul_one_sub_T hA hx
  rw [D.T_eq_jacobiMatrix hAs] at hpd ⊢
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  exact inv_smul_one_sub_jacobiMatrix_apply_zero_zero D.alpha D.beta m hpd

end LanczosDecomp

end NLAlib
