import NLAlib.Krylov.Quadrature.JacobiSpectrum

/-! # Christoffel numbers and Jacobi eigenvectors

Compression of polynomial evaluation identifies the Jacobi eigenvectors with
evaluations of the actual Lanczos orthonormal polynomials. It gives reciprocal
kernel Gauss weights and discrete orthogonality, including finite termination.
Source: Gautschi (2004), Theorem 1.31 and its corollary, Theorem 1.22.
Atlas: `gauss-christoffel-numbers`.
-/

noncomputable section

open Matrix Polynomial
open scoped Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The compressed polynomial vector is the corresponding coordinate vector.
This holds for each actual Lanczos polynomial, without choosing its sign. -/
theorem aeval_poly_T_mulVec_transpose_Q_eq_single (D : LanczosDecomp A b q)
    (j : Fin q) : aeval D.T (D.poly j.val) *ᵥ (D.Qᵀ *ᵥ b) = Pi.single j 1 := by
  have hc := transpose_mulVec_aeval_mulVec_eq D.hasOrthonormalCols b D.range_Q.ge
    (D.degree_poly_le j.val |>.trans (by exact_mod_cast j.isLt.le))
  change D.Qᵀ *ᵥ (aeval A (D.poly j.val) *ᵥ b) =
    aeval D.T (D.poly j.val) *ᵥ (D.Qᵀ *ᵥ b) at hc
  rw [← hc, ← D.vec_eq_aeval_poly, D.vec_of_lt j.isLt]
  funext k
  change D.Q.col k ⬝ᵥ D.Q.col j = (Pi.single j (1 : ℝ) : Fin q → ℝ) k
  rw [D.hasOrthonormalCols.col_dotProduct_col]
  simp [Pi.single_apply, eq_comm]

/-- Each Jacobi eigenvector coordinate is a polynomial evaluation times its first
coordinate and the signed starting-vector normalization. Source: Gautschi
(2004), Theorem 1.31.
atlas: gauss-christoffel-numbers (partial) -/
theorem eigenvectorBasis_T_apply_eq_eval_poly_mul (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (i j : Fin q) :
    (D.isHermitian_T hA).eigenvectorBasis i j =
      (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i) *
        ((D.Qᵀ *ᵥ b) ⟨0, hq⟩ * (D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) := by
  have h := eigenvectorBasis_dotProduct_aeval_mulVec (D.isHermitian_T hA)
    (D.poly j.val) (D.Qᵀ *ᵥ b) i
  rw [D.aeval_poly_T_mulVec_transpose_Q_eq_single, dotProduct_single, mul_one] at h
  have hc : D.Qᵀ *ᵥ b = Pi.single ⟨0, hq⟩ ((D.Qᵀ *ᵥ b) ⟨0, hq⟩) := by
    ext k
    by_cases hk : k = ⟨0, hq⟩
    · subst k
      simp
    · rw [Pi.single_eq_of_ne hk, D.transpose_Q_mulVec_apply_eq_zero]
      have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
      omega
  rw [hc, dotProduct_single] at h
  simpa only [mul_comm _ ((D.Qᵀ *ᵥ b) ⟨0, hq⟩)] using h

private theorem startingCoordinate_ne_zero (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) : (D.Qᵀ *ᵥ b) ⟨0, hq⟩ ≠ 0 := by
  intro hzero
  have h := D.eigenvectorBasis_T_apply_eq_eval_poly_mul hA hq ⟨0, hq⟩ ⟨0, hq⟩
  rw [hzero, zero_mul, mul_zero] at h
  exact D.eigenvectorBasis_T_apply_zero_ne_zero hA hq ⟨0, hq⟩ h

/-- The polynomial-evaluation vector at a Gauss node is an eigenvector of the
Jacobi matrix. It remains valid at finite-support termination, without a
degree-`q` normalized polynomial. Source: Gautschi (2004), Theorem 1.31.
atlas: gauss-christoffel-numbers (partial) -/
theorem T_mulVec_eval_poly_eq_smul (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (i : Fin q) :
    D.T *ᵥ (fun j : Fin q => (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) =
      (D.isHermitian_T hA).eigenvalues i •
        (fun j : Fin q => (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) := by
  let s := (D.Qᵀ *ᵥ b) ⟨0, hq⟩ * (D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩
  have hs : s ≠ 0 := mul_ne_zero (D.startingCoordinate_ne_zero hA hq)
    (D.eigenvectorBasis_T_apply_zero_ne_zero hA hq i)
  have heq : (fun j : Fin q => (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) =
      s⁻¹ • (D.isHermitian_T hA).eigenvectorBasis i := by
    ext j
    rw [Pi.smul_apply, smul_eq_mul, D.eigenvectorBasis_T_apply_eq_eval_poly_mul hA hq]
    change _ = s⁻¹ * (_ * s)
    field_simp
  rw [heq, Matrix.mulVec_smul, (D.isHermitian_T hA).mulVec_eigenvectorBasis,
    smul_smul, smul_smul, mul_comm]

/-- A Jacobi unit eigenvector is the normalized polynomial-evaluation vector,
up to a real sign. The sign accommodates arbitrary orientations of the Lanczos
basis. Source: Gautschi (2004), Theorem 1.31.
atlas: gauss-christoffel-numbers (partial) -/
theorem exists_eigenvectorBasis_T_eq_sign_smul_eval_poly (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (i : Fin q) :
    ∃ ε : ℝ, ε ^ 2 = 1 ∧
      (D.isHermitian_T hA).eigenvectorBasis i =
        (ε / ‖WithLp.toLp 2
          (fun j : Fin q => (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i))‖) •
        (fun j : Fin q => (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) := by
  let v : Fin q → ℝ := fun j => (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)
  let s := (D.Qᵀ *ᵥ b) ⟨0, hq⟩ * (D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩
  have heq : ((D.isHermitian_T hA).eigenvectorBasis i : Fin q → ℝ) = s • v := by
    ext j
    change _ = s * v j
    rw [D.eigenvectorBasis_T_apply_eq_eval_poly_mul hA hq i j]
    exact mul_comm _ s
  have hnorm : ‖WithLp.toLp 2 (s • v)‖ = 1 := by
    rw [← heq, WithLp.toLp_ofLp]
    exact (D.isHermitian_T hA).eigenvectorBasis.orthonormal.1 i
  have hmul : |s| * ‖WithLp.toLp 2 v‖ = 1 := by
    simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] using hnorm
  have hvnorm : ‖WithLp.toLp 2 v‖ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact zero_ne_one hmul
  refine ⟨s * ‖WithLp.toLp 2 v‖, ?_, ?_⟩
  · rw [mul_pow, ← sq_abs s, ← mul_pow, hmul]
    norm_num
  · change _ = ((s * ‖WithLp.toLp 2 v‖) / ‖WithLp.toLp 2 v‖) • v
    rw [mul_div_cancel_right₀ s hvnorm]
    exact heq

/-- The Christoffel kernel has reciprocal equal to the mass-scaled first
eigenvector square. Source: Gautschi (2004), Corollary to Theorem 1.31.
atlas: gauss-christoffel-numbers (partial) -/
theorem mul_sq_eigenvectorBasis_T_apply_zero_eq_inv_sum_sq_eval_poly
    (D : LanczosDecomp A b q) (hA : A.IsHermitian) (hq : 0 < q) (i : Fin q) :
    (b ⬝ᵥ b) * ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 =
      (∑ j : Fin q, ((D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) ^ 2)⁻¹ := by
  have hnorm := eigenvectorBasis_dotProduct_eigenvectorBasis (D.isHermitian_T hA) i i
  simp only [ite_true, dotProduct, ← pow_two] at hnorm
  let S := ∑ j : Fin q, ((D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) ^ 2
  have heq : (∑ j : Fin q, ((D.isHermitian_T hA).eigenvectorBasis i j) ^ 2) =
      S * ((D.Qᵀ *ᵥ b) ⟨0, hq⟩ *
        (D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 := by
    change _ = (∑ j : Fin q,
      ((D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i)) ^ 2) * _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [D.eigenvectorBasis_T_apply_eq_eval_poly_mul hA hq i j, mul_pow]
  rw [heq, mul_pow, D.sq_transpose_Q_mulVec_apply_zero hq] at hnorm
  have hS : S ≠ 0 := by
    intro hz
    change S * _ = 1 at hnorm
    rw [hz, zero_mul] at hnorm
    exact zero_ne_one hnorm
  change _ = S⁻¹
  rw [← one_div]
  apply (eq_div_iff hS).mpr
  change _ * S = 1
  nlinarith [hnorm]

/-- The first `q` actual Lanczos polynomials are orthonormal for the Gauss rule,
with weights for the original spectral measure rather than a probability
normalization. Source: Gautschi (2004), Theorem 1.22.
atlas: gauss-christoffel-numbers (partial) -/
theorem sum_weight_mul_eval_poly_mul_eval_poly (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (j k : Fin q) :
    (∑ i : Fin q, (b ⬝ᵥ b) * ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2 *
      (D.poly j.val).eval ((D.isHermitian_T hA).eigenvalues i) *
      (D.poly k.val).eval ((D.isHermitian_T hA).eigenvalues i)) = if j = k then 1 else 0 := by
  have hU := congrArg (fun M : Matrix (Fin q) (Fin q) ℝ => M j k)
    (Unitary.coe_mul_star_self (D.isHermitian_T hA).eigenvectorUnitary)
  simp only [Unitary.coe_star, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.one_apply] at hU
  rw [← hU]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.eigenvectorBasis_T_apply_eq_eval_poly_mul hA hq i j,
    D.eigenvectorBasis_T_apply_eq_eval_poly_mul hA hq i k,
    ← D.sq_transpose_Q_mulVec_apply_zero hq]
  ring

end LanczosDecomp

end NLAlib
