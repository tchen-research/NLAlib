import NLAlib.Krylov.MatrixFunctions.FunctionApprox
import NLAlib.Krylov.Quadrature.Jacobi
/-!
# The characteristic polynomial of a Krylov compression

For any real square matrix `A` and an orthonormal `Q` whose range contains the Krylov space
`K_{card k}(A, b)`, the characteristic polynomial of the compression `Qᵀ A Q` is the unique monic
polynomial of degree `card k` minimising `‖p(A) b‖²` (below the grade), and its residual
`χ(A) b` is orthogonal to the Krylov space. No symmetry assumption on `A` is needed.

* `transpose_mulVec_aeval_charpoly_mulVec_eq_zero`, `dotProduct_aeval_charpoly_mulVec_eq_zero_of_mem_range`:
  the residual `χ(A) b` is orthogonal to `range Q`;
* `dotProduct_aeval_mulVec_self_eq_charpoly_add`: the Pythagorean split for a monic competitor;
* `dotProduct_aeval_charpoly_mulVec_self_le`: minimality;
* `dotProduct_aeval_mulVec_self_eq_charpoly_iff`: uniqueness below the grade.

Source: Saad (2011) [`saad11`], §6.6 (the Lanczos polynomial as the least-residual monic
polynomial); Saad (1992) [`saad92`], Lemma 3.1 (polynomial exactness); Golub–Meurant (2010)
[`gm10`], Ch. 4. Atlas: `krylov-polynomial-exactness`.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **The characteristic residual has zero coordinates in `Q`**: `Qᵀ χ(A) b = 0` for
`χ = charpoly (QᵀAQ)` when `K_{card k}(A, b) ⊆ range Q` (polynomial exactness and
Cayley–Hamilton). Any real `A`. Source: Saad (2011) [`saad11`], §6.6; Saad (1992) [`saad92`],
Lemma 3.1.
atlas: krylov-polynomial-exactness -/
theorem transpose_mulVec_aeval_charpoly_mulVec_eq_zero {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin) :
    Qᵀ *ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0 := by
  rw [transpose_mulVec_aeval_mulVec_eq hQ b hK
    (by rw [Matrix.charpoly_degree_eq_dim]), Matrix.aeval_self_charpoly,
    Matrix.zero_mulVec]

/-- **The characteristic residual is orthogonal to `range Q`**, hence to the Krylov space it
contains. Any real `A`. Source: Saad (2011) [`saad11`], §6.6.
atlas: krylov-polynomial-exactness -/
theorem dotProduct_aeval_charpoly_mulVec_eq_zero_of_mem_range {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin)
    {x : n → ℝ} (hx : x ∈ LinearMap.range Q.mulVecLin) :
    x ⬝ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change (Q *ᵥ y) ⬝ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0
  rw [← dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    transpose_mulVec_aeval_charpoly_mulVec_eq_zero hQ b hK, dotProduct_zero]

/-- **Pythagorean split of a monic competitor**: for monic `p` of degree `card k`,
`‖p(A) b‖² = ‖χ(A) b‖² + ‖(p − χ)(A) b‖²` with `χ = charpoly (QᵀAQ)`, since `(p − χ)(A) b` lies
in the Krylov space and `χ(A) b` is orthogonal to it. Any real `A`. Source: Saad (2011)
[`saad11`], §6.6.
atlas: krylov-polynomial-exactness -/
theorem dotProduct_aeval_mulVec_self_eq_charpoly_add {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin)
    {p : ℝ[X]} (hp : p.Monic) (hpdeg : p.degree = Fintype.card k) :
    (aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) =
      (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
          (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) +
        (aeval A (p - (Qᵀ * A * Q).charpoly) *ᵥ b) ⬝ᵥ
          (aeval A (p - (Qᵀ * A * Q).charpoly) *ᵥ b) := by
  have hdeg : (p - (Qᵀ * A * Q).charpoly).degree < Fintype.card k := by
    rw [← hpdeg]
    exact degree_sub_lt_left (hpdeg.trans (Matrix.charpoly_degree_eq_dim _).symm)
      hp.ne_zero (hp.leadingCoeff.trans (Matrix.charpoly_monic _).leadingCoeff.symm)
  have hmem := hK ((mem_krylovSpace_iff A b _ _).2 ⟨_, hdeg, rfl⟩)
  have horth := dotProduct_aeval_charpoly_mulVec_eq_zero_of_mem_range hQ b hK hmem
  have hsplit : aeval A p *ᵥ b = aeval A (Qᵀ * A * Q).charpoly *ᵥ b +
      aeval A (p - (Qᵀ * A * Q).charpoly) *ᵥ b := by
    rw [map_sub, Matrix.sub_mulVec]
    abel
  have horth' : (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
      (aeval A (p - (Qᵀ * A * Q).charpoly) *ᵥ b) = 0 :=
    (dotProduct_comm _ _).trans horth
  rw [hsplit, add_dotProduct, dotProduct_add, dotProduct_add, horth, horth']
  ring

/-- **The characteristic polynomial of a Krylov compression minimises `‖p(A) b‖²`** among
monic polynomials of its degree, when `K_{card k}(A, b) ⊆ range Q`. Any real `A`. Source: Saad
(2011) [`saad11`], §6.6 (the Lanczos polynomial as the least-residual monic polynomial).
atlas: krylov-polynomial-exactness -/
theorem dotProduct_aeval_charpoly_mulVec_self_le {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin)
    {p : ℝ[X]} (hp : p.Monic) (hpdeg : p.degree = Fintype.card k) :
    (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
        (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ≤
      (aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) := by
  rw [dotProduct_aeval_mulVec_self_eq_charpoly_add hQ b hK hp hpdeg]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- **Uniqueness of the minimiser below the grade**: for `card k ≤ krylovGrade A b`, a monic `p`
of degree `card k` attains the minimal residual norm iff `p = charpoly (QᵀAQ)`. Any real `A`.
Source: Saad (2011) [`saad11`], §6.6.
atlas: krylov-polynomial-exactness -/
theorem dotProduct_aeval_mulVec_self_eq_charpoly_iff {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin)
    (hq : Fintype.card k ≤ krylovGrade A b)
    {p : ℝ[X]} (hp : p.Monic) (hpdeg : p.degree = Fintype.card k) :
    (aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) =
        (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
          (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ↔ p = (Qᵀ * A * Q).charpoly := by
  constructor
  · intro heq
    have hid := dotProduct_aeval_mulVec_self_eq_charpoly_add hQ b hK hp hpdeg
    have hz : (aeval A (p - (Qᵀ * A * Q).charpoly) *ᵥ b) ⬝ᵥ
        (aeval A (p - (Qᵀ * A * Q).charpoly) *ᵥ b) = 0 := by linarith
    have hdeg : (p - (Qᵀ * A * Q).charpoly).degree < Fintype.card k := by
      rw [← hpdeg]
      exact degree_sub_lt_left (hpdeg.trans (Matrix.charpoly_degree_eq_dim _).symm)
        hp.ne_zero (hp.leadingCoeff.trans (Matrix.charpoly_monic _).leadingCoeff.symm)
    exact sub_eq_zero.1 (eq_zero_of_aeval_mulVec_eq_zero
      (hdeg.trans_le (by exact_mod_cast hq)) (dotProduct_self_eq_zero.1 hz))
  · rintro rfl
    rfl

/-- **The column count of a basis of a Krylov space is its dimension**: if `Q` has orthonormal
columns and `range Q = K_q(A, b)` with `q ≤ krylovGrade A b`, then `card k = q`. Helper for
`krylov-polynomial-exactness`. -/
theorem card_eq_of_range_eq_krylovSpace {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) {b : n → ℝ} {q : ℕ}
    (hspan : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b) :
    Fintype.card k = q := by
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have hh := congrArg (fun z => Qᵀ *ᵥ z) hxy
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec] using hh
  calc Fintype.card k = Module.finrank ℝ (LinearMap.range Q.mulVecLin) := by
        rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
    _ = q := by rw [hspan, finrank_krylovSpace, min_eq_left hq]

end NLAlib
