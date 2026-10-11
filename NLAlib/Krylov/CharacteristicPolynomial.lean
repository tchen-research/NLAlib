import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import NLAlib.Krylov.FunctionApprox
import NLAlib.Krylov.Jacobi

/-!
# The characteristic polynomial of a Krylov compression

For any real square matrix `A`, an orthonormal matrix `Q` spanning the Krylov space of
dimension `card k` has a compression whose characteristic polynomial is the unique monic
polynomial of that degree minimising the squared norm of `p(A) b`. The residual is orthogonal
to the Krylov space. No symmetry assumption on `A` is needed.

Source: `open_problems_operator_rederivations.tex`, section "Compression exactness and the
remaining polynomial statement" (`rt:compression`), following equation (rt:power-exact);
Saad (1992), Lemma 3.1
(polynomial exactness).
Atlas: `krylov-polynomial-exactness`.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The compression's characteristic residual has zero coordinates in `Q`.
Source: the manuscript's monic least-residual argument following (rt:power-exact), using
compressed polynomial exactness and Cayley–Hamilton. This allows arbitrary real `A` and any
orthonormal `Q` containing `K_(card k)`.
atlas: krylov-polynomial-exactness (partial) -/
theorem transpose_mulVec_aeval_charpoly_mulVec_eq_zero {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin) :
    Qᵀ *ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0 := by
  rw [transpose_mulVec_aeval_mulVec_eq hQ b hK
    (by rw [Matrix.charpoly_degree_eq_dim]), Matrix.aeval_self_charpoly,
    Matrix.zero_mulVec]

/-- The compression's characteristic residual is orthogonal to its range, hence to the
Krylov space it contains. Source: the manuscript's monic least-residual argument following
(rt:power-exact). No symmetry assumption is used.
atlas: krylov-polynomial-exactness (partial) -/
theorem dotProduct_aeval_charpoly_mulVec_eq_zero_of_mem_range {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin)
    {x : n → ℝ} (hx : x ∈ LinearMap.range Q.mulVecLin) :
    x ⬝ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change (Q *ᵥ y) ⬝ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0
  rw [← dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    transpose_mulVec_aeval_charpoly_mulVec_eq_zero hQ b hK, dotProduct_zero]

/-- A monic competitor of degree `card k` splits orthogonally into the characteristic residual
and a residual of smaller degree. Source: the manuscript's monic least-residual argument
following (rt:power-exact). Squared norms are explicit dot products; `A` is arbitrary real.
atlas: krylov-polynomial-exactness (partial) -/
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
  have hmem := hK ((mem_krylovSpace_iff_degree A b _ _).2 ⟨_, hdeg, rfl⟩)
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

/-- The characteristic polynomial of a Krylov compression minimises `‖p(A)b‖²` among monic
polynomials of its degree. Source: the manuscript's monic least-residual argument following
(rt:power-exact). The containing-space hypothesis suffices for minimality; `A` is arbitrary.
atlas: krylov-polynomial-exactness (partial) -/
theorem dotProduct_aeval_charpoly_mulVec_self_le {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ)
    (hK : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin)
    {p : ℝ[X]} (hp : p.Monic) (hpdeg : p.degree = Fintype.card k) :
    (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
        (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ≤
      (aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) := by
  rw [dotProduct_aeval_mulVec_self_eq_charpoly_add hQ b hK hp hpdeg]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- The compression's characteristic polynomial is the unique monic minimiser below or at
the grade. Equality of squared residual norms forces equality of polynomials.
Source: the manuscript's monic least-residual argument following (rt:power-exact), with
independence of the first `card k` Krylov powers. Generic finite labels and real scalars;
no symmetry hypothesis is required.
atlas: krylov-polynomial-exactness (partial) -/
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

/-- Polynomial exactness and the unique monic least-residual characterisation of the Krylov
compression. The first two identities need only `K_q ⊆ range Q`; minimality and uniqueness
apply when `Q` spans `K_q` and `q` is at most the grade. The characteristic residual is
orthogonal to `K_q`. Source: the manuscript's section `rt:compression`, following
(rt:power-exact); Saad (1992), Lemma 3.1. Deviation: arbitrary
finite column labels, squared dot-product norms, and also `q = 0`; no symmetry assumption.
atlas: krylov-polynomial-exactness -/
theorem aeval_mulVec_eq_and_charpoly_is_unique_minimiser {A : Matrix n n ℝ}
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (b : n → ℝ) {q : ℕ}
    (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin) :
    (∀ p : ℝ[X], p.degree < q →
      Q *ᵥ (aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) = aeval A p *ᵥ b) ∧
    (∀ p : ℝ[X], p.degree ≤ q →
      Qᵀ *ᵥ (aeval A p *ᵥ b) = aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) ∧
    (LinearMap.range Q.mulVecLin = krylovSpace A b q → q ≤ krylovGrade A b →
      (Qᵀ * A * Q).charpoly.Monic ∧ (Qᵀ * A * Q).charpoly.degree = q ∧
      (∀ x ∈ krylovSpace A b q, x ⬝ᵥ (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) = 0) ∧
      ∀ p : ℝ[X], p.Monic → p.degree = q →
        (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
            (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ≤
          (aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) ∧
        ((aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) =
          (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ⬝ᵥ
            (aeval A (Qᵀ * A * Q).charpoly *ᵥ b) ↔ p = (Qᵀ * A * Q).charpoly)) := by
  refine ⟨fun p hp => mulVec_aeval_transpose_mul_mul_mulVec_eq hQ b hK hp,
    fun p hp => transpose_mulVec_aeval_mulVec_eq hQ b hK hp, ?_⟩
  intro hspan hq
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have hh := congrArg (fun z => Qᵀ *ᵥ z) hxy
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec] using hh
  have hcard : Fintype.card k = q := by
    calc Fintype.card k = Module.finrank ℝ (LinearMap.range Q.mulVecLin) := by
          rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
      _ = q := by rw [hspan, finrank_krylovSpace, min_eq_left hq]
  have hK' : krylovSpace A b (Fintype.card k) ≤ LinearMap.range Q.mulVecLin :=
    hcard.symm ▸ hK
  refine ⟨Matrix.charpoly_monic _, (Matrix.charpoly_degree_eq_dim _).trans
    (by exact_mod_cast hcard), fun x hx =>
      dotProduct_aeval_charpoly_mulVec_eq_zero_of_mem_range hQ b hK' (hK hx), ?_⟩
  intro p hp hpdeg
  have hpdeg' : p.degree = Fintype.card k := hpdeg.trans (by exact_mod_cast hcard.symm)
  exact ⟨dotProduct_aeval_charpoly_mulVec_self_le hQ b hK' hp hpdeg',
    dotProduct_aeval_mulVec_self_eq_charpoly_iff hQ b hK' (hcard.symm ▸ hq) hp hpdeg'⟩

end NLAlib
