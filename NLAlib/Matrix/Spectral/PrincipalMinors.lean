import NLAlib.Matrix.Functions.PolynomialCalculus
import NLAlib.Matrix.Basic.OrderedPrincipalMinors

/-!
# Principal minors and elementary spectral sums

The sum of fixed-order principal minors equals the corresponding elementary
sum of eigenvalues, by diagonalization (`G = U diag(d) V` with `VU = 1`, over any commutative
ring; orthogonal and unitary diagonalizations are the instances `V = Uᵀ`, `V = Uᴴ`) and
Mathlib's determinant coefficient identity. This is the normalizer identity of volume sampling.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Similarity preserves the determinant polynomial `det(I+tG)` over any
commutative ring. Source: the determinant coefficient proof of; no reality assumption is needed. -/
theorem det_one_add_X_smul_eq_of_diagonalization {G U V : Matrix ι ι R} {d : ι → R}
    (hVU : V * U = 1) (hG : G = U * Matrix.diagonal d * V) :
    Matrix.det (1 + (X : R[X]) • G.map C) =
      Matrix.det (1 + (X : R[X]) • (Matrix.diagonal d).map C) := by
  let Up : Matrix ι ι R[X] := U.map C
  let Vp : Matrix ι ι R[X] := V.map C
  let Dp : Matrix ι ι R[X] := (Matrix.diagonal d).map C
  have hp : Vp * Up = 1 := by
    have h := congrArg (fun M : Matrix ι ι R => M.map C) hVU
    simpa [Up, Vp, Matrix.map_mul, Matrix.map_one] using h
  have hp' : Up * Vp = 1 := mul_eq_one_comm.1 hp
  have hg : G.map C = Up * Dp * Vp := by
    rw [hG, Matrix.map_mul, Matrix.map_mul]
  have he : 1 + (X : R[X]) • G.map C = Up * (1 + (X : R[X]) • Dp) * Vp := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hp']
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
  have hd : Up.det * Vp.det = 1 := by rw [← Matrix.det_mul, hp', Matrix.det_one]
  rw [he, Matrix.det_mul, Matrix.det_mul]
  dsimp only [Dp]
  calc
    Up.det * (1 + (X : R[X]) • (Matrix.diagonal d).map C).det * Vp.det =
        (Up.det * Vp.det) * (1 + (X : R[X]) • (Matrix.diagonal d).map C).det := by ring
    _ = _ := by rw [hd, one_mul]

/-- The sum of order-`k` principal minors of a diagonalizable matrix `G = U diag(d) V`
(`VU = 1`, any commutative ring) equals the elementary symmetric sum of the diagonal spectrum.
Orthogonal (`V = Uᵀ`) and unitary (`V = Uᴴ`) diagonalizations are instances.
Deshpande--Rademacher--Vempala--Wang (2006), volume-sampling proof. -/
theorem sum_det_principal_minors_eq_sum_prod_of_diagonalization
    {G U V : Matrix ι ι R} {d : ι → R} (hVU : V * U = 1)
    (hG : G = U * Matrix.diagonal d * V) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, (G.submatrix
      (Subtype.val : S → ι) (Subtype.val : S → ι)).det) =
      ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, d i := by
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    det_one_add_X_smul_eq_of_diagonalization hVU hG,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro S _
  have hD : (Matrix.diagonal d).submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) =
      Matrix.diagonal (fun i : S => d i) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply]
  rw [hD, Matrix.det_diagonal]
  exact Finset.prod_coe_sort S d

end NLAlib

namespace NLAlib

open scoped Matrix

/-- The sum of fixed-order Hermitian principal determinants is the elementary
sum of the actual eigenvalues, over either scalar field. The spectral theorem
and the generic determinant-coefficient identity prove the assertion without
a positivity or invertibility assumption. -/
theorem _root_.Matrix.IsHermitian.sum_det_principal_minors_eq_sum_prod
    {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {G : Matrix n n 𝕜} (hG : G.IsHermitian) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, (G.submatrix
      (Subtype.val : S → n) (Subtype.val : S → n)).det) =
      ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, (hG.eigenvalues i : 𝕜) := by
  have hd : G = (hG.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => (hG.eigenvalues i : 𝕜)) *
      star (hG.eigenvectorUnitary : Matrix n n 𝕜) := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using hG.spectral_theorem
  exact NLAlib.sum_det_principal_minors_eq_sum_prod_of_diagonalization
    (Unitary.coe_star_mul_self hG.eigenvectorUnitary) hd k

/-- The sum of real principal determinants along all ordered length-`k`
histories is `k!` times the elementary sum of the sorted Hermitian spectrum.
Zero, repeated, and oversized histories are all included. -/
theorem _root_.Matrix.IsHermitian.sum_re_det_submatrix_eq_factorial_mul_sum_prod_eigenvalues₀
    {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (∑ h : Fin k → n, RCLike.re (A.submatrix h h).det) =
      (k.factorial : ℝ) *
        ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card n))).powersetCard k,
          ∏ i ∈ S, hA.eigenvalues₀ i := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hSort :
      (∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card n))).powersetCard k,
        ∏ i ∈ S, (hA.eigenvalues₀ i : 𝕜)) =
      ∑ S ∈ (Finset.univ : Finset n).powersetCard k, ∏ i ∈ S, (hA.eigenvalues i : 𝕜) := by
    simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
      Finset.sum_powersetCard_prod_equiv e (fun i => (hA.eigenvalues i : 𝕜)) k
  have hm := NLAlib.sum_det_submatrix_eq_factorial_mul_sum_principalMinors A k
  rw [hA.sum_det_principal_minors_eq_sum_prod, ← hSort] at hm
  have hh := congrArg RCLike.re hm
  simpa only [map_sum, RCLike.mul_re, RCLike.natCast_re, RCLike.natCast_im, zero_mul,
    sub_zero, ← RCLike.ofReal_prod, RCLike.ofReal_re] using hh

end NLAlib
