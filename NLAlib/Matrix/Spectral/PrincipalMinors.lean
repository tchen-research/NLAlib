import NLAlib.Matrix.Functions.PolynomialCalculus

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
commutative ring. Source: the determinant coefficient proof of
manuscript `sa:volume-theorem`; no reality assumption is needed. -/
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
Source: manuscript `sa:volume`, the normalizer identity;
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
