/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Slava Naprienko.
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Slava Naprienko, NLAlib contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The multivariate principal-minor expansion

Adapted from Mathlib's `coeff_det_one_add_X_smul_eq_sum_minors`: row
multilinearity retains an individual scalar for every selected row. The
identity holds over any commutative ring and includes the empty determinant.
-/

noncomputable section

namespace Matrix

set_option backward.isDefEq.respectTransparency false

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Expanding `det (I + diag(z) M)` selects a principal minor and the product
of the corresponding row weights. No symmetry or invertibility is required. -/
theorem det_one_add_diagonal_mul (M : Matrix n n R) (z : n → R) :
    (1 + diagonal z * M).det =
      ∑ S : Finset n, (M.submatrix (Subtype.val : S → n) Subtype.val).det * ∏ i ∈ S, z i := by
  classical
  let D := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  rw [add_comm]
  change D ((fun i => (diagonal z * M) i) + fun i => (1 : Matrix n n R) i) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have hrow : S.piecewise (fun i => (diagonal z * M) i)
      (fun i => (1 : Matrix n n R) i) =
      fun i => (if i ∈ S then z i else 1) • S.piecewise M (1 : Matrix n n R) i := by
    funext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hrow, D.map_smul_univ]
  change (∏ i, if i ∈ S then z i else 1) *
    (Matrix.of (S.piecewise M (1 : Matrix n n R))).det = _
  have hd := det_piecewise_one_eq_submatrix_det M S
  change (Matrix.of (S.piecewise M (1 : Matrix n n R))).det = _ at hd
  rw [hd]
  simp only [Finset.prod_ite_mem, Finset.univ_inter, mul_comm]

/-- The sum of all principal minors is `det (I + M)`, including the empty
minor one. This is the row-multilinear normalizer identity. -/
theorem det_one_add_eq_sum_principal_minors (M : Matrix n n R) :
    (1 + M).det =
      ∑ S : Finset n, (M.submatrix (Subtype.val : S → n) Subtype.val).det := by
  simpa only [diagonal_one, one_mul, Finset.prod_const_one, mul_one] using
    det_one_add_diagonal_mul M (fun _ => 1)

end Matrix
