import NLAlib.ForMathlib.LinearAlgebra.Matrix.PrincipalMinorExpansion

/-!
# Sums of principal minors containing a prescribed set

Coefficient extraction from a one-variable determinant identity proves the
inclusion identity used by L-ensemble marginal kernels. This is finite algebra
over a commutative ring, independent of positivity or probability.
-/

noncomputable section

open Polynomial

namespace Matrix

set_option backward.isDefEq.respectTransparency false

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem coeff_prod_one_add_X_indicator (S J : Finset n) :
    ((∏ i ∈ S, if i ∈ J then (1 + X : R[X]) else 1)).coeff J.card =
      if J ⊆ S then 1 else 0 := by
  classical
  have hp : (∏ i ∈ S, if i ∈ J then (1 + X : R[X]) else 1) =
      (1 + X) ^ (S ∩ J).card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
  rw [hp, coeff_one_add_X_pow]
  by_cases h : J ⊆ S
  · simp [h, Finset.inter_eq_right.mpr h]
  · have hlt : (S ∩ J).card < J.card := by
      apply Finset.card_lt_card
      refine lt_of_le_of_ne Finset.inter_subset_right ?_
      intro he
      exact h (Finset.inter_eq_right.mp he)
    simp [h, Nat.choose_eq_zero_of_lt hlt]

/-- The top possible coefficient of `det (I + X M)` is `det M`, including
the empty-dimensional determinant. -/
theorem coeff_det_one_add_X_smul_card (M : Matrix n n R) :
    (det (1 + (X : R[X]) • M.map C)).coeff (Fintype.card n) = M.det := by
  classical
  rw [coeff_det_one_add_X_smul_eq_sum_minors,
    ← Finset.card_univ (α := n), Finset.powersetCard_self, Finset.sum_singleton]
  let e : ↥(Finset.univ : Finset n) ≃ n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact det_submatrix_equiv_self e M

private theorem coeff_det_one_add_diagonal_indicator (K : Matrix n n R) (J : Finset n) :
    (det (1 + diagonal (fun i => if i ∈ J then (X : R[X]) else 0) * K.map C)).coeff J.card =
      (K.submatrix (Subtype.val : J → n) (Subtype.val : J → n)).det := by
  classical
  have hm : 1 + diagonal (fun i => if i ∈ J then (X : R[X]) else 0) * K.map C =
      Matrix.of (J.piecewise (1 + (X : R[X]) • K.map C).row
        (1 : Matrix n n R[X]).row) := by
    ext i j
    simp only [Finset.piecewise, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [hm, det_piecewise_one_eq_submatrix_det]
  have hs : (1 + (X : R[X]) • K.map C).submatrix (Subtype.val : J → n) (Subtype.val : J → n) =
      1 + (X : R[X]) • (K.submatrix (Subtype.val : J → n) (Subtype.val : J → n)).map C := by
    apply Matrix.ext
    intro i j
    change (1 : Matrix n n R[X]) (i : n) (j : n) + X * C (K i j) =
      (1 : Matrix J J R[X]) i j + X * C (K i j)
    simp only [Matrix.one_apply, Subtype.val_inj]
  rw [hs]
  simpa only [Fintype.card_coe] using
    coeff_det_one_add_X_smul_card (K.submatrix (Subtype.val : J → n) (Subtype.val : J → n))

/-- If `K (I + L) = L`, the sum of all principal minors of `L` whose index
set contains `J` is `det (I + L)` times the principal `J` minor of `K`.
For `K = L (I + L)⁻¹` this is the finite L-ensemble inclusion identity. -/
theorem sum_det_principal_minors_superset (L K : Matrix n n R)
    (hK : K * (1 + L) = L) (J : Finset n) :
    (∑ S : Finset n,
      if J ⊆ S then (L.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det else 0) =
      (1 + L).det * (K.submatrix (Subtype.val : J → n) (Subtype.val : J → n)).det := by
  classical
  let Lp : Matrix n n R[X] := L.map C
  let Kp : Matrix n n R[X] := K.map C
  let t : n → R[X] := fun i => if i ∈ J then X else 0
  have hk : Kp * (1 + Lp) = Lp := by
    have h := congrArg (fun M : Matrix n n R => M.map C) hK
    simpa [Lp, Kp, Matrix.map_mul, Matrix.map_add, Matrix.map_one] using h
  have hdiag : diagonal (fun i => 1 + t i) = (1 : Matrix n n R[X]) + diagonal t := by
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  have he : 1 + diagonal (fun i => 1 + t i) * Lp =
      (1 + diagonal t * Kp) * (1 + Lp) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hk,
      hdiag, Matrix.add_mul,
      Matrix.one_mul]
    simp only [add_assoc]
  have hd := congrArg (fun p : R[X] => p.coeff J.card)
    (congrArg Matrix.det he)
  rw [Matrix.det_mul] at hd
  have hc : (1 + Lp).det = C (1 + L).det := by
    have hm : 1 + Lp = (1 + L).map C := by
      simp [Lp, Matrix.map_add, Matrix.map_one]
    rw [hm]
    exact (RingHom.map_det (C : R →+* R[X]) (1 + L)).symm
  rw [hc, Polynomial.coeff_mul_C, coeff_det_one_add_diagonal_indicator] at hd
  rw [det_one_add_diagonal_mul, Polynomial.finsetSum_coeff] at hd
  have ht (i : n) : 1 + t i = if i ∈ J then (1 + X : R[X]) else 1 := by
    simp only [t]
    split_ifs <;> simp
  have hminor (S : Finset n) :
      (Lp.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det =
        C (L.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det := by
    exact (RingHom.map_det (C : R →+* R[X])
      (L.submatrix (Subtype.val : S → n) (Subtype.val : S → n))).symm
  simp only [ht, hminor, Polynomial.coeff_C_mul,
    coeff_prod_one_add_X_indicator] at hd
  simpa only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, mul_comm] using hd

end Matrix
