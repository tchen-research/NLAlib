import NLAlib.Matrix.Basic.JacobiBlockMinor
import NLAlib.Matrix.Basic.SchurRank
/-!
# Signed Jacobi inverse-minor identity

Row and column splitting bijections encode equal-sized selected index sets
and their complements. The relative permutation sign is the cofactor sign.
All subminors, including singular, empty and full minors, are covered.
Horn–Johnson 2013, §§0.7.6 and 0.8.4; complementary-nullities.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Two coordinate bijections change a determinant by their relative
permutation sign. This is the cofactor orientation convention for Jacobi's
identity. Horn–Johnson 2013, §0.8.4. -/
theorem det_submatrix_equiv_eq_sign_mul {n r : Type*}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (A : Matrix n n ℝ) (er ec : r ≃ n) :
    (A.submatrix er ec).det =
      (Equiv.Perm.sign (ec.trans er.symm) : ℝ) * A.det := by
  have h : A.submatrix er ec = (A.submatrix er er).submatrix id (ec.trans er.symm) := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.apply_symm_apply, id_eq]
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

/-- Jacobi's full inverse-minor identity for arbitrary ordered finite
coordinates. The first summand gives equal-sized selected row and column
sets; the second gives their complements. The sign is the actual relative
coordinate permutation sign, equal to the usual cofactor parity for the
increasing-coordinate convention. No selected minor is assumed invertible.
Horn–Johnson 2013, §0.8.4.
atlas: complementary-nullities (partial) -/
theorem det_inverse_complement_minor_eq_sign_mul_div {n p q : Type*}
    [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix n n ℝ) (hA : IsUnit A.det) (er ec : (p ⊕ q) ≃ n) :
    (A⁻¹.submatrix (fun i : q => ec (Sum.inr i)) (fun j : q => er (Sum.inr j))).det =
      (Equiv.Perm.sign (ec.trans er.symm) : ℝ) *
        (A.submatrix (fun i : p => er (Sum.inl i)) (fun j : p => ec (Sum.inl j))).det / A.det := by
  let M := A.submatrix er ec
  let J := A⁻¹.submatrix ec er
  have hDet : M.det = (Equiv.Perm.sign (ec.trans er.symm) : ℝ) * A.det :=
    det_submatrix_equiv_eq_sign_mul A er ec
  have hSign : (Equiv.Perm.sign (ec.trans er.symm) : ℝ) ≠ 0 := by
    exact_mod_cast (Units.ne_zero (Equiv.Perm.sign (ec.trans er.symm)))
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (hDet ▸ mul_ne_zero hSign hA.ne_zero)
  have hMJ : M * J = 1 := by
    change A.submatrix er ec * A⁻¹.submatrix ec er = 1
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv A hA,
      Matrix.submatrix_one_equiv]
  have hInv : M⁻¹ = J := by
    calc
      M⁻¹ = M⁻¹ * (M * J) := by rw [hMJ, Matrix.mul_one]
      _ = J := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.one_mul]
  have h := det_inverse_bottomRight_eq_topLeft_div_det M hM
  rw [hInv] at h
  change (A⁻¹.submatrix (fun i : q => ec (Sum.inr i)) (fun j : q => er (Sum.inr j))).det =
    (A.submatrix (fun i : p => er (Sum.inl i)) (fun j : p => ec (Sum.inl j))).det / M.det at h
  rw [h, hDet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ec.trans er.symm)) with hs | hs
  · simp [hs]
  · simp [hs]
    exact (div_neg _).trans (neg_div _ _).symm

universe u v w

/-- The full complementary-nullities bundle: rectangular right nullities,
their explicit column-cardinality rank form, signed Jacobi minors with all
singular/empty/full cases, and Schur rank additivity without symmetry.
Horn–Johnson 2013, §§0.7.5, 0.7.6 and 0.8.4.
atlas: complementary-nullities -/
theorem complementary_nullities_properties {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A.det) :
    (∀ (p q : n → Prop) [DecidablePred p] [DecidablePred q],
      Module.finrank ℝ (LinearMap.ker (A.toBlock p q).mulVecLin) =
        Module.finrank ℝ (LinearMap.ker (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).mulVecLin)) ∧
    (∀ (p q : n → Prop) [DecidablePred p] [DecidablePred q],
      Fintype.card {j // q j} - (A.toBlock p q).rank =
        Fintype.card {j // ¬p j} - (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).rank) ∧
    (∀ (p : Type v) (q : Type w) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
      (er ec : (p ⊕ q) ≃ n),
      (A⁻¹.submatrix (fun i : q => ec (Sum.inr i)) (fun j : q => er (Sum.inr j))).det =
        (Equiv.Perm.sign (ec.trans er.symm) : ℝ) *
          (A.submatrix (fun i : p => er (Sum.inl i)) (fun j : p => ec (Sum.inl j))).det / A.det) ∧
    (∀ (m : Type u) (r : Type v) (l : Type w) [Fintype m] [Fintype r] [Fintype l]
      [DecidableEq m] [DecidableEq r] [DecidableEq l]
      (P : Matrix m m ℝ) (B : Matrix m r ℝ) (C : Matrix l m ℝ) (D : Matrix l r ℝ),
      IsUnit P.det → (Matrix.fromBlocks P B C D).rank = P.rank + (D - C * P⁻¹ * B).rank) :=
  ⟨finrank_ker_toBlock_eq_finrank_ker_inverse_complement A hA,
    card_columns_sub_rank_toBlock_eq_inverse_complement A hA,
    (by intros; exact det_inverse_complement_minor_eq_sign_mul_div A hA _ _),
    (by intros; exact rank_fromBlocks_eq_rank_add_rank_schur _ _ _ _ ‹_›)⟩

end NLAlib
