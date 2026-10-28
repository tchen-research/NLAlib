import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationAuxiliarySystem

/-!
# The source root/Cauchy determinant below the denominator degree

The `m-n` auxiliary power columns have zero polynomial-row entries. The source
determinant has a proved nonzero normalization and represents `u πhat_n`.
The first-row version puts the leading original polynomial first; moving it to
the end changes only the scalar normalization. No modification root is required
to be real.
Source: Gautschi (2004), Theorem 2.53.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m n : ℕ}

private theorem auxiliary_border_fst_sum {ι : Type*} [Fintype ι] (f : ι → 𝕜[X] × 𝕜[X]) :
    (∑ j, f j).1 = ∑ j, (f j).1 := map_sum (LinearMap.fst 𝕜 𝕜[X] 𝕜[X]) _ _

private theorem auxiliary_border_snd_sum {ι : Type*} [Fintype ι] (f : ι → 𝕜[X] × 𝕜[X]) :
    (∑ j, f j).2 = ∑ j, (f j).2 := map_sum (LinearMap.snd 𝕜 𝕜[X] 𝕜[X]) _ _

/-- The source leading column for the small-order root/Cauchy determinant. -/
def rationalModificationAuxiliaryLeadingConstraints (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (hm : n ≤ m) :
    RationalModificationAuxiliaryIndex l m n → 𝕜 :=
  fun i => rationalModificationAuxiliaryRow T x z
    (rationalModificationAuxiliaryRowEquiv hm i) (monicOrthogonalPolynomial L (l+n),0)

/-- Source bordered matrix in a last-row convention. The polynomial row is
zero on auxiliary columns and is `π_0,...,π_(l+n)` on its remaining columns. -/
def rationalModificationAuxiliaryBorderMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (hm : n ≤ m) :
    Matrix (RationalModificationAuxiliaryIndex l m n ⊕ Fin 1)
      (RationalModificationAuxiliaryIndex l m n ⊕ Fin 1) 𝕜[X] :=
  fromBlocks ((rationalModificationAuxiliaryMatrix L T x z hm).map C)
    (fun i _ => C (rationalModificationAuxiliaryLeadingConstraints L T x z hm i))
    (fun _ j => (rationalModificationAuxiliaryColumn L j).1)
    (fun _ _ => monicOrthogonalPolynomial L (l+n))

set_option maxHeartbeats 1000000 in
private theorem auxiliary_border_det_eq (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (hm : n ≤ m)
    (hd : (rationalModificationAuxiliaryMatrix L T x z hm).det ≠ 0) :
    (rationalModificationAuxiliaryBorderMatrix L T x z hm).det =
      C (rationalModificationAuxiliaryMatrix L T x z hm).det *
        (monicOrthogonalPolynomial L (l+n) -
          ∑ j : RationalModificationAuxiliaryIndex l m n,
            C (((rationalModificationAuxiliaryMatrix L T x z hm)⁻¹ *ᵥ
              rationalModificationAuxiliaryLeadingConstraints L T x z hm) j) *
                (rationalModificationAuxiliaryColumn L j).1) := by
  let M := rationalModificationAuxiliaryMatrix L T x z hm
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
  let : Invertible (M.map C) :=
    { invOf := (M⁻¹).map C
      invOf_mul_self := by rw [← Matrix.map_mul, M.nonsing_inv_mul hu]; simp
      mul_invOf_self := by rw [← Matrix.map_mul, M.mul_nonsing_inv hu]; simp }
  rw [rationalModificationAuxiliaryBorderMatrix,det_fromBlocks₁₁,
    det_eq_elem_of_subsingleton _ (0 : Fin 1)]
  rw [show (M.map C).det = C M.det from (RingHom.map_det C M).symm]
  congr 1
  change monicOrthogonalPolynomial L (l+n) -
      ∑ j, (∑ i, (rationalModificationAuxiliaryColumn L i).1*C (M⁻¹ i j))*
        C (rationalModificationAuxiliaryLeadingConstraints L T x z hm j) =
    monicOrthogonalPolynomial L (l+n) -
      ∑ i, C (∑ j, M⁻¹ i j*rationalModificationAuxiliaryLeadingConstraints L T x z hm j)*
        (rationalModificationAuxiliaryColumn L i).1
  simp only [map_sum,map_mul,sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The source auxiliary-power determinant is its actual nonzero normalization
times `u πhat_n`, including all orders below the divisor degree.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationAuxiliaryBorderMatrix_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z) (hm : n ≤ m)
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0) :
    (rationalModificationAuxiliaryBorderMatrix L T x z hm).det =
      C (rationalModificationAuxiliaryMatrix L T x z hm).det * Lagrange.nodal Finset.univ x *
        monicOrthogonalPolynomial (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n := by
  let M := rationalModificationAuxiliaryMatrix L T x z hm
  let b := rationalModificationAuxiliaryLeadingConstraints L T x z hm
  let c := M⁻¹ *ᵥ b
  let low : 𝕜[X] := ∑ j, C (c j)*(rationalModificationAuxiliaryColumn L j).1
  let P := monicOrthogonalPolynomial L (l+n)-low
  let A : 𝕜[X] := -(∑ j, C (c j)*(rationalModificationAuxiliaryColumn L j).2)
  let u := Lagrange.nodal Finset.univ x
  let π := monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n
  have hd := det_rationalModificationAuxiliaryMatrix_ne_zero L T x z hx hz hm hn
  have hMc : M *ᵥ c = b := by
    dsimp only [c]
    rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),one_mulVec]
  have hlow : low.degree < (l+n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    rw [C_mul']
    apply (degree_smul_le _ _).trans_lt
    cases j with
    | inl j => simp [rationalModificationAuxiliaryColumn]
    | inr j =>
      simp only [rationalModificationAuxiliaryColumn,Sum.elim_inr]
      rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
        natDegree_monicOrthogonalPolynomial]
      exact_mod_cast j.isLt
  have hA : A.degree < (m-n : ℕ) := by
    dsimp only [A]
    rw [degree_neg]
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    rw [C_mul']
    apply (degree_smul_le _ _).trans_lt
    cases j with
    | inl j =>
      simp only [rationalModificationAuxiliaryColumn,Sum.elim_inl,degree_X_pow]
      exact_mod_cast j.isLt
    | inr j => simp [rationalModificationAuxiliaryColumn]
  have hs : (P,A) = (monicOrthogonalPolynomial L (l+n),0) -
      ∑ j, c j • rationalModificationAuxiliaryColumn L j := by
    apply Prod.ext <;> simp [P,A,low,C_mul',auxiliary_border_fst_sum,auxiliary_border_snd_sum]
  have hrows (i : Fin (l+m)) : rationalModificationAuxiliaryRow T x z i (P,A) = 0 := by
    rw [hs,map_sub,map_sum]
    simp only [map_smul,smul_eq_mul]
    have hi := congrFun hMc ((rationalModificationAuxiliaryRowEquiv hm).symm i)
    have he : (∑ j, c j*rationalModificationAuxiliaryRow T x z i
        (rationalModificationAuxiliaryColumn L j)) =
        rationalModificationAuxiliaryRow T x z i (monicOrthogonalPolynomial L (l+n),0) := by
      simpa only [M,b,rationalModificationAuxiliaryMatrix,
        rationalModificationAuxiliaryLeadingConstraints,Matrix.mulVec,dotProduct,
        Equiv.apply_symm_apply,mul_comm] using hi
    rw [he,sub_self]
  have hfull := rationalModificationConstraint_of_auxiliary_rows T x z hx hz hm P A hA hrows
  have htop : (monicOrthogonalPolynomial L (l+n)).degree = (l+n : ℕ) := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hPmonic : P.Monic := (monic_monicOrthogonalPolynomial L _).sub_of_left
    (hlow.trans_eq htop.symm)
  have hPdeg : P.degree = (l+n : ℕ) :=
    (degree_sub_eq_left_of_degree_lt (hlow.trans_eq htop.symm)).trans htop
  have hπ := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (polynomialWeightedFunctional T u) hn
  have hπm : π.Monic := hπ.monic
  have hu : u.Monic := Lagrange.nodal_monic
  have hUdeg : (u*π).degree = (l+n : ℕ) := by
    rw [degree_mul,degree_eq_natDegree hu.ne_zero,degree_eq_natDegree hπ.monic.ne_zero,
      hπ.natDegree_eq]
    simp only [u,Lagrange.natDegree_nodal,card_univ,Fintype.card_fin,Nat.cast_add]
  have hdiff : (P-u*π).degree < (l+n : ℕ) := by
    apply (degree_sub_lt_left (hPdeg.trans hUdeg.symm) hPmonic.ne_zero ?_).trans_eq hPdeg
    simp only [hPmonic.leadingCoeff,leadingCoeff_mul,hu.leadingCoeff,hπm.leadingCoeff,mul_one]
  have hπrows : ∀ i, rationalModificationConstraint T u n i (u*π) = 0 := by
    apply (rationalModificationConstraint_eq_zero_iff T hu.ne_zero n _).mpr
    refine ⟨dvd_mul_right _ _,?_⟩
    intro r
    simpa only [π,polynomialWeightedFunctional_apply,mul_assoc] using
      functional_monicOrthogonalPolynomial_mul_X_pow_eq_zero (polynomialWeightedFunctional T u) hn r
  have heq : P = u*π := sub_eq_zero.mp
    (eq_zero_of_rationalModificationConstraint_eq_zero T hu.ne_zero hn
      (by simpa only [u,Lagrange.natDegree_nodal,card_univ,Fintype.card_fin] using hdiff)
      (by intro i; rw [map_sub,hfull i,hπrows i,sub_self]))
  rw [auxiliary_border_det_eq L T x z hm hd]
  change C M.det * P = _
  rw [heq]
  exact (mul_assoc _ _ _).symm

/-- The source first-row determinant, with the leading original polynomial
column first and auxiliary power columns immediately after it. -/
def rationalModificationAuxiliaryFirstRowMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (hm : n ≤ m) :
    Matrix (Fin 1 ⊕ RationalModificationAuxiliaryIndex l m n)
      (Fin 1 ⊕ RationalModificationAuxiliaryIndex l m n) 𝕜[X] :=
  (rationalModificationAuxiliaryBorderMatrix L T x z hm).submatrix
    (Equiv.sumComm _ _) (Equiv.sumComm _ _)

/-- The first-row source matrix with auxiliary powers gives the modified
polynomial and a proved nonzero actual source normalization.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationAuxiliaryFirstRowMatrix_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z) (hm : n ≤ m)
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0) :
    (rationalModificationAuxiliaryFirstRowMatrix L T x z hm).det =
      C (rationalModificationAuxiliaryMatrix L T x z hm).det * Lagrange.nodal Finset.univ x *
        monicOrthogonalPolynomial (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ∧
      (rationalModificationAuxiliaryMatrix L T x z hm).det ≠ 0 := by
  rw [rationalModificationAuxiliaryFirstRowMatrix,Matrix.det_submatrix_equiv_self]
  exact ⟨det_rationalModificationAuxiliaryBorderMatrix_eq L T x z hx hz hm hn,
    det_rationalModificationAuxiliaryMatrix_ne_zero L T x z hx hz hm hn⟩

end NLAlib
