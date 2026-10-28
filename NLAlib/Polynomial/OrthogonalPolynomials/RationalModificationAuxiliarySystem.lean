import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationAuxiliaryRows
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Nonzero source normalization for the auxiliary-power determinant

For `n≤m`, the source has `m-n` auxiliary power columns and `l+n`
original-polynomial columns. Its source root/Cauchy rows give a square minor.
The actual minor is nonsingular by modified finite moment nondegeneracy.
Source: Gautschi (2004), Theorem 2.53.
-/

noncomputable section
open Polynomial Matrix Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m n : ℕ}

private theorem auxiliary_fst_sum {ι : Type*} [Fintype ι] (f : ι → 𝕜[X] × 𝕜[X]) :
    (∑ j, f j).1 = ∑ j, (f j).1 := map_sum (LinearMap.fst 𝕜 𝕜[X] 𝕜[X]) _ _

private theorem auxiliary_snd_sum {ι : Type*} [Fintype ι] (f : ι → 𝕜[X] × 𝕜[X]) :
    (∑ j, f j).2 = ∑ j, (f j).2 := map_sum (LinearMap.snd 𝕜 𝕜[X] 𝕜[X]) _ _

/-- Column indices of the source small-order determinant. -/
abbrev RationalModificationAuxiliaryIndex (l m n : ℕ) := Fin (m-n) ⊕ Fin (l+n)

/-- The square row index enumerates numerator roots, then denominator roots. -/
def rationalModificationAuxiliaryRowEquiv (hm : n ≤ m) :
    RationalModificationAuxiliaryIndex l m n ≃ Fin (l+m) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Auxiliary powers first, then the original monic-polynomial columns. -/
def rationalModificationAuxiliaryColumn (L : 𝕜[X] →ₗ[𝕜] 𝕜) :
    RationalModificationAuxiliaryIndex l m n → 𝕜[X] × 𝕜[X] :=
  Sum.elim (fun j => (0,X^j.val)) (fun j => (monicOrthogonalPolynomial L j.val,0))

/-- The source normalization minor with auxiliary powers, evaluations at
numerator roots and Cauchy-cofactor moments at denominator roots. -/
def rationalModificationAuxiliaryMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (hm : n ≤ m) :
    Matrix (RationalModificationAuxiliaryIndex l m n)
      (RationalModificationAuxiliaryIndex l m n) 𝕜 :=
  fun i j => rationalModificationAuxiliaryRow T x z
    (rationalModificationAuxiliaryRowEquiv hm i) (rationalModificationAuxiliaryColumn L j)

/-- The actual source normalization minor is nonzero for `n≤m`, including
orders below the denominator degree. No nondegeneracy of the output is assumed.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationAuxiliaryMatrix_ne_zero
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z) (hm : n ≤ m)
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0) :
    (rationalModificationAuxiliaryMatrix L T x z hm).det ≠ 0 := by
  intro hd
  obtain ⟨c,hc,hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  let P : 𝕜[X] := ∑ j : Fin (l+n), c (Sum.inr j) • monicOrthogonalPolynomial L j.val
  let A : 𝕜[X] := ∑ j : Fin (m-n), c (Sum.inl j) • X^j.val
  have hP : P.degree < (l+n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast j.isLt
  have hA : A.degree < (m-n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    apply (degree_smul_le _ _).trans_lt
    rw [degree_X_pow]
    exact_mod_cast j.isLt
  have hs : (P,A) = ∑ j, c j • rationalModificationAuxiliaryColumn L j := by
    apply Prod.ext <;> simp [P,A,rationalModificationAuxiliaryColumn,Fintype.sum_sum_type,
      auxiliary_fst_sum,auxiliary_snd_sum]
  have hrows (i : Fin (l+m)) : rationalModificationAuxiliaryRow T x z i (P,A) = 0 := by
    rw [hs,map_sum]
    simp only [map_smul,smul_eq_mul]
    have hi := congrFun hMc ((rationalModificationAuxiliaryRowEquiv hm).symm i)
    simpa only [rationalModificationAuxiliaryMatrix,Matrix.mulVec,dotProduct,
      Equiv.apply_symm_apply,Pi.zero_apply,mul_comm] using hi
  have hfull := rationalModificationConstraint_of_auxiliary_rows T x z hx hz hm P A hA hrows
  have hP0 : P = 0 := eq_zero_of_rationalModificationConstraint_eq_zero T
    Lagrange.nodal_ne_zero hn
    (by simpa only [Lagrange.natDegree_nodal,card_univ,Fintype.card_fin] using hP) hfull
  have hAe (i : Fin m) : A.eval (z i) = 0 := by
    have hi := hrows ⟨l+i.val,by have := i.isLt; omega⟩
    simpa only [rationalModificationAuxiliaryRow,dif_neg (show ¬l+i.val<l by omega),
      Nat.add_sub_cancel_left,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.fst_apply,LinearMap.snd_apply,polynomialWeightedFunctional_apply,
      Polynomial.leval_apply,hP0,mul_zero,map_zero,zero_add] using hi
  have hA0 : A = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hz.injOn
      (by simpa only [card_univ,Fintype.card_fin] using
        hA.trans_le (by exact_mod_cast Nat.sub_le m n)) (fun i _ => hAe i)
  have hliP := (monicMomentPolynomialSequence L).linearIndependent.comp
    (fun j : Fin (l+n) => j.val) Fin.val_injective
  have hcP := Fintype.linearIndependent_iff.mp hliP (fun j => c (Sum.inr j)) hP0
  have hliA : LinearIndependent 𝕜 (fun j : Fin (m-n) => (X : 𝕜[X])^j.val) := by
    simpa only [coe_basisMonomials,Function.comp_def,monomial_one_right_eq_X_pow] using
      (Polynomial.basisMonomials 𝕜).linearIndependent.comp
        (fun j : Fin (m-n) => j.val) Fin.val_injective
  have hcA := Fintype.linearIndependent_iff.mp hliA (fun j => c (Sum.inl j)) hA0
  exact hc (funext (fun j => Sum.casesOn j hcA hcP))

end NLAlib
