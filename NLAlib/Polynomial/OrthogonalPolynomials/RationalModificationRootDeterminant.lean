import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootSystem
import Mathlib.GroupTheory.Perm.Fin

/-!
# The Christoffel--Uvarov determinant with root and Cauchy rows

For denominator degree at most the order, the source matrix has the original
monic polynomials in its first row, evaluations at numerator roots next, and
Cauchy-cofactor moments at denominator roots last. Its actual normalization
minor is proved nonzero. This finite algebraic statement includes complex roots.
Source: Gautschi (2004), Theorems 2.52--2.53.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m : ℕ}

/-- The last column of root and Cauchy constraints. -/
def rationalModificationRootLeadingConstraints (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (n : ℕ) : Fin (l+m) → 𝕜 :=
  fun i => rationalModificationRootConstraint T x z i (monicOrthogonalPolynomial L (l+n))

/-- The root/Cauchy determinant in a last-row block convention. -/
def rationalModificationRootBorderMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (n : ℕ) :
    Matrix (Fin (l+m) ⊕ Fin 1) (Fin (l+m) ⊕ Fin 1) 𝕜[X] :=
  fromBlocks ((rationalModificationRootMatrix L T x z n).map C)
    (fun i _ => C (rationalModificationRootLeadingConstraints L T x z n i))
    (fun _ j => monicOrthogonalPolynomial L (n-m+j.val))
    (fun _ _ => monicOrthogonalPolynomial L (l+n))

set_option maxHeartbeats 1000000 in
private theorem root_border_det_eq (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (n : ℕ)
    (hd : (rationalModificationRootMatrix L T x z n).det ≠ 0) :
    (rationalModificationRootBorderMatrix L T x z n).det =
      C (rationalModificationRootMatrix L T x z n).det *
        (monicOrthogonalPolynomial L (l+n) -
          ∑ j : Fin (l+m),
            C (((rationalModificationRootMatrix L T x z n)⁻¹ *ᵥ
              rationalModificationRootLeadingConstraints L T x z n) j) *
                monicOrthogonalPolynomial L (n-m+j.val)) := by
  let M := rationalModificationRootMatrix L T x z n
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
  let : Invertible (M.map C) :=
    { invOf := (M⁻¹).map C
      invOf_mul_self := by rw [← Matrix.map_mul, M.nonsing_inv_mul hu]; simp
      mul_invOf_self := by rw [← Matrix.map_mul, M.mul_nonsing_inv hu]; simp }
  rw [rationalModificationRootBorderMatrix, det_fromBlocks₁₁,
    det_eq_elem_of_subsingleton _ (0 : Fin 1)]
  rw [show (M.map C).det = C M.det from (RingHom.map_det C M).symm]
  congr 1
  change monicOrthogonalPolynomial L (l+n) -
      ∑ j : Fin (l+m), (∑ i : Fin (l+m),
        monicOrthogonalPolynomial L (n-m+i.val) * C (M⁻¹ i j)) *
          C (rationalModificationRootLeadingConstraints L T x z n j) =
      monicOrthogonalPolynomial L (l+n) -
        ∑ i : Fin (l+m), C (∑ j : Fin (l+m), M⁻¹ i j *
          rationalModificationRootLeadingConstraints L T x z n j) *
            monicOrthogonalPolynomial L (n-m+i.val)
  simp only [map_sum, map_mul, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The exact source root/Cauchy determinant is a proved nonzero scalar times
the numerator polynomial times the canonical modified monic polynomial.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationRootBorderMatrix_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hTv : ∀ p, T (Lagrange.nodal Finset.univ z*p) = L p) {n : ℕ} (hm : m ≤ n)
    (hL : ∀ j ≤ l+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0) :
    (rationalModificationRootBorderMatrix L T x z n).det =
      C (rationalModificationRootMatrix L T x z n).det * Lagrange.nodal Finset.univ x *
        monicOrthogonalPolynomial (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n := by
  let M := rationalModificationRootMatrix L T x z n
  let b := rationalModificationRootLeadingConstraints L T x z n
  let c := M⁻¹ *ᵥ b
  let low : 𝕜[X] := ∑ j : Fin (l+m), C (c j) * monicOrthogonalPolynomial L (n-m+j.val)
  let P := monicOrthogonalPolynomial L (l+n) - low
  let u := Lagrange.nodal Finset.univ x
  let π := monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n
  have hd := det_rationalModificationRootMatrix_ne_zero L T x z hx hz hTv hm
    (fun j hj => hL j hj.le) hn
  have hMc : M *ᵥ c = b := by
    dsimp only [c]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  have hindex (j : Fin (l+m)) : n-m+j.val < l+n := by have := j.isLt; omega
  have hlow : low.degree < (l+n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    rw [C_mul']
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hindex j
  have htop : (monicOrthogonalPolynomial L (l+n)).degree = (l+n : ℕ) := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hPmonic : P.Monic := (monic_monicOrthogonalPolynomial L _).sub_of_left (hlow.trans_eq htop.symm)
  have hPdeg : P.degree = (l+n : ℕ) :=
    (degree_sub_eq_left_of_degree_lt (hlow.trans_eq htop.symm)).trans htop
  have hrows (i : Fin (l+m)) : rationalModificationRootConstraint T x z i P = 0 := by
    have hi := congrFun hMc i
    dsimp only [P, low]
    rw [map_sub, map_sum]
    simp only [C_mul', map_smul, smul_eq_mul]
    have he : (∑ j : Fin (l+m), c j * rationalModificationRootConstraint T x z i
        (monicOrthogonalPolynomial L (n-m+j.val))) = b i := by
      simpa only [M, rationalModificationRootMatrix, Matrix.mulVec, dotProduct, mul_comm] using hi
    rw [he]
    simp only [b, rationalModificationRootLeadingConstraints, sub_self]
  have horth (q : 𝕜[X]) (hq : q.degree < (n-m : ℕ)) : L (P*q) = 0 := by
    dsimp only [P, low]
    rw [sub_mul, map_sub,
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ le_rfl)).orthogonal q
        (hq.trans_le (by exact_mod_cast (show n-m ≤ l+n by omega)))]
    simp only [sum_mul, C_mul', smul_mul_assoc, map_sum, map_smul]
    rw [sum_eq_zero (fun j _ => by
      rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ (hindex j).le)).orthogonal q
        (hq.trans_le (by exact_mod_cast Nat.le_add_right (n-m) j.val)), smul_zero])]
    simp
  have hfull := rationalModificationConstraint_full_of_root_rows L T x z hx hz hTv horth hrows
  have hπ := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (polynomialWeightedFunctional T u) hn
  have hπm : π.Monic := hπ.monic
  have hu : u.Monic := Lagrange.nodal_monic
  have hUdeg : (u*π).degree = (l+n : ℕ) := by
    rw [degree_mul, degree_eq_natDegree hu.ne_zero, degree_eq_natDegree hπ.monic.ne_zero,
      hπ.natDegree_eq]
    simp only [u, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin, Nat.cast_add]
  have hdiff : (P-u*π).degree < (l+n : ℕ) := by
    apply (degree_sub_lt_left (hPdeg.trans hUdeg.symm) hPmonic.ne_zero ?_).trans_eq hPdeg
    simp only [hPmonic.leadingCoeff, leadingCoeff_mul, hu.leadingCoeff, hπm.leadingCoeff, mul_one]
  have hπrows : ∀ i, rationalModificationConstraint T u n i (u*π) = 0 := by
    apply (rationalModificationConstraint_eq_zero_iff T hu.ne_zero n _).mpr
    refine ⟨dvd_mul_right _ _, ?_⟩
    intro r
    simpa only [π, polynomialWeightedFunctional_apply, mul_assoc] using
      functional_monicOrthogonalPolynomial_mul_X_pow_eq_zero (polynomialWeightedFunctional T u) hn r
  have heq : P = u*π := sub_eq_zero.mp
    (eq_zero_of_rationalModificationConstraint_eq_zero T hu.ne_zero hn
      (by simpa only [u, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] using hdiff)
      (by intro i; rw [map_sub, hfull i, hπrows i, sub_self]))
  rw [root_border_det_eq L T x z n hd]
  change C M.det * P = _
  rw [heq]
  exact (mul_assoc _ _ _).symm

/-- The source first-row matrix: original monic polynomials followed by their
numerator evaluations and denominator Cauchy-cofactor integrals. -/
def rationalModificationRootFirstRowMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (n : ℕ) :
    Matrix (Fin (l+m+1)) (Fin (l+m+1)) 𝕜[X] :=
  fun i j => if hi : i.val=0 then monicOrthogonalPolynomial L (n-m+j.val)
    else C (rationalModificationRootConstraint T x z
      ⟨i.val-1, by have := i.isLt; omega⟩ (monicOrthogonalPolynomial L (n-m+j.val)))

/-- Moving the source polynomial row to the first position contributes the
explicit sign, including empty numerator or denominator root lists. -/
theorem det_rationalModificationRootFirstRowMatrix_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    {n : ℕ} (hm : m ≤ n) :
    (rationalModificationRootFirstRowMatrix L T x z n).det =
      (-1 : 𝕜[X])^(l+m) * (rationalModificationRootBorderMatrix L T x z n).det := by
  let k := l+m
  let B := (rationalModificationRootBorderMatrix L T x z n).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  have hlast (j : Fin (k+1)) :
      rationalModificationRootBorderMatrix L T x z n (Sum.inr 0) (finSumFinEquiv.symm j) =
        monicOrthogonalPolynomial L (n-m+j.val) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [finSumFinEquiv_symm_last, rationalModificationRootBorderMatrix,
        fromBlocks_apply₂₂, Fin.val_last, k, show n-m+(l+m)=l+n by omega]
    · simp [rationalModificationRootBorderMatrix]
  have hrow (i : Fin k) (j : Fin (k+1)) :
      rationalModificationRootBorderMatrix L T x z n (Sum.inl i) (finSumFinEquiv.symm j) =
        C (rationalModificationRootConstraint T x z i
          (monicOrthogonalPolynomial L (n-m+j.val))) := by
    refine Fin.lastCases ?_ (fun t => ?_) j
    · simp only [finSumFinEquiv_symm_last, rationalModificationRootBorderMatrix,
        fromBlocks_apply₁₂, rationalModificationRootLeadingConstraints, Fin.val_last, k,
        show n-m+(l+m)=l+n by omega]
    · simp [rationalModificationRootBorderMatrix, rationalModificationRootMatrix]
  have hrows : rationalModificationRootFirstRowMatrix L T x z n =
      B.submatrix (Fin.last k).cycleRange.symm id := by
    funext i j
    refine Fin.cases ?_ (fun t => ?_) i
    · simp only [rationalModificationRootFirstRowMatrix, Fin.val_zero,
        Matrix.submatrix_apply, id_eq, B, Fin.cycleRange_symm_zero, k, finSumFinEquiv_symm_last]
      exact (hlast j).symm
    · simp only [rationalModificationRootFirstRowMatrix, Fin.val_succ,
        dif_neg (show t.val+1 ≠ 0 by omega), Nat.add_sub_cancel,
        Matrix.submatrix_apply, id_eq, B, Fin.cycleRange_symm_succ,
        Fin.succAbove_last, finSumFinEquiv_symm_apply_castSucc]
      exact (hrow t j).symm
  rw [hrows, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
  simp [sign_finRotate, k]

/-- The source's first-row determinant is its proved nonzero normalization
times `u πhat_n`, with the exact row-permutation sign.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationRootFirstRowMatrix_eq_mul_monicOrthogonalPolynomial
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hTv : ∀ p, T (Lagrange.nodal Finset.univ z*p) = L p) {n : ℕ} (hm : m ≤ n)
    (hL : ∀ j ≤ l+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0) :
    (rationalModificationRootFirstRowMatrix L T x z n).det =
      C ((-1 : 𝕜)^(l+m) * (rationalModificationRootMatrix L T x z n).det) *
        Lagrange.nodal Finset.univ x *
          monicOrthogonalPolynomial (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ∧
      (-1 : 𝕜)^(l+m) * (rationalModificationRootMatrix L T x z n).det ≠ 0 := by
  constructor
  · rw [det_rationalModificationRootFirstRowMatrix_eq L T x z hm,
      det_rationalModificationRootBorderMatrix_eq L T x z hx hz hTv hm hL hn]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
  · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (det_rationalModificationRootMatrix_ne_zero L T x z hx hz hTv hm (fun j hj => hL j hj.le) hn)

end NLAlib
