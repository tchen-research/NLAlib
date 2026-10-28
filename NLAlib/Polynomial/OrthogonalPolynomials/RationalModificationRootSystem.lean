import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootConstraints
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The source root/Cauchy constraint matrix

The source's small matrix has numerator evaluations and denominator Cauchy
rows. Its normalization is nonzero by finite modified nondegeneracy, rather
than a determinant hypothesis about the output. Complex roots are included.
Source: Gautschi (2004), Theorems 2.52--2.53.
-/

noncomputable section
open Polynomial Matrix Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m : ℕ}

/-- A source evaluation row followed by the Cauchy cofactor rows. -/
def rationalModificationRootConstraint (T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (i : Fin (l+m)) : 𝕜[X] →ₗ[𝕜] 𝕜 :=
  if hi : i.val < l then Polynomial.leval (x ⟨i.val, hi⟩) else
    polynomialWeightedFunctional T (rootCofactor z ⟨i.val-l, by have := i.isLt; omega⟩)

/-- Kernel of the concatenated root/Cauchy row vector. -/
theorem forall_rationalModificationRootConstraint_eq_zero_iff
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜) (P : 𝕜[X]) :
    (∀ i, rationalModificationRootConstraint T x z i P = 0) ↔
      (∀ i, P.eval (x i) = 0) ∧ (∀ i, T (P * rootCofactor z i) = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [rationalModificationRootConstraint, dif_pos i.isLt,
        Polynomial.leval_apply] using h ⟨i.val, by omega⟩
    · intro i
      have hi := h ⟨l+i.val, by have := i.isLt; omega⟩
      simpa only [rationalModificationRootConstraint, dif_neg (show ¬l+i.val<l by omega),
        Nat.add_sub_cancel_left, polynomialWeightedFunctional_apply, mul_comm] using hi
  · rintro ⟨hx, hz⟩ i
    unfold rationalModificationRootConstraint
    split_ifs with hi
    · exact hx ⟨i.val, hi⟩
    · simpa only [polynomialWeightedFunctional_apply, mul_comm] using
        hz ⟨i.val-l, by have := i.isLt; omega⟩

/-- The source rows and original lower orthogonality imply all native
modified orthogonality constraints, including orders above the denominator degree. -/
theorem rationalModificationConstraint_full_of_root_rows
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hTv : ∀ p, T (Lagrange.nodal Finset.univ z*p) = L p) {n : ℕ} {P : 𝕜[X]}
    (horth : ∀ q : 𝕜[X], q.degree < (n-m : ℕ) → L (P*q) = 0)
    (hrows : ∀ i, rationalModificationRootConstraint T x z i P = 0) :
    ∀ i, rationalModificationConstraint T (Lagrange.nodal Finset.univ x) n i P = 0 := by
  obtain ⟨heval, hcof⟩ := (forall_rationalModificationRootConstraint_eq_zero_iff T x z P).mp hrows
  have hdiv := (nodal_dvd_iff_forall_eval_eq_zero x hx P).mpr heval
  have hmoment := (forall_rootCofactor_moment_eq_zero_iff T z hz P).mp hcof
  have hs := (rationalModificationConstraint_eq_zero_iff T Lagrange.nodal_ne_zero
    (min n (Lagrange.nodal Finset.univ z).natDegree) P).mpr
      ⟨hdiv, fun r => hmoment (X^r.val) (by
        rw [degree_X_pow]
        exact_mod_cast (show r.val < m by
          have hr := lt_of_lt_of_le r.isLt (min_le_right n (Lagrange.nodal Finset.univ z).natDegree)
          simpa only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] using hr))⟩
  exact (rationalModificationConstraint_small_iff_full L T
    Lagrange.nodal_ne_zero Lagrange.nodal_ne_zero hTv n P
    (by simpa only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] using horth)).mp hs

/-- Finite modified nondegeneracy kills every lower-degree polynomial satisfying
the source rows and the original lower orthogonality conditions. -/
theorem eq_zero_of_rationalModificationRootConstraint_eq_zero
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hTv : ∀ p, T (Lagrange.nodal Finset.univ z*p) = L p) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0)
    {P : 𝕜[X]} (hP : P.degree < (l+n : ℕ))
    (horth : ∀ q : 𝕜[X], q.degree < (n-m : ℕ) → L (P*q) = 0)
    (hrows : ∀ i, rationalModificationRootConstraint T x z i P = 0) : P = 0 := by
  exact eq_zero_of_rationalModificationConstraint_eq_zero T Lagrange.nodal_ne_zero hn
    (by simpa only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] using hP)
    (rationalModificationConstraint_full_of_root_rows L T x z hx hz hTv horth hrows)

/-- The source root/Cauchy matrix in the original polynomial basis. When `m≤n`,
its columns run from `π_(n-m)` through `π_(n+l-1)`. -/
def rationalModificationRootMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (n : ℕ) : Matrix (Fin (l+m)) (Fin (l+m)) 𝕜 :=
  fun i j => rationalModificationRootConstraint T x z i
    (monicOrthogonalPolynomial L (n-m+j.val))

/-- The root/Cauchy normalization minor is nonzero under the native source
functional assumptions, including empty root lists and repeated eigenvalues of
the underlying Jacobi system. The modification roots themselves are distinct.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationRootMatrix_ne_zero
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hTv : ∀ p, T (Lagrange.nodal Finset.univ z*p) = L p) {n : ℕ} (hm : m ≤ n)
    (hL : ∀ j < l+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T (Lagrange.nodal Finset.univ x)) n ≠ 0) :
    (rationalModificationRootMatrix L T x z n).det ≠ 0 := by
  intro hd
  obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  let P : 𝕜[X] := ∑ j : Fin (l+m), c j • monicOrthogonalPolynomial L (n-m+j.val)
  have hindex (j : Fin (l+m)) : n-m+j.val < l+n := by have := j.isLt; omega
  have hPdeg : P.degree < (l+n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hindex j
  have horth (q : 𝕜[X]) (hq : q.degree < (n-m : ℕ)) : L (P*q) = 0 := by
    simp only [P, sum_mul, smul_mul_assoc, map_sum, map_smul]
    apply sum_eq_zero
    intro j _
    rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ (hindex j))).orthogonal q
      (hq.trans_le (by exact_mod_cast Nat.le_add_right (n-m) j.val)), smul_zero]
  have hrows (i : Fin (l+m)) : rationalModificationRootConstraint T x z i P = 0 := by
    have hi := congrFun hMc i
    simpa only [P, map_sum, map_smul, smul_eq_mul, rationalModificationRootMatrix,
      Matrix.mulVec, dotProduct, mul_comm, Pi.zero_apply] using hi
  have hzero := eq_zero_of_rationalModificationRootConstraint_eq_zero L T x z hx hz hTv hn
    hPdeg horth hrows
  have hlin := (monicMomentPolynomialSequence L).linearIndependent.comp
    (fun j : Fin (l+m) => n-m+j.val) (fun i j hij => Fin.ext (Nat.add_left_cancel hij))
  exact hc (funext (Fintype.linearIndependent_iff.mp hlin c hzero))

end NLAlib
