import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationSmallSystem

/-!
# Finite algorithms for polynomial divisor modifications

For `T(v p)=L(p)`, the modified monic polynomial is obtained from the last
`min(n,degree v)` original polynomials by a nonsingular inverse-moment system.
This gives the linear and quadratic divisor algorithms, including their smaller
initial systems. No root simplicity or coprimality is needed.
Source: Gautschi (2004), Algorithms 2.8--2.11.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- The inverse-moment matrix for a divisor modification. -/
def divisorModificationMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (v : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (min n v.natDegree)) (Fin (min n v.natDegree)) 𝕜 :=
  fun i j => T (X ^ i.val * monicOrthogonalPolynomial L (n - v.natDegree + j.val))

/-- The right hand side of the actual inverse-moment system. -/
def divisorModificationMoments (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (v : 𝕜[X]) (n : ℕ) :
    Fin (min n v.natDegree) → 𝕜 := fun i => T (X ^ i.val * monicOrthogonalPolynomial L n)

/-- The computed lower coefficients in the original polynomial basis. -/
def divisorModificationCoefficients (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (v : 𝕜[X]) (n : ℕ) :
    Fin (min n v.natDegree) → 𝕜 :=
  -(divisorModificationMatrix L T v n)⁻¹ *ᵥ divisorModificationMoments L T v n

private theorem divisor_constraints_full
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v * p) = L p) (n : ℕ) (P : 𝕜[X])
    (horth : ∀ q : 𝕜[X], q.degree < (n-v.natDegree : ℕ) → L (P*q) = 0)
    (hsmall : ∀ i : Fin (min n v.natDegree), T (P * X^i.val) = 0) :
    ∀ q : 𝕜[X], q.degree < n → T (P*q) = 0 := by
  have hs := (rationalModificationConstraint_eq_zero_iff T (u := 1) one_ne_zero
    (min n v.natDegree) P).mpr ⟨one_dvd _, hsmall⟩
  have hf := (rationalModificationConstraint_small_iff_full L T (u := 1)
    one_ne_zero hv hTv n P horth).mp hs
  have hm := ((rationalModificationConstraint_eq_zero_iff T (u := 1) one_ne_zero n P).mp hf).2
  exact fun q hq => functional_mul_eq_zero_of_monomial_tests T hm hq

/-- Finite modified nondegeneracy proves that the actual divisor system is
nonsingular, including order zero and orders below the denominator degree.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_divisorModificationMatrix_ne_zero
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v * p) = L p) {n : ℕ}
    (hL : ∀ j < n, hankelMomentDet L j ≠ 0) (hn : hankelMomentDet T n ≠ 0) :
    (divisorModificationMatrix L T v n).det ≠ 0 := by
  intro hz
  obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  let P : 𝕜[X] := ∑ j : Fin (min n v.natDegree), c j •
    monicOrthogonalPolynomial L (n-v.natDegree+j.val)
  have hindex (j : Fin (min n v.natDegree)) : n-v.natDegree+j.val < n := by
    have := j.isLt; omega
  have hPdeg : P.degree < n := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hindex j
  have horth (q : 𝕜[X]) (hq : q.degree < (n-v.natDegree : ℕ)) : L (P*q) = 0 := by
    simp only [P, sum_mul, map_sum, smul_mul_assoc, map_smul]
    apply sum_eq_zero
    intro j _
    rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ (hindex j))).orthogonal q
      (hq.trans_le (by exact_mod_cast Nat.le_add_right (n-v.natDegree) j.val)), smul_zero]
  have hsmall (i : Fin (min n v.natDegree)) : T (P * X^i.val) = 0 := by
    have hi := congrFun hMc i
    dsimp only [P]
    rw [sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, smul_eq_mul]
    simpa only [divisorModificationMatrix, Matrix.mulVec, dotProduct,
      Pi.zero_apply, mul_comm] using hi
  have hzero := eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero
    T hn hPdeg (divisor_constraints_full L T hv hTv n P horth hsmall)
  have hlin := (monicMomentPolynomialSequence L).linearIndependent.comp
    (fun j : Fin (min n v.natDegree) => n-v.natDegree+j.val)
    (fun i j hij => Fin.ext (Nat.add_left_cancel hij))
  exact hc (funext (Fintype.linearIndependent_iff.mp hlin c hzero))

/-- The computed coefficients solve the actual inverse-moment equations.
atlas: christoffel-uvarov-modification (partial) -/
theorem divisorModificationMatrix_mulVec_coefficients
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v * p) = L p) {n : ℕ}
    (hL : ∀ j < n, hankelMomentDet L j ≠ 0) (hn : hankelMomentDet T n ≠ 0) :
    divisorModificationMatrix L T v n *ᵥ divisorModificationCoefficients L T v n =
      -divisorModificationMoments L T v n := by
  have hd := det_divisorModificationMatrix_ne_zero L T hv hTv hL hn
  rw [divisorModificationCoefficients, Matrix.neg_mulVec, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]

/-- The explicit finite inverse-moment algorithm produces the canonical modified
monic polynomial. A quadratic denominator uses the last three original polynomials
for `n≥2`; orders zero and one automatically use their smaller systems.
atlas: christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_eq_divisorModification
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v * p) = L p) {n : ℕ}
    (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0) (hn : hankelMomentDet T n ≠ 0) :
    monicOrthogonalPolynomial T n = monicOrthogonalPolynomial L n +
      ∑ j : Fin (min n v.natDegree), C (divisorModificationCoefficients L T v n j) *
        monicOrthogonalPolynomial L (n - v.natDegree + j.val) := by
  let c := divisorModificationCoefficients L T v n
  let low : 𝕜[X] := ∑ j : Fin (min n v.natDegree), C (c j) *
    monicOrthogonalPolynomial L (n-v.natDegree+j.val)
  let P := monicOrthogonalPolynomial L n + low
  have hindex (j : Fin (min n v.natDegree)) : n-v.natDegree+j.val < n := by
    have := j.isLt; omega
  have hlow : low.degree < n := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    rw [C_mul']
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hindex j
  have htop : (monicOrthogonalPolynomial L n).degree = (n : ℕ) := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hPmonic : P.Monic := (monic_monicOrthogonalPolynomial L n).add_of_left
    (hlow.trans_eq htop.symm)
  have hPdeg : P.natDegree = n := by
    dsimp only [P]
    rw [natDegree_add_eq_left_of_degree_lt (hlow.trans_eq htop.symm),
      natDegree_monicOrthogonalPolynomial]
  have horth (q : 𝕜[X]) (hq : q.degree < (n-v.natDegree : ℕ)) : L (P*q) = 0 := by
    dsimp only [P, low]
    rw [add_mul, map_add,
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n le_rfl)).orthogonal q
        (hq.trans_le (by exact_mod_cast Nat.sub_le n v.natDegree))]
    simp only [sum_mul, C_mul', smul_mul_assoc, map_sum, map_smul, zero_add]
    apply sum_eq_zero
    intro j _
    rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ (hindex j).le)).orthogonal q
      (hq.trans_le (by exact_mod_cast Nat.le_add_right (n-v.natDegree) j.val)), smul_zero]
  have hsmall (i : Fin (min n v.natDegree)) : T (P*X^i.val) = 0 := by
    have hi := congrFun (divisorModificationMatrix_mulVec_coefficients L T hv hTv
      (fun j hj => hL j hj.le) hn) i
    dsimp only [P, low]
    simp only [add_mul, map_add, sum_mul, C_mul', smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
    have he : (∑ j : Fin (min n v.natDegree), c j *
        T (monicOrthogonalPolynomial L (n-v.natDegree+j.val)*X^i.val)) =
        -T (X^i.val*monicOrthogonalPolynomial L n) := by
      simpa only [divisorModificationMatrix, divisorModificationMoments, Matrix.mulVec,
        dotProduct, Pi.neg_apply, c, mul_comm] using hi
    rw [he]
    rw [mul_comm (monicOrthogonalPolynomial L n), add_neg_cancel]
  exact (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial T hn).eq_of_hankelMomentDet_ne_zero
    ⟨hPmonic, hPdeg, divisor_constraints_full L T hv hTv n P horth hsmall⟩ hn

/-- The divisor coefficient solution is unique; singular normalization is ruled
out by the input functional hypotheses rather than assumed of the output. -/
theorem divisorModificationCoefficients_unique
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v * p) = L p) {n : ℕ}
    (hL : ∀ j < n, hankelMomentDet L j ≠ 0) (hn : hankelMomentDet T n ≠ 0)
    (c : Fin (min n v.natDegree) → 𝕜)
    (hc : divisorModificationMatrix L T v n *ᵥ c = -divisorModificationMoments L T v n) :
    c = divisorModificationCoefficients L T v n := by
  have hd := det_divisorModificationMatrix_ne_zero L T hv hTv hL hn
  have hi := congrArg (fun x => (divisorModificationMatrix L T v n)⁻¹ *ᵥ x)
    (hc.trans (divisorModificationMatrix_mulVec_coefficients L T hv hTv hL hn).symm)
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.one_mulVec] using hi

end NLAlib
