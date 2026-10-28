import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootConstraints

/-!
# The auxiliary power columns when the divisor degree exceeds the order

The source determinant uses `m-n` power columns at the denominator roots.
The top-coefficient Lagrange identity shows that these columns imply exactly
the required first `n` divided-moment tests. No rank or output-normalization
assumption is used.
Source: Gautschi (2004), Theorem 2.53.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m n : ℕ}

/-- Cauchy values equal to a polynomial of degree below `m-n` annihilate all
the divided moments below `n`. This includes `n=0` and empty auxiliary spaces.
atlas: christoffel-uvarov-modification (partial) -/
theorem moments_eq_zero_of_rootCofactor_eq_low_polynomial
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (z : Fin m → 𝕜) (hz : Function.Injective z)
    (hm : n ≤ m) (P a : 𝕜[X]) (ha : a.degree < (m-n : ℕ))
    (hc : ∀ i, T (P*rootCofactor z i) = a.eval (z i)) :
    ∀ q : 𝕜[X], q.degree < n → T (P*q) = 0 := by
  intro q hq
  have hqm : q.degree < m := hq.trans_le (by exact_mod_cast hm)
  have hprod : (a*q).degree < (m-1 : ℕ) := by
    by_cases ha0 : a = 0
    · simp [ha0]
    by_cases hq0 : q = 0
    · simp [hq0]
    have ha' : a.natDegree < m-n := by
      exact_mod_cast (show (a.natDegree : WithBot ℕ) < (m-n : ℕ) by
        simpa only [degree_eq_natDegree ha0] using ha)
    have hq' : q.natDegree < n := by
      exact_mod_cast (show (q.natDegree : WithBot ℕ) < (n : ℕ) by
        simpa only [degree_eq_natDegree hq0] using hq)
    rw [degree_mul, degree_eq_natDegree ha0, degree_eq_natDegree hq0, ← Nat.cast_add]
    exact_mod_cast (show a.natDegree+q.natDegree < m-1 by omega)
  have hprod' : (a*q).degree < m := hprod.trans_le (by exact_mod_cast Nat.sub_le m 1)
  have hi := Lagrange.coeff_eq_sum (s := Finset.univ) hz.injOn
    (by simpa only [card_univ, Fintype.card_fin] using hprod')
  simp only [card_univ, Fintype.card_fin] at hi
  have hsum : ∑ i : Fin m, (a.eval (z i)*q.eval (z i))/(rootCofactor z i).eval (z i) = 0 := by
    rw [show (a*q).coeff (m-1) = 0 from coeff_eq_zero_of_degree_lt hprod] at hi
    simpa only [card_univ, Fintype.card_fin, eval_mul, rootCofactor, eval_prod,
      eval_sub, eval_X, eval_C] using hi.symm
  rw [eq_sum_C_mul_rootCofactor z hz hqm, mul_sum, map_sum]
  have hpull (i : Fin m) :
      T (P*(C (q.eval (z i)/(rootCofactor z i).eval (z i))*rootCofactor z i)) =
        (q.eval (z i)/(rootCofactor z i).eval (z i))*a.eval (z i) := by
    rw [show P*(C (q.eval (z i)/(rootCofactor z i).eval (z i))*rootCofactor z i) =
        C (q.eval (z i)/(rootCofactor z i).eval (z i))*(P*rootCofactor z i) by ring,
      C_mul', map_smul, hc, smul_eq_mul]
  simp_rw [hpull]
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- The source small-order row is numerator evaluation, or Cauchy moment plus
evaluation of the auxiliary polynomial at a denominator root. -/
def rationalModificationAuxiliaryRow (T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (i : Fin (l+m)) :
    (𝕜[X] × 𝕜[X]) →ₗ[𝕜] 𝕜 :=
  if hi : i.val < l then
    (Polynomial.leval (x ⟨i.val,hi⟩)).comp (LinearMap.fst 𝕜 𝕜[X] 𝕜[X]) else
    (polynomialWeightedFunctional T (rootCofactor z ⟨i.val-l,by have := i.isLt; omega⟩)).comp
        (LinearMap.fst 𝕜 𝕜[X] 𝕜[X]) +
      (Polynomial.leval (z ⟨i.val-l,by have := i.isLt; omega⟩)).comp
        (LinearMap.snd 𝕜 𝕜[X] 𝕜[X])

/-- Source auxiliary rows imply the native numerator and `n` moment constraints.
atlas: christoffel-uvarov-modification (partial) -/
theorem rationalModificationConstraint_of_auxiliary_rows
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z) (hm : n ≤ m)
    (P a : 𝕜[X]) (ha : a.degree < (m-n : ℕ))
    (hr : ∀ i, rationalModificationAuxiliaryRow T x z i (P,a) = 0) :
    ∀ i, rationalModificationConstraint T (Lagrange.nodal Finset.univ x) n i P = 0 := by
  have heval (i : Fin l) : P.eval (x i) = 0 := by
    simpa only [rationalModificationAuxiliaryRow, dif_pos i.isLt,
      LinearMap.comp_apply, LinearMap.fst_apply, Polynomial.leval_apply]
      using hr ⟨i.val,by have := i.isLt; omega⟩
  have hc (i : Fin m) : T (P*rootCofactor z i) = (-a).eval (z i) := by
    have hi := hr ⟨l+i.val,by have := i.isLt; omega⟩
    simp only [rationalModificationAuxiliaryRow, dif_neg (show ¬l+i.val<l by omega),
      Nat.add_sub_cancel_left, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, Polynomial.leval_apply,
      polynomialWeightedFunctional_apply, mul_comm] at hi
    simpa only [eval_neg] using eq_neg_of_add_eq_zero_left hi
  have hmoment := moments_eq_zero_of_rootCofactor_eq_low_polynomial T z hz hm P (-a)
    (by simpa only [degree_neg] using ha) hc
  apply (rationalModificationConstraint_eq_zero_iff T Lagrange.nodal_ne_zero n P).mpr
  exact ⟨(nodal_dvd_iff_forall_eval_eq_zero x hx P).mpr heval,
    fun i => hmoment (X^i.val) (by rw [degree_X_pow]; exact_mod_cast i.isLt)⟩

end NLAlib
