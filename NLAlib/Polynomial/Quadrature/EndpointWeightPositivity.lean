import NLAlib.Polynomial.Quadrature.RadauLobatto

/-! # Positive endpoint quadrature weights

Polynomial exactness identifies each Radau weight with a squared cardinal integral.
Lobatto positivity uses the nonnegative interval endpoint factors, keeping the precise
support nondegeneracy in the statements.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A nonnegative polynomial integral is positive if its zeros imply the zeros of a
nonzero polynomial below the support-cardinality threshold. This allows nonnegative
interval factors in quadrature positivity tests without square-root measurability. -/
theorem integral_eval_pos_of_zero_imp_eval_zero {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {p r : ℝ[X]} (hp0 : p ≠ 0) (hp : p.degree < n)
    (hr : ∀ᵐ x ∂μ, 0 ≤ r.eval x) (hzero : ∀ x, r.eval x = 0 → p.eval x = 0) :
    0 < ∫ x, r.eval x ∂μ := by
  apply lt_of_le_of_ne (integral_nonneg_of_ae hr)
  intro he
  have hae : ∀ᵐ x ∂μ, r.eval x = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hr (hμ r)).mp he.symm] with x hx
    exact hx
  have hpint : (∫ x, (p.eval x) ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    simp only [hzero x hx, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]
  exact (integral_sq_eval_pos_of_le_support_encard hn hp0 hp (hμ.integrable_sq p)).ne' hpint

/-- Exactness through degree `2q` makes every weight of a distinct `(q+1)`-node Radau
rule strictly positive when the original positive measure has at least `q+1` support
points. Endpoint location is not needed for this squared-cardinal argument.
Source: Gautschi (2004), Theorems 3.3 and 3.7; operator derivations (AQ8).
atlas: gauss-radau-lobatto (partial) -/
theorem endpoint_quadrature_weight_pos_of_exact {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {q : ℕ} (hn : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (v w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (he : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i)) (i : Fin (q + 1)) : 0 < w i := by
  let B := Lagrange.basis univ v i
  have hBdeg : B.degree = (q : ℕ) := by
    simpa only [B, card_univ, Fintype.card_fin, Nat.add_sub_cancel] using
      Lagrange.degree_basis hv.injOn (mem_univ i)
  have hB0 : B ≠ 0 := Lagrange.basis_ne_zero hv.injOn (mem_univ i)
  have hp : (B ^ 2).degree < (2 * q + 1 : ℕ) := by
    rw [degree_pow, hBdeg, nsmul_eq_mul]
    exact_mod_cast (show 2 * q < 2 * q + 1 by omega)
  have hw : (∫ x, (B.eval x) ^ 2 ∂μ) = w i := by
    have h := he (B ^ 2) hp
    simp only [eval_pow] at h
    rw [h, sum_eq_single i]
    · simp only [B, Lagrange.eval_basis_self hv.injOn (mem_univ i), one_pow, mul_one]
    · intro j _ hji
      simp only [B, Lagrange.eval_basis_of_ne hji.symm (mem_univ j), zero_pow
        (by decide : (2 : ℕ) ≠ 0), mul_zero]
    · simp
  rw [← hw]
  apply integral_sq_eval_pos_of_le_support_encard hn hB0 _ (hμ.integrable_sq B)
  rw [hBdeg]
  exact_mod_cast Nat.lt_succ_self q

/-- A nonnegative polynomial factor times a square has positive integral when its
product with the unsquared polynomial is below the support threshold and nonzero. -/
theorem integral_eval_mul_sq_pos_of_le_support_encard {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {l p : ℝ[X]} (hl0 : l ≠ 0) (hp0 : p ≠ 0) (hp : (l * p).degree < n)
    (hl : ∀ᵐ x ∂μ, 0 ≤ l.eval x) :
    0 < ∫ x, l.eval x * (p.eval x) ^ 2 ∂μ := by
  have h := integral_eval_pos_of_zero_imp_eval_zero hμ hn (mul_ne_zero hl0 hp0) hp
    (r := l * p ^ 2) (by
      filter_upwards [hl] with x hx
      simp only [eval_mul, eval_pow]
      exact mul_nonneg hx (sq_nonneg _)) (by
      intro x hx
      simp only [eval_mul, eval_pow] at hx ⊢
      rcases mul_eq_zero.mp hx with hx | hx
      · rw [hx, zero_mul]
      · rw [sq_eq_zero_iff.mp hx, mul_zero])
  simpa only [eval_mul, eval_pow] using h

/-- Lobatto exactness through degree `2q+1` gives strictly positive endpoint and
interior weights for `q+2` distinct nodes when the original measure has at least
`q+2` support points. This support premise also handles a terminal atomic rule.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ8), (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem twoEndpoint_quadrature_weight_pos_of_exact {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a b : ℝ} (hab : a < b)
    (hμab : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (hn : (q + 2 : ℕ∞) ≤ μ.support.encard) (v : Fin q → ℝ)
    (w : Fin (q + 2) → ℝ) (hv : Function.Injective v) (hva : ∀ i, v i ∈ Ioo a b)
    (he : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i))
    (j : Fin (q + 2)) : 0 < w j := by
  let u := twoEndpointNodeFamily a b v
  let P := Lagrange.nodal univ v
  have hPdeg : P.natDegree = q := by simp only [P, Lagrange.natDegree_nodal,
    card_univ, Fintype.card_fin]
  have hPa : P.eval a ≠ 0 := Lagrange.eval_nodal_not_at_node fun i _ => (hva i).1.ne
  have hPb : P.eval b ≠ 0 := Lagrange.eval_nodal_not_at_node fun i _ => (hva i).2.ne'
  have hPv (i : Fin q) : P.eval (v i) = 0 := Lagrange.eval_nodal_at_node (mem_univ i)
  have hdeg {p : ℝ[X]} {d : ℕ} (hp : p.natDegree < d) : p.degree < d :=
    degree_le_natDegree.trans_lt (by exact_mod_cast hp)
  have htest (i : Fin (q + 2)) (r : ℝ[X]) (hr : r.degree < (2 * q + 2 : ℕ))
      (hri : 0 < r.eval (u i)) (hrj : ∀ j, j ≠ i → r.eval (u j) = 0)
      (hI : 0 < ∫ x, r.eval x ∂μ) : 0 < w i := by
    have h := he r hr
    rw [sum_eq_single i] at h
    · rw [h] at hI
      exact pos_of_mul_pos_left hI hri.le
    · intro j _ hji
      rw [hrj j hji, mul_zero]
    · simp
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · let l : ℝ[X] := -(X - C b)
    have hldeg : l.natDegree = 1 := by
      dsimp only [l]
      rw [natDegree_neg, natDegree_X_sub_C]
    have hl : ∀ᵐ x ∂μ, 0 ≤ l.eval x := by
      filter_upwards [hμab] with x hx
      simp only [l, eval_neg, eval_sub, eval_X, eval_C]
      linarith [hx.2]
    have hp : (l * P).degree < (q + 2 : ℕ) := by
      apply hdeg
      have h := natDegree_mul_le (p := l) (q := P)
      rw [hldeg, hPdeg] at h
      omega
    have hi := integral_eval_mul_sq_pos_of_le_support_encard hμ hn
      (neg_ne_zero.mpr (X_sub_C_ne_zero b)) Lagrange.nodal_ne_zero hp hl
    apply htest 0 (l * P ^ 2)
    · apply hdeg
      have h := natDegree_mul_le (p := l) (q := P ^ 2)
      rw [hldeg, natDegree_pow, hPdeg] at h
      omega
    · simpa only [u, twoEndpointNodeFamily, endpointNodeFamily, Fin.cases_zero,
        eval_mul, eval_neg, eval_sub, eval_X, eval_C, eval_pow, l] using
        mul_pos (by linarith : 0 < -(a - b)) (sq_pos_of_ne_zero hPa)
    · intro k
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
      · intro hk; exact (hk rfl).elim
      · intro _
        change (l * P ^ 2).eval b = 0
        simp [l]
      · intro _; simp [u, twoEndpointNodeFamily, endpointNodeFamily, hPv]
    · simpa only [eval_mul, eval_pow] using hi
  · let l : ℝ[X] := X - C a
    have hldeg : l.natDegree = 1 := natDegree_X_sub_C a
    have hl : ∀ᵐ x ∂μ, 0 ≤ l.eval x := by
      filter_upwards [hμab] with x hx
      simpa only [l, eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.1
    have hp : (l * P).degree < (q + 2 : ℕ) := by
      apply hdeg
      have h := natDegree_mul_le (p := l) (q := P)
      rw [hldeg, hPdeg] at h
      omega
    have hi := integral_eval_mul_sq_pos_of_le_support_encard hμ hn
      (X_sub_C_ne_zero a) Lagrange.nodal_ne_zero hp hl
    apply htest (Fin.succ 0) (l * P ^ 2)
    · apply hdeg
      have h := natDegree_mul_le (p := l) (q := P ^ 2)
      rw [hldeg, natDegree_pow, hPdeg] at h
      omega
    · simpa only [u, twoEndpointNodeFamily, endpointNodeFamily, Fin.cases_succ,
        Fin.cases_zero, eval_mul, eval_sub, eval_X, eval_C, eval_pow, l] using
        mul_pos (sub_pos.mpr hab) (sq_pos_of_ne_zero hPb)
    · intro k
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
      · intro _; simp [u, twoEndpointNodeFamily, endpointNodeFamily, l]
      · intro hk; exact (hk rfl).elim
      · intro _; simp [u, twoEndpointNodeFamily, endpointNodeFamily, hPv]
    · simpa only [eval_mul, eval_pow] using hi
  · let B := Lagrange.basis univ v i
    let l : ℝ[X] := (X - C a) * -(X - C b)
    have hBdeg : B.natDegree = q - 1 := by
      simpa only [B, card_univ, Fintype.card_fin] using Lagrange.natDegree_basis hv.injOn (mem_univ i)
    have hq : 0 < q := by have := i.isLt; omega
    have hl0 : l ≠ 0 := mul_ne_zero (X_sub_C_ne_zero a) (neg_ne_zero.mpr (X_sub_C_ne_zero b))
    have hB0 : B ≠ 0 := Lagrange.basis_ne_zero hv.injOn (mem_univ i)
    have hldeg : l.natDegree ≤ 2 := by
      have h := natDegree_mul_le (p := (X - C a : ℝ[X])) (q := -(X - C b))
      rw [natDegree_neg, natDegree_X_sub_C, natDegree_X_sub_C] at h
      exact h
    have hl : ∀ᵐ x ∂μ, 0 ≤ l.eval x := by
      filter_upwards [hμab] with x hx
      simp only [l, eval_mul, eval_sub, eval_neg, eval_X, eval_C]
      exact mul_nonneg (sub_nonneg.mpr hx.1) (by linarith [hx.2])
    have hp : (l * B).degree < (q + 2 : ℕ) := by
      apply hdeg
      have h := natDegree_mul_le (p := l) (q := B)
      rw [hBdeg] at h
      omega
    have hi := integral_eval_mul_sq_pos_of_le_support_encard hμ hn hl0 hB0 hp hl
    apply htest i.succ.succ (l * B ^ 2)
    · apply hdeg
      have h := natDegree_mul_le (p := l) (q := B ^ 2)
      rw [natDegree_pow, hBdeg] at h
      omega
    · simpa only [u, twoEndpointNodeFamily, endpointNodeFamily, Fin.cases_succ,
        eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_neg, l, B,
        Lagrange.eval_basis_self hv.injOn (mem_univ i), one_pow, mul_one] using
        mul_pos (sub_pos.mpr (hva i).1) (by simpa using sub_pos.mpr (hva i).2)
    · intro k
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
      · intro _
        change (l * B ^ 2).eval a = 0
        simp [l]
      · intro _
        change (l * B ^ 2).eval b = 0
        simp [l]
      · intro hk
        have hki : i ≠ k := by intro h; subst k; exact hk rfl
        simp [u, twoEndpointNodeFamily, endpointNodeFamily, B,
          Lagrange.eval_basis_of_ne hki (mem_univ k)]
    · simpa only [eval_mul, eval_pow] using hi

end NLAlib
