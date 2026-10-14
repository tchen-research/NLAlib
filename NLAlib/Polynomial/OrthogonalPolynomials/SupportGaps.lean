import NLAlib.Polynomial.OrthogonalPolynomials.MeasureOrthogonality

/-! # At most one orthogonal-polynomial zero in each support gap

If two zeros lie in a support-free interval, divide out their two linear
factors. Orthogonality would then integrate a nonnegative product to zero,
forcing the original polynomial to vanish on the measure and contradicting
its positive squared norm.
Source: Gautschi (2004), Theorem 1.19; operator derivations OP11.
-/

noncomputable section

open Polynomial MeasureTheory Set

namespace NLAlib

/-- An open interval disjoint from a positive measure's support contains at most
one zero of its nonterminal monic orthogonal polynomial.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eq_of_eval_monicOrthogonalPolynomial_eq_zero_of_mem_support_gap
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n + 1 : ℕ∞) ≤ μ.support.encard) {c d u v : ℝ}
    (hg : Disjoint (Ioo c d) μ.support) (hu : u ∈ Ioo c d) (hv : v ∈ Ioo c d)
    (hpu : (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval u = 0)
    (hpv : (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval v = 0) : u = v := by
  let L := polynomialIntegral μ hμ
  let p := monicOrthogonalPolynomial L n
  have hp : p.Monic := monic_monicOrthogonalPolynomial L n
  by_contra huv
  obtain ⟨r, hpr⟩ := dvd_iff_isRoot.mpr hpu
  have hrv : r.eval v = 0 := by
    have h := congrArg (eval v) hpr
    rw [hpv] at h
    simp only [eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr (fun h => huv h.symm))
  obtain ⟨q, hrq⟩ := dvd_iff_isRoot.mpr hrv
  have hpq : p = ((X - C u) * (X - C v)) * q := by
    change monicOrthogonalPolynomial (polynomialIntegral μ hμ) n = _
    rw [hpr, hrq, mul_assoc]
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hpq
    exact hp.ne_zero hpq
  have hqd : q.degree < n := by
    have hd := congrArg natDegree hpq
    rw [natDegree_monicOrthogonalPolynomial,
      natDegree_mul (mul_ne_zero (monic_X_sub_C u).ne_zero (monic_X_sub_C v).ne_zero) hq0,
      natDegree_mul (monic_X_sub_C u).ne_zero (monic_X_sub_C v).ne_zero,
      natDegree_X_sub_C, natDegree_X_sub_C] at hd
    rw [degree_eq_natDegree hq0]
    exact_mod_cast (show q.natDegree < n by omega)
  have horth : (∫ x, p.eval x * q.eval x ∂μ) = 0 := by
    have hspec := isMonicOrthogonalPolynomial_polynomialIntegral μ hμ
      ((by exact_mod_cast Nat.le_succ n : (n : ℕ∞) ≤ n + 1).trans hn)
    simpa only [L, p, polynomialIntegral_apply, eval_mul] using hspec.orthogonal q hqd
  have hint : Integrable (fun x => p.eval x * q.eval x) μ := by
    convert hμ (p * q) using 1
    ext x
    simp
  have hnon : 0 ≤ᵐ[μ] (fun x => p.eval x * q.eval x) := by
    filter_upwards [μ.support_mem_ae] with x hx
    have hxg : x ∉ Ioo c d := fun h => Set.disjoint_left.mp hg h hx
    have heval : p.eval x * q.eval x = (x - u) * (x - v) * q.eval x ^ 2 := by
      rw [hpq]
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      ring
    rw [heval]
    apply mul_nonneg _ (sq_nonneg _)
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hxg
    rcases hxg with hxc | hdx
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hu.1]) (by linarith [hv.1])
    · exact mul_nonneg (by linarith [hu.2]) (by linarith [hv.2])
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnon hint).mp horth
  have hpzero : (∫ x, p.eval x ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    have hpx : p.eval x = 0 := by
      rcases mul_eq_zero.mp hx with hx | hx
      · exact hx
      · simp only [hpq, eval_mul, hx, mul_zero]
    simp only [hpx, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]
  have hpos : 0 < ∫ x, p.eval x ^ 2 ∂μ := by
    simpa only [L, p, orthogonalPolynomialNorm, polynomialIntegral_apply, eval_pow] using
      orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ hn
  exact hpos.ne' hpzero

/-- At the terminal order, the zeros are exactly the finite measure support.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eval_monicOrthogonalPolynomial_eq_zero_iff_mem_support_of_encard_eq
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : μ.support.encard = n) (x : ℝ) :
    (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval x = 0 ↔
      x ∈ μ.support := by
  have hs : μ.support.Finite := Set.finite_of_encard_le_coe hn.le
  have hcard : hs.toFinset.card = n := by
    exact_mod_cast hs.encard_eq_coe_toFinset_card.symm.trans hn
  rw [← hcard, monicOrthogonalPolynomial_eq_nodal_support μ hμ hs]
  simp only [Lagrange.nodal_eq, eval_prod, eval_sub, eval_X, eval_C, id_eq,
    Finset.prod_eq_zero_iff, sub_eq_zero, Set.Finite.mem_toFinset]
  exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- A support-free open interval contains at most one zero, including the
finite-support terminal polynomial. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eq_of_eval_monicOrthogonalPolynomial_eq_zero_of_mem_support_gap_le
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) {c d u v : ℝ}
    (hg : Disjoint (Ioo c d) μ.support) (hu : u ∈ Ioo c d) (hv : v ∈ Ioo c d)
    (hpu : (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval u = 0)
    (hpv : (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval v = 0) : u = v := by
  rcases hn.eq_or_lt with heq | hlt
  · have hus := (eval_monicOrthogonalPolynomial_eq_zero_iff_mem_support_of_encard_eq
      hμ heq.symm u).mp hpu
    exact (Set.disjoint_left.mp hg hu hus).elim
  · exact eq_of_eval_monicOrthogonalPolynomial_eq_zero_of_mem_support_gap hμ
      (by simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hlt)
      hg hu hv hpu hpv

end NLAlib
