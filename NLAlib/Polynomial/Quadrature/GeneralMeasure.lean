import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Polynomial

/-! # Interpolatory Gauss quadrature for arbitrary compactly supported measures

Polynomial division proves exactness from the defining orthogonality of the nodal
polynomial. Support nondegeneracy proves strict positivity of the actual integrated
cardinal weights, including measures supported at exactly the number of nodes.
-/

noncomputable section
open Polynomial MeasureTheory Set Finset
namespace NLAlib

/-- Polynomial evaluations are integrable for any finite measure concentrated on a
compact interval. Source: the compact-moment prerequisite of ATAP Theorem 19.1. -/
theorem integrable_eval_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (p : ℝ[X]) : Integrable p.eval μ := by
  refine (p.continuous.continuousOn.integrableOn_compact (isCompact_Icc (a := a) (b := b))).integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [hμ] with x hx hnot
  exact (hnot hx).elim

/-- Every nonzero polynomial of degree below the number of distinct support witnesses
has strictly positive squared integral. Source: positive definiteness of polynomial
moments in the proof of ATAP Theorem 19.1. -/
theorem integral_sq_eval_pos_of_degree_lt {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {ι : Type*} (s : Finset ι) {u : ι → ℝ}
    (hu : InjOn u s) (huμ : ∀ i ∈ s, u i ∈ μ.support) {p : ℝ[X]}
    (hp : p.degree < s.card) (hp0 : p ≠ 0) : 0 < ∫ x, (p.eval x) ^ 2 ∂μ := by
  have hi : Integrable (fun x => (p.eval x) ^ 2) μ := by
    have hpow : (p ^ 2).eval = fun x => (p.eval x) ^ 2 := by
      funext x
      exact eval_pow 2
    rw [← hpow]
    exact integrable_eval_of_ae_mem_Icc hμ (p ^ 2)
  have hnon : 0 ≤ ∫ x, (p.eval x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro heq
  have hae : (fun x => (p.eval x) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp heq.symm
  have hs : μ.support ⊆ {x | p.eval x = 0} := by
    apply Measure.support_subset_of_isClosed (isClosed_eq p.continuous continuous_const)
    filter_upwards [hae] with x hx
    simpa only [Pi.zero_apply, sq_eq_zero_iff] using hx
  exact hp0 (eq_zero_of_degree_lt_of_eval_index_eq_zero s hu hp
    (fun i hi => hs (huμ i hi)))

/-- Integrating the cardinal Lagrange polynomials gives a rule exact through degree
`N−1` for any `N` distinct nodes. Source: Trefethen, ATAP, Theorem 19.1.
atlas: gauss-quadrature-general-measure (partial) -/
theorem integral_eval_eq_sum_integral_basis_mul_eval_of_degree_lt
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) (hv : InjOn v s)
    {p : ℝ[X]} (hp : p.degree < s.card) :
    (∫ x, p.eval x ∂μ) = ∑ i ∈ s, (∫ x, (Lagrange.basis s v i).eval x ∂μ) * p.eval (v i) := by
  have hpI := Lagrange.eq_interpolate hv hp
  conv_lhs => rw [hpI]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum s (fun i hi =>
    (integrable_eval_of_ae_mem_Icc hμ (Lagrange.basis s v i)).const_mul _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- At zeros of a degree-`N` orthogonal polynomial, the integrated cardinal rule is
exact through degree `2N−1`. Orthogonality is stated directly for the monic nodal
polynomial, so no normalization or positive norm of the degree-`N` polynomial is needed.
Source: Trefethen, ATAP, Theorem 19.1; division proof.
atlas: gauss-quadrature-general-measure (partial) -/
theorem integral_eval_eq_sum_integral_basis_mul_eval_of_orthogonal_nodal
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) (hv : InjOn v s)
    (horth : ∀ q : ℝ[X], q.degree < s.card →
      ∫ x, (Lagrange.nodal s v).eval x * q.eval x ∂μ = 0)
    {p : ℝ[X]} (hp : p.degree < (2 * s.card : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i ∈ s, (∫ x, (Lagrange.basis s v i).eval x ∂μ) * p.eval (v i) := by
  let l := Lagrange.nodal s v
  let Q := p /ₘ l
  let R := p %ₘ l
  have hQ : Q.degree < s.card := by
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    have hp0 : p ≠ 0 := by intro h; simp [Q, h] at hQ0
    have hn := (natDegree_lt_iff_degree_lt hp0).mpr hp
    rw [degree_eq_natDegree hQ0]
    have hqn : Q.natDegree = p.natDegree - s.card := by
      simp only [Q, natDegree_divByMonic p Lagrange.nodal_monic, l, Lagrange.natDegree_nodal]
    rw [hqn]
    exact_mod_cast (show p.natDegree - s.card < s.card by omega)
  have hR : R.degree < s.card := by
    simpa only [R, l, Lagrange.degree_nodal] using
      degree_modByMonic_lt p (Lagrange.nodal_monic (s := s) (v := v))
  have hdiv : p = R + l * Q := (modByMonic_add_div p l).symm
  have hInt : (∫ x, p.eval x ∂μ) = ∫ x, R.eval x ∂μ := by
    conv_lhs => rw [hdiv]
    simp only [eval_add, eval_mul]
    rw [integral_add (integrable_eval_of_ae_mem_Icc hμ R)
      (by simpa only [eval_mul] using integrable_eval_of_ae_mem_Icc hμ (l * Q)),
      horth Q hQ, add_zero]
  rw [hInt, integral_eval_eq_sum_integral_basis_mul_eval_of_degree_lt hμ s v hv hR]
  apply Finset.sum_congr rfl
  intro i hi
  have hnode : R.eval (v i) = p.eval (v i) := by
    rw [hdiv, eval_add, eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul, add_zero]
  rw [hnode]

/-- A Gauss weight equals the squared integral of its cardinal polynomial.
Source: Trefethen, ATAP, Theorem 19.1. This proves positivity without requiring
a nonzero norm for the degree-`N` orthogonal polynomial.
atlas: gauss-quadrature-general-measure (partial) -/
theorem integral_basis_eq_integral_sq_basis_of_orthogonal_nodal
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) (hv : InjOn v s)
    (horth : ∀ q : ℝ[X], q.degree < s.card →
      ∫ x, (Lagrange.nodal s v).eval x * q.eval x ∂μ = 0) {i : ι} (hi : i ∈ s) :
    (∫ x, (Lagrange.basis s v i).eval x ∂μ) =
      ∫ x, ((Lagrange.basis s v i).eval x) ^ 2 ∂μ := by
  have hcard : 0 < s.card := card_pos.mpr ⟨i, hi⟩
  have hdeg : ((Lagrange.basis s v i) ^ 2).degree < (2 * s.card : ℕ) := by
    rw [degree_pow, Lagrange.degree_basis hv hi]
    simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using
      (show ((2 * (s.card - 1) : ℕ) : WithBot ℕ) < ((2 * s.card : ℕ) : WithBot ℕ)
        from Nat.cast_lt.mpr (by omega))
  have h := integral_eval_eq_sum_integral_basis_mul_eval_of_orthogonal_nodal hμ s v hv horth hdeg
  have hpow : ((Lagrange.basis s v i) ^ 2).eval =
      fun x => ((Lagrange.basis s v i).eval x) ^ 2 := by
    funext x
    exact eval_pow 2
  rw [hpow] at h
  simp only [eval_pow] at h
  rw [sum_eq_single i] at h
  · simpa only [Lagrange.eval_basis_self hv hi, one_pow, mul_one] using h.symm
  · intro j hj hji
    rw [Lagrange.eval_basis_of_ne hji.symm hj, zero_pow (by decide), mul_zero]
  · exact fun hnot => (hnot hi).elim

/-- General Gauss quadrature has positive weights, total mass equal to the measure's
mass, and exactness through degree `2N−1`. The supplied distinct nodes are defined
by their monic nodal polynomial's orthogonality to all degrees below `N`. The measure
is concentrated on a compact interval and has at least `N` distinct support witnesses.
Source: Trefethen, ATAP, Theorem 19.1. This includes exactly `N` support points.
atlas: gauss-quadrature-general-measure -/
theorem gauss_quadrature_of_orthogonal_nodal
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℝ) (hv : InjOn v s)
    (horth : ∀ q : ℝ[X], q.degree < s.card →
      ∫ x, (Lagrange.nodal s v).eval x * q.eval x ∂μ = 0)
    (hsupport : ∃ u : ι → ℝ, InjOn u s ∧ ∀ i ∈ s, u i ∈ μ.support) :
    (∀ i ∈ s, 0 < ∫ x, (Lagrange.basis s v i).eval x ∂μ) ∧
      (∑ i ∈ s, ∫ x, (Lagrange.basis s v i).eval x ∂μ) = (μ univ).toReal ∧
      (∀ p : ℝ[X], p.degree < (2 * s.card : ℕ) →
        (∫ x, p.eval x ∂μ) =
          ∑ i ∈ s, (∫ x, (Lagrange.basis s v i).eval x ∂μ) * p.eval (v i)) := by
  obtain ⟨u, hu, huμ⟩ := hsupport
  refine ⟨?_, ?_, fun p hp =>
    integral_eval_eq_sum_integral_basis_mul_eval_of_orthogonal_nodal hμ s v hv horth hp⟩
  · intro i hi
    rw [integral_basis_eq_integral_sq_basis_of_orthogonal_nodal hμ s v hv horth hi]
    apply integral_sq_eval_pos_of_degree_lt hμ s hu huμ
    · rw [Lagrange.degree_basis hv hi]
      exact_mod_cast (show s.card - 1 < s.card by have h := hs.card_pos; omega)
    · exact Lagrange.basis_ne_zero hv hi
  · have hdeg : (1 : ℝ[X]).degree < (2 * s.card : ℕ) := by
      simp only [degree_one]
      exact_mod_cast (show 0 < 2 * s.card by have h := hs.card_pos; omega)
    have h := integral_eval_eq_sum_integral_basis_mul_eval_of_orthogonal_nodal
      hμ s v hv horth hdeg
    simpa only [eval_one, mul_one, integral_const, smul_eq_mul, mul_one, measureReal_def] using h.symm

end NLAlib
