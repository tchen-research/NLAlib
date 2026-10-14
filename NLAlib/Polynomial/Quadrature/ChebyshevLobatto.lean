import NLAlib.Polynomial.BestApproximation.LobattoCardinals
import NLAlib.Polynomial.Chebyshev.CosineBasis
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-! # The explicit Chebyshev Gauss–Lobatto rule

Integrating the actual endpoint-half cosine cardinals against the Chebyshev first-kind
measure gives weights `π/N`, halved at the two endpoints. The existing finite frequency
folding proves exactness through degree `2N−1` on the `N+1` extrema nodes.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev Real Finset MeasureTheory

namespace NLAlib

/-- Every polynomial is integrable against the first-kind Chebyshev measure. -/
theorem hasPolynomialMoments_measureT : HasPolynomialMoments measureT :=
  fun p => integrable_measureT p.continuous.continuousOn

/-- The actual extrema cardinal integral against the first-kind Chebyshev measure is
the explicit endpoint-half weight. Source: Gautschi (2004), Example 1.50.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_lobattoCardinal_measureT {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (∫ x, (lobattoCardinal N j).eval x ∂measureT) = π * lobattoEndpointWeight N j / N := by
  let L := polynomialIntegral measureT hasPolynomialMoments_measureT
  have hL0 : L 1 = π := by
    simpa only [L, polynomialIntegral_apply, T_zero] using integral_eval_T_real_measureT_zero
  have hLT (k : ℕ) (hk : k ≠ 0) : L (T ℝ k) = 0 :=
    integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hk)
  change L (lobattoCardinal N j) = _
  simp only [lobattoCardinal, map_smul, map_add, map_sum, smul_eq_mul, hL0,
    hLT N hN.ne', hLT _ (Nat.succ_ne_zero _), mul_zero, sum_const_zero, add_zero]
  ring

/-- The explicit Chebyshev Lobatto weights are positive, including both half-weight
endpoints. Source: Gautschi (2004), Example 1.50.
atlas: gauss-radau-lobatto (partial) -/
theorem chebyshevLobattoWeight_pos {N : ℕ} (hN : 0 < N) (j : ℕ) :
    0 < π * lobattoEndpointWeight N j / N := by
  apply div_pos _ (by exact_mod_cast hN)
  apply mul_pos pi_pos
  unfold lobattoEndpointWeight
  split_ifs <;> norm_num

/-- The actual Chebyshev Gauss–Lobatto rule has `N+1` extrema nodes and the explicit
endpoint-half weights, and integrates every polynomial through degree `2N−1`.
The case `N=1` is the two-endpoint rule. Source: Gautschi (2004), Example 1.50.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_measureT_eq_chebyshevLobattoRule {N : ℕ} (hN : 0 < N)
    {p : ℝ[X]} (hp : p.degree < (2 * N : ℕ)) :
    (∫ x, p.eval x ∂measureT) =
      ∑ j ∈ range (N + 1), (π * lobattoEndpointWeight N j / N) * p.eval (node N j) := by
  let L := polynomialIntegral measureT hasPolynomialMoments_measureT
  let Q : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := fun p => ∑ j ∈ range (N + 1),
        (π * lobattoEndpointWeight N j / N) * p.eval (node N j)
      map_add' := by intro p q; simp [mul_add, sum_add_distrib]
      map_smul' := by
        intro c p
        simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring }
  have hcard (j : ℕ) (hj : j ∈ range (N + 1)) :
      L (Lagrange.basis (range (N + 1)) (node N) j) = π * lobattoEndpointWeight N j / N := by
    rw [← lobattoCardinal_eq_basis hN (by have := mem_range.mp hj; omega)]
    exact integral_lobattoCardinal_measureT hN j
  have hLT (k : ℕ) : L (T ℝ k) = if k = 0 then π else 0 := by
    by_cases hk : k = 0
    · subst k
      exact integral_eval_T_real_measureT_zero
    · rw [if_neg hk]
      exact integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hk)
  have hLQ (k : ℕ) (hk : k < 2 * N) : L (T ℝ k) = Q (T ℝ k) := by
    have hinterp : L (Lagrange.interpolate (range (N + 1)) (node N)
        (fun j => (T ℝ k).eval (node N j))) = Q (T ℝ k) := by
      simp only [Lagrange.interpolate_apply, C_mul', map_sum, map_smul, smul_eq_mul]
      change (∑ j ∈ range (N + 1), (T ℝ k).eval (node N j) *
        L (Lagrange.basis (range (N + 1)) (node N) j)) = _
      apply sum_congr rfl
      intro j hj
      rw [hcard j hj]
      ring
    rw [interpolate_eval_T_node_eq_T_alias hN] at hinterp
    rw [← hinterp, hLT, hLT]
    have hzero : chebyshevAliasIndex N k = 0 ↔ k = 0 := by
      unfold chebyshevAliasIndex
      rw [Nat.mod_eq_of_lt hk]
      omega
    simp only [hzero]
  by_cases hp0 : p = 0
  · simp [hp0]
  have hp' : p.degree ≤ (2 * N - 1 : ℕ) := by
    rw [degree_eq_natDegree hp0] at hp ⊢
    have hd : p.natDegree < 2 * N := by exact_mod_cast hp
    exact_mod_cast (show p.natDegree ≤ 2 * N - 1 by omega)
  obtain ⟨c, hc⟩ := exists_sum_smul_T_eq_of_degree_le hp'
  change L p = Q p
  rw [← hc, map_sum, map_sum]
  apply sum_congr rfl
  intro k hk
  rw [map_smul, map_smul, hLQ k (by have := mem_range.mp hk; omega)]

/-- The explicit endpoint-half Chebyshev Lobatto weights sum to the measure mass `π`.
Source: Gautschi (2004), Example 1.50.
atlas: gauss-radau-lobatto (partial) -/
theorem sum_chebyshevLobattoWeight {N : ℕ} (hN : 0 < N) :
    (∑ j ∈ range (N + 1), π * lobattoEndpointWeight N j / N) = π := by
  have h := integral_eval_measureT_eq_chebyshevLobattoRule hN (p := 1) (by
    simpa only [degree_one] using (show (0 : WithBot ℕ) < (2 * N : ℕ) by exact_mod_cast (show 0 < 2 * N by omega)))
  have hm : (∫ x, (1 : ℝ[X]).eval x ∂measureT) = π := by
    simpa only [T_zero] using integral_eval_T_real_measureT_zero
  simpa only [eval_one, mul_one] using h.symm.trans hm

/-- Chebyshev polynomials through degree `N` are discretely orthogonal in the actual
Chebyshev Lobatto rule. The two boundary modes have squared norm `π`; the other modes
have squared norm `π/2`. Source: Gautschi (2004), Theorem 1.23 and Example 1.50.
atlas: gauss-radau-lobatto (partial) -/
theorem sum_chebyshevLobattoWeight_mul_eval_T_mul_eval_T {N : ℕ} (hN : 0 < N)
    (i k : ℕ) (hi : i ≤ N) (hk : k ≤ N) :
    (∑ j ∈ range (N + 1), (π * lobattoEndpointWeight N j / N) *
      (T ℝ i).eval (node N j) * (T ℝ k).eval (node N j)) =
      if i = k then (if i = 0 ∨ i = N then π else π / 2) else 0 := by
  by_cases htop : i = N ∧ k = N
  · rw [htop.1, htop.2]
    simp only [ite_true, or_true]
    have hs (j : ℕ) : (T ℝ N).eval (node N j) ^ 2 = 1 := by
      rw [node, T_real_cos]
      norm_cast
      rw [show (N : ℝ) * (j * π / N) = j * π by
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp]
      have h := cos_sq_add_sin_sq ((j : ℝ) * π)
      rw [sin_nat_mul_pi, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at h
      exact h
    calc _ = ∑ j ∈ range (N + 1), π * lobattoEndpointWeight N j / N := by
          apply sum_congr rfl
          intro j _
          rw [mul_assoc, ← pow_two, hs j, mul_one]
      _ = π := sum_chebyshevLobattoWeight hN
  · have hdegree : (T ℝ i * T ℝ k).degree < (2 * N : ℕ) := by
      rw [degree_mul, degree_T, degree_T, Int.natAbs_natCast, Int.natAbs_natCast]
      exact_mod_cast (show i + k < 2 * N by omega)
    have h := integral_eval_measureT_eq_chebyshevLobattoRule hN hdegree
    simp only [eval_mul] at h
    rw [show (∑ j ∈ range (N + 1), π * lobattoEndpointWeight N j / N *
        (T ℝ i).eval (node N j) * (T ℝ k).eval (node N j)) =
        ∑ j ∈ range (N + 1), π * lobattoEndpointWeight N j / N *
          ((T ℝ i).eval (node N j) * (T ℝ k).eval (node N j)) from
        sum_congr rfl fun _ _ => mul_assoc _ _ _]
    rw [← h]
    by_cases hik : i = k
    · subst k
      rw [if_pos rfl]
      by_cases hi0 : i = 0
      · subst i
        rw [if_pos (Or.inl rfl)]
        exact integral_eval_T_real_mul_self_measureT_zero
      · rw [if_neg (by aesop)]
        exact integral_T_real_mul_self_measureT_of_ne_zero hi0
    · rw [if_neg hik]
      exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hik

end NLAlib
