import NLAlib.ForMathlib.Analysis.LobattoKernel
import NLAlib.Polynomial.Chebyshev.ChebyshevAliasing
import NLAlib.Polynomial.BestApproximation.Basic

/-!
# Finite cosine expansion of Lobatto Lagrange cardinals

The endpoint-half discrete cosine sum gives exactly the polynomial cardinal functions at
Chebyshev extrema. Source: focused rederivations, Theorem `thm:lobatto`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Real Finset

namespace NLAlib

/-- Endpoint-half weights on the extrema grid.
Source: the finite cosine cardinal kernel. -/
def lobattoEndpointWeight (n j : ℕ) : ℝ := if j = 0 ∨ j = n then 1 / 2 else 1

/-- The finite DCT expansion of a Chebyshev-extrema cardinal polynomial.
Source: focused rederivations, Theorem `thm:lobatto`. -/
def lobattoCardinal (n j : ℕ) : ℝ[X] :=
  (lobattoEndpointWeight n j / n) •
    (1 + ∑ k ∈ range (n - 1),
      (2 * cos ((k + 1 : ℕ) * (j * π / n))) • T ℝ (k + 1 : ℕ) +
      cos ((n : ℝ) * (j * π / n)) • T ℝ n)

/-- The DCT cardinal expansion has degree at most the interpolation cutoff.
Source: the degrees of the individual Chebyshev terms. -/
theorem degree_lobattoCardinal_le (n j : ℕ) : (lobattoCardinal n j).degree ≤ n := by
  apply (degree_smul_le _ _).trans
  refine (degree_add_le _ _).trans (max_le ?_ ?_)
  · refine (degree_add_le _ _).trans (max_le ?_ ?_)
    · exact (show (1 : ℝ[X]).degree ≤ n by simp)
    · apply (degree_sum_le _ _).trans
      apply Finset.sup_le
      intro k hk
      apply (degree_smul_le _ _).trans
      rw [degree_T, Int.natAbs_natCast]
      exact_mod_cast (show k + 1 ≤ n by have := mem_range.mp hk; omega)
  · apply (degree_smul_le _ _).trans
    rw [degree_T, Int.natAbs_natCast]

/-- At a cosine point, the polynomial cardinal is the paired finite trigonometric kernel.
Source: finite product-to-sum. -/
theorem eval_lobattoCardinal_cos (n j : ℕ) (t : ℝ) :
    (lobattoCardinal n j).eval (cos t) = lobattoEndpointWeight n j *
      (lobattoKernel n (t - j * π / n) + lobattoKernel n (t + j * π / n)) := by
  simp only [lobattoCardinal, eval_smul, eval_add, eval_one, eval_finsetSum,
    smul_eq_mul, T_real_cos, Int.cast_natCast]
  dsimp [lobattoKernel]
  simp only [mul_sub, mul_add, cos_sub, cos_add]
  have hsum : ∀ k : ℕ,
      2 * cos ((k + 1 : ℕ) * (j * π / n)) * cos ((k + 1 : ℕ) * t) =
      cos ((k + 1 : ℕ) * t) * cos ((k + 1 : ℕ) * (j * π / n)) +
        sin ((k + 1 : ℕ) * t) * sin ((k + 1 : ℕ) * (j * π / n)) +
      (cos ((k + 1 : ℕ) * t) * cos ((k + 1 : ℕ) * (j * π / n)) -
        sin ((k + 1 : ℕ) * t) * sin ((k + 1 : ℕ) * (j * π / n))) := by
    intro k; ring
  simp_rw [hsum, Finset.sum_add_distrib]
  ring

private theorem kernel_grid_sub {n i j : ℕ} (hn : 0 < n) (hi : i ≤ n) (hj : j ≤ n) :
    lobattoKernel n ((i : ℝ) * π / n - j * π / n) = if i = j then 1 else 0 := by
  split_ifs with hij
  · simp [hij, lobattoKernel_zero hn]
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd : j - i < 2 * n := by omega
      have hd0 : 0 < j - i := by omega
      rw [show (i : ℝ) * π / n - j * π / n = -((j - i : ℕ) * π / n) by
        rw [Nat.cast_sub hlt.le]; ring, lobattoKernel_neg]
      exact lobattoKernel_grid_zero hn hd0 hd
    · rw [show (i : ℝ) * π / n - j * π / n = (i - j : ℕ) * π / n by
        rw [Nat.cast_sub hgt.le]; ring]
      exact lobattoKernel_grid_zero hn (by omega) (by omega)

private theorem kernel_grid_add {n i j : ℕ} (hn : 0 < n) (hi : i ≤ n) (hj : j ≤ n) :
    lobattoKernel n ((i : ℝ) * π / n + j * π / n) =
      if i = j ∧ (j = 0 ∨ j = n) then 1 else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases hz : i + j = 0
  · have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    simp [hi0, hj0, lobattoKernel_zero hn]
  by_cases htop : i + j = 2 * n
  · have hin : i = n := by omega
    have hjn : j = n := by omega
    have ha : (n : ℝ) * π / n + n * π / n = 2 * π := by field_simp; ring
    rw [hin, hjn, ha]
    simpa only [zero_add, lobattoKernel_zero hn, true_and, or_true, ite_true] using lobattoKernel_periodic n 0
  · rw [show (i : ℝ) * π / n + j * π / n = (i + j : ℕ) * π / n by push_cast; ring,
      lobattoKernel_grid_zero hn (by omega) (by omega)]
    have hne : ¬(i = j ∧ (j = 0 ∨ j = n)) := by
      rintro ⟨hij, h0 | hn'⟩ <;> omega
    simp [hne]

/-- The DCT expansion has the exact cardinal nodal values.
Source: the cardinal finite trigonometric kernel. -/
theorem eval_lobattoCardinal_node {n i j : ℕ} (hn : 0 < n) (hi : i ≤ n) (hj : j ≤ n) :
    (lobattoCardinal n j).eval (node n i) = if i = j then 1 else 0 := by
  rw [node, eval_lobattoCardinal_cos, kernel_grid_sub hn hi hj, kernel_grid_add hn hi hj]
  by_cases hij : i = j
  · rw [if_pos hij]
    simp only [hij, true_and, lobattoEndpointWeight]
    split_ifs <;> norm_num
  · simp [hij]

/-- The finite endpoint-half DCT expression is exactly Mathlib's Lagrange cardinal polynomial.
Source: focused rederivations, Theorem `thm:lobatto`.
atlas: lebesgue-constant-chebyshev (partial) -/
theorem lobattoCardinal_eq_basis {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    lobattoCardinal n j = Lagrange.basis (range (n + 1)) (node n) j := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (range (n + 1)) (chebyshev_node_injOn n)
  · exact (degree_lobattoCardinal_le n j).trans_lt (by rw [card_range]; exact_mod_cast Nat.lt_succ_self n)
  · rw [Lagrange.degree_basis (chebyshev_node_injOn n) (by simpa using hj), card_range]
    exact_mod_cast Nat.lt_succ_self n
  · intro i hi
    rw [eval_lobattoCardinal_node hn (by simpa using hi) hj]
    split_ifs with hij
    · subst i
      exact (Lagrange.eval_basis_self (chebyshev_node_injOn n) hi).symm
    · exact (Lagrange.eval_basis_of_ne (Ne.symm hij) hi).symm




/-- The canonical extrema grid indexed by `Fin` has distinct nodes.
Source: Mathlib `strictAntiOn_node`. -/
theorem injective_chebyshev_extrema_fin (n : ℕ) :
    Function.Injective (fun j : Fin (n + 1) => node n j) := by
  intro i j hij
  apply Fin.ext
  exact chebyshev_node_injOn n (by simpa using i.isLt) (by simpa using j.isLt) hij

/-- The finite cosine expression also identifies the bundled finite-index cardinal basis.
Source: the exact DCT cardinal expansion. -/
theorem lobattoCardinal_eq_basis_fin {n : ℕ} (hn : 0 < n) (j : Fin (n + 1)) :
    lobattoCardinal n j = Lagrange.basis univ (fun i : Fin (n + 1) => node n i) j := by
  have hv := (injective_chebyshev_extrema_fin n).injOn (s := (univ : Finset (Fin (n + 1))))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq univ hv
  · exact (degree_lobattoCardinal_le n j).trans_lt (by simp only [card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_self n)
  · rw [Lagrange.degree_basis hv (mem_univ j), card_univ, Fintype.card_fin]
    exact_mod_cast (show n + 1 - 1 < n + 1 by omega)
  · intro i hi
    rw [eval_lobattoCardinal_node hn (by omega) (by omega)]
    by_cases hij : i = j
    · subst i
      rw [if_pos rfl, Lagrange.eval_basis_self hv (mem_univ j)]
    · rw [if_neg (by exact fun h => hij (Fin.ext h))]
      exact (Lagrange.eval_basis_of_ne (v := fun i : Fin (n + 1) => node n i) (Ne.symm hij) hi).symm

end NLAlib
