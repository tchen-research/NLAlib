import NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries
import NLAlib.Polynomial.Chebyshev.ChebyshevAliasing
import NLAlib.Polynomial.Interpolation.Basic

/-!
# Folding absolutely summable Chebyshev series

The actual grid interpolant has the coefficients obtained by folding frequencies
modulo twice the grid degree. Endpoint fibers are counted once. Its error is
at most twice the Chebyshev coefficient tail.
Atlas: `chebyshev-aliasing`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set
open scoped Topology

namespace NLAlib

/-- Folding an absolutely summable coefficient sequence adds each frequency fiber once.
Source: Trefethen, ATAP, Theorem 4.2; operator rederivations `polyseries:aliasing`.
The fiber formulation includes the distinct endpoint coefficients without double counting. -/
def chebyshevFoldCoeff (a : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ∑' k, if chebyshevAliasIndex n k = j then a k else 0

/-- The finite Chebyshev polynomial formed by folded coefficients.
Source: Trefethen, ATAP, Theorem 4.2; helper for `chebyshev-aliasing`. -/
def chebyshevFoldPolynomial (a : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), C (chebyshevFoldCoeff a n j) * T ℝ (j : ℤ)

/-- A single frequency fiber of an absolutely summable sequence is absolutely summable.
Source: finite partition of an absolute series; helper for `chebyshev-aliasing`. -/
theorem summable_chebyshevFoldFiber {a : ℕ → ℝ} (hs : Summable (fun k => |a k|))
    (n j : ℕ) : Summable (fun k => if chebyshevAliasIndex n k = j then a k else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro k
  by_cases h : chebyshevAliasIndex n k = j <;> simp [h, Real.norm_eq_abs]

/-- A folded polynomial has degree at most the grid degree.
Source: Trefethen, ATAP, Theorem 4.2; helper for `chebyshev-aliasing`. -/
theorem degree_chebyshevFoldPolynomial_le (a : ℕ → ℝ) (n : ℕ) :
    (chebyshevFoldPolynomial a n).degree ≤ n := by
  unfold chebyshevFoldPolynomial
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
  rw [C_mul']
  refine (degree_smul_le _ _).trans ?_
  rw [degree_T, Int.natAbs_natCast]
  exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)

/-- The folded finite polynomial evaluates to the series of folded frequencies.
Source: finite partition of an absolute series; helper for `chebyshev-aliasing`. -/
theorem hasSum_mul_eval_T_alias {a : ℕ → ℝ} (hs : Summable (fun k => |a k|))
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    HasSum (fun k => a k * (T ℝ (chebyshevAliasIndex n k : ℤ)).eval x)
      ((chebyshevFoldPolynomial a n).eval x) := by
  have hj : ∀ j ∈ range (n + 1), HasSum
      (fun k => (if chebyshevAliasIndex n k = j then a k else 0) * (T ℝ (j : ℤ)).eval x)
      (chebyshevFoldCoeff a n j * (T ℝ (j : ℤ)).eval x) := by
    intro j hj
    exact (summable_chebyshevFoldFiber hs n j).hasSum.mul_right _
  have h := hasSum_sum hj
  convert h using 1
  · funext k
    rw [sum_eq_single (chebyshevAliasIndex n k)]
    · simp
    · intro j hj hne
      simp [hne.symm]
    · intro hnot
      exact False.elim (hnot (mem_range.mpr (Nat.lt_succ_of_le (chebyshevAliasIndex_le hn k))))
  · simp only [chebyshevFoldPolynomial, eval_finsetSum, eval_mul, eval_C]

/-- The actual interpolant of a continuous function with absolute Chebyshev coefficients
is its finite folded-coefficient polynomial.
Source: Trefethen, ATAP, Theorems 4.1 and 4.2.
atlas: chebyshev-aliasing (partial) -/
theorem chebyshevInterpolant_eq_foldPolynomial {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) {n : ℕ} (hn : 0 < n) :
    chebyshevInterpolant f n = chebyshevFoldPolynomial (chebyshevCoeff f) n := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ (chebyshev_node_injOn n)
  · have hdegree := degree_chebyshevFoldPolynomial_le (chebyshevCoeff f) n
    rw [card_range]
    exact hdegree.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  · intro j hj
    have h := hasSum_mul_eval_T_alias hs hn (node n j)
    have hterm : ∀ k,
        chebyshevCoeff f k * (T ℝ (chebyshevAliasIndex n k : ℤ)).eval (node n j) =
          chebyshevCoeff f k * (T ℝ (k : ℤ)).eval (node n j) := by
      intro k
      rw [eval_T_node_eq_eval_T_alias hn k j]
    simp_rw [hterm] at h
    exact h.unique (hasSum_chebyshevCoeff_mul_eval_T hf hs node_mem_Icc)

/-- The interpolant's genuine Chebyshev coefficient is exactly its folded frequency fiber.
This is the aliasing coefficient formula for every index, including both endpoint fibers.
Source: Trefethen, ATAP, Theorem 4.2; operator rederivations `polyseries:aliasing`.
atlas: chebyshev-aliasing (partial) -/
theorem chebyshevCoeff_eval_interpolant_eq_foldCoeff {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    chebyshevCoeff (chebyshevInterpolant f n).eval j =
      if j ≤ n then chebyshevFoldCoeff (chebyshevCoeff f) n j else 0 := by
  rw [chebyshevInterpolant_eq_foldPolynomial hf hs hn]
  simp only [chebyshevFoldPolynomial, C_mul']
  exact chebyshevCoeff_eval_sum_smul_T _ _ _

/-- Interpolation leaves low Chebyshev frequencies unchanged.
Source: Trefethen, ATAP, Theorem 4.1; helper for `chebyshev-aliasing`. -/
theorem chebyshevAliasIndex_eq_self_of_le {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    chebyshevAliasIndex n k = k := by
  unfold chebyshevAliasIndex
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The grid interpolant error is bounded by twice the absolute Chebyshev coefficient tail.
Source: Trefethen, ATAP, Theorem 4.2. Together with the fiber formula this proves the
summable-coefficient aliasing assertion, including its endpoint normalization.
atlas: chebyshev-aliasing -/
theorem abs_sub_eval_chebyshevInterpolant_le_two_mul_tsum {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : Summable (fun k => |chebyshevCoeff f k|)) {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |f x - (chebyshevInterpolant f n).eval x| ≤
      2 * ∑' j, |chebyshevCoeff f (j + (n + 1))| := by
  let u : ℕ → ℝ := fun k => chebyshevCoeff f k *
    ((T ℝ (k : ℤ)).eval x - (T ℝ (chebyshevAliasIndex n k : ℤ)).eval x)
  have hu : HasSum u (f x - (chebyshevInterpolant f n).eval x) := by
    have h := (hasSum_chebyshevCoeff_mul_eval_T hf hs hx).sub (hasSum_mul_eval_T_alias hs hn x)
    rw [← chebyshevInterpolant_eq_foldPolynomial hf hs hn] at h
    simpa only [u, mul_sub] using h
  have hzero : ∑ k ∈ range (n + 1), u k = 0 := by
    apply sum_eq_zero
    intro k hk
    dsimp [u]
    rw [chebyshevAliasIndex_eq_self_of_le hn (Nat.le_of_lt_succ (mem_range.mp hk)),
      sub_self, mul_zero]
  have hsplit := hu.summable.sum_add_tsum_nat_add (n + 1)
  rw [hzero, zero_add, hu.tsum_eq] at hsplit
  have hterm : ∀ j, ‖u (j + (n + 1))‖ ≤ 2 * |chebyshevCoeff f (j + (n + 1))| := by
    intro j
    have hT := abs_eval_T_real_le_one ((j + (n + 1) : ℕ) : ℤ) (abs_le.mpr hx)
    have hI := abs_eval_T_real_le_one (chebyshevAliasIndex n (j + (n + 1)) : ℤ) (abs_le.mpr hx)
    have hsum : |(T ℝ ((j + (n + 1) : ℕ) : ℤ)).eval x -
        (T ℝ (chebyshevAliasIndex n (j + (n + 1)) : ℤ)).eval x| ≤ 2 := by
      have h := abs_sub ((T ℝ ((j + (n + 1) : ℕ) : ℤ)).eval x)
        ((T ℝ (chebyshevAliasIndex n (j + (n + 1)) : ℤ)).eval x)
      linarith
    dsimp [u]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hstail := ((summable_nat_add_iff (n + 1)).mpr hs).mul_left 2
  have hnorm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hstail
  rw [← hsplit, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hterm hstail).trans_eq
    (tsum_mul_left))

end NLAlib
