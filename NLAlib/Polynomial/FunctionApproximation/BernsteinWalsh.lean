import NLAlib.Polynomial.FunctionApproximation.EllipseGeometry
import Mathlib.Analysis.Complex.AbsMax

/-!
# Bernstein–Walsh growth on an ellipse

A reversed Joukowski substitution is an ordinary polynomial. Applying maximum
modulus on the unit disk gives the exact growth rate `bernstein-walsh-ellipse`.
-/

noncomputable section

open Polynomial Set Finset Complex Metric

namespace NLAlib

private def joukowskiReversePoly (p : ℂ[X]) (n : ℕ) : ℂ[X] :=
  ∑ j ∈ range (n + 1), C (p.coeff j / 2 ^ j) * X ^ (n - j) * (1 + X ^ 2) ^ j

private theorem eval_joukowskiReversePoly {p : ℂ[X]} {n : ℕ} (hp : p.degree ≤ n)
    {v : ℂ} (hv : v ≠ 0) :
    (joukowskiReversePoly p n).eval v = v ^ n * p.eval (joukowski v) := by
  have hn : p.natDegree < n + 1 := Nat.lt_succ_of_le (natDegree_le_of_degree_le hp)
  rw [Polynomial.eval_eq_sum_range' hn, Finset.mul_sum]
  simp only [joukowskiReversePoly, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, eval_add, eval_one]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hpow : v ^ n = v ^ (n - j) * v ^ j := by rw [← pow_add, Nat.sub_add_cancel hjn]
  have hJ : joukowski v = (1 + v ^ 2) / (2 * v) := by
    dsimp [joukowski]
    field_simp
    ring
  rw [hpow, hJ, div_pow, mul_pow]
  field_simp

/-- Bernstein–Walsh growth in the Joukowski coordinate: a degree-`n` complex
polynomial bounded by `M` on the real unit interval grows by at most `|w|^n`.
Source: Trefethen, ATAP, Ch. 8; operator derivations §5.
atlas: bernstein-walsh-ellipse -/
theorem norm_eval_joukowski_le_mul_pow {p : ℂ[X]} {n : ℕ} {M : ℝ}
    (hp : p.degree ≤ n) (hM : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M)
    {w : ℂ} (hw : 1 ≤ ‖w‖) : ‖p.eval (joukowski w)‖ ≤ M * ‖w‖ ^ n := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  let q := joukowskiReversePoly p n
  have hqbound : ∀ v ∈ frontier (ball (0 : ℂ) 1), ‖q.eval v‖ ≤ M := by
    intro v hv
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hv
    have hvnorm : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; norm_num)
    have hre : v.re ∈ Icc (-1 : ℝ) 1 := by
      exact abs_le.mp (by simpa only [hvnorm] using Complex.abs_re_le_norm v)
    rw [show q = joukowskiReversePoly p n from rfl, eval_joukowskiReversePoly hp hv0,
      norm_mul, norm_pow, hvnorm, one_pow, one_mul, joukowski_eq_re_of_norm_eq_one hvnorm]
    exact hM v.re hre
  have hdiff : DiffContOnCl ℂ (fun z => q.eval z) (ball (0 : ℂ) 1) :=
    ⟨q.differentiable.differentiableOn, q.continuous.continuousOn⟩
  have hmem : w⁻¹ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simp only [mem_closedBall, dist_zero_right, norm_inv]
    exact (inv_le_one₀ (norm_pos_iff.mpr hw0)).mpr hw
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1)) hdiff hqbound hmem
  rw [show q = joukowskiReversePoly p n from rfl,
    eval_joukowskiReversePoly hp (inv_ne_zero hw0), norm_mul, norm_pow, norm_inv,
    joukowski_inv, inv_pow] at hbound
  have hscaled : ‖p.eval (joukowski w)‖ / ‖w‖ ^ n ≤ M := by
    simpa only [div_eq_mul_inv, mul_comm] using hbound
  exact (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hw0) n)).mp hscaled

/-- A degree-`n` complex polynomial bounded on the real unit interval is at most
`Mρ^n` throughout the filled Bernstein ellipse, including its boundary.
Source: Trefethen, ATAP, Ch. 8; operator derivations §5.
atlas: bernstein-walsh-ellipse -/
theorem norm_eval_le_mul_pow_of_mem_filledBernsteinEllipse {p : ℂ[X]} {n : ℕ}
    {M ρ : ℝ} (hp : p.degree ≤ n)
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M)
    {z : ℂ} (hz : z ∈ filledBernsteinEllipse ρ) : ‖p.eval z‖ ≤ M * ρ ^ n := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨by norm_num, by norm_num⟩)
  exact (norm_eval_joukowski_le_mul_pow hp hM hw.1).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw.2 n) hM0)

end NLAlib
