import NLAlib.Polynomial.AnalyticApproximation
import NLAlib.Polynomial.ChebyshevAliasing

/-!
# Analytic interpolation on the canonical Chebyshev grid

The interpolant is Mathlib's actual Lagrange polynomial at `cos(jπ/N)`, `0≤j≤N`.
Aliasing controls each interpolated Chebyshev frequency and yields the factor-four rate.
-/

noncomputable section

open Complex Polynomial Polynomial.Chebyshev Finset Real
open scoped Topology

namespace NLAlib

/-- The actual Lagrange interpolant on the `(N+1)`-point canonical Chebyshev extrema grid.
Mathlib totalizes the `N=0` grid at the point `1`; this convention is made explicit.
Source: Trefethen, ATAP, Chapters 2 and 8 (`chebyshev-approx-analytic`, definition). -/
def chebyshevAnalyticInterpolant (F : ℂ → ℂ) (N : ℕ) : ℝ[X] :=
  Lagrange.interpolate (range (N + 1)) (node N) (fun j => (F (node N j)).re)

/-- The actual canonical grid interpolant has degree at most `N`.
Source: Trefethen, ATAP, Chapters 2 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem degree_chebyshevAnalyticInterpolant_le (F : ℂ → ℂ) (N : ℕ) :
    (chebyshevAnalyticInterpolant F N).degree ≤ N := by
  have h := Lagrange.degree_interpolate_lt (fun j => (F (node N j)).re) (chebyshev_node_injOn N)
  rw [card_range] at h
  apply degree_le_of_natDegree_le
  rcases eq_or_ne (chebyshevAnalyticInterpolant F N) 0 with hzero | hzero
  · simp [hzero]
  · have hn := (natDegree_lt_iff_degree_lt hzero).mpr h
    exact Nat.le_of_lt_succ hn

/-- The canonical polynomial takes the original function's values at every grid point.
Source: Trefethen, ATAP, Chapters 2 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem eval_chebyshevAnalyticInterpolant_node (F : ℂ → ℂ) (N j : ℕ) (hj : j ≤ N) :
    (chebyshevAnalyticInterpolant F N).eval (node N j) = (F (node N j)).re := by
  exact Lagrange.eval_interpolate_at_node _ (chebyshev_node_injOn N) (mem_range.mpr (by omega))

/-- Low frequencies are interpolated exactly on the canonical grid.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
theorem interpolate_eval_T_node_eq_T_of_le {N k : ℕ} (hk : k ≤ N) :
    Lagrange.interpolate (range (N + 1)) (node N)
      (fun j => (T ℝ (k : ℤ)).eval (node N j)) = T ℝ (k : ℤ) := by
  symm
  apply Lagrange.eq_interpolate (chebyshev_node_injOn N)
  rw [degree_T, Int.natAbs_natCast, card_range]
  exact_mod_cast Nat.lt_succ_of_le hk

/-- Interpolated Chebyshev frequencies are bounded by one, including the totalized zero grid.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
theorem abs_eval_interpolate_eval_T_node_le_one_all (N k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Lagrange.interpolate (range (N + 1)) (node N)
      (fun j => (T ℝ (k : ℤ)).eval (node N j))).eval x| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [range_one, node]
  · exact abs_eval_interpolate_eval_T_node_le_one hN k hx

/-- The actual interpolant is obtained by interpolating the genuinely reconstructed
Chebyshev series term by term; there are only finitely many nodal values.
Source: Trefethen, ATAP, Theorems 3.1(a) and 4.2 (`chebyshev-approx-analytic`, helper). -/
theorem hasSum_chebyshevAnalyticCoeff_mul_eval_interpolate_T_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) (N : ℕ) (x : ℝ) :
    HasSum (fun k : ℕ => chebyshevAnalyticCoeff F k *
      (Lagrange.interpolate (range (N + 1)) (node N)
        (fun j => (T ℝ (k : ℤ)).eval (node N j))).eval x)
      ((chebyshevAnalyticInterpolant F N).eval x) := by
  have hj : ∀ j ∈ range (N + 1), HasSum (fun k : ℕ =>
      (chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval (node N j)) *
        (Lagrange.basis (range (N + 1)) (node N) j).eval x)
      ((F (node N j)).re * (Lagrange.basis (range (N + 1)) (node N) j).eval x) := by
    intro j hj
    exact (hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse hρ hFd hM node_mem_Icc).mul_right _
  have h := hasSum_sum hj
  convert h using 1 <;> try rfl
  · funext k
    simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  · simp only [chebyshevAnalyticInterpolant, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]

/-- The actual canonical Chebyshev-grid interpolant has the sharp analytic factor-four
geometric error bound, from original open-ellipse holomorphy without a boundary extension.
Source: Trefethen, ATAP, Theorem 8.2; the finite frequency folding is Theorem 4.1.
atlas: chebyshev-approx-analytic (partial) -/
theorem abs_re_sub_eval_chebyshevAnalyticInterpolant_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) (N : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(F x).re - (chebyshevAnalyticInterpolant F N).eval x| ≤
      4 * M / ρ ^ N / (ρ - 1) := by
  let I : ℕ → ℝ := fun k => (Lagrange.interpolate (range (N + 1)) (node N)
    (fun j => (T ℝ (k : ℤ)).eval (node N j))).eval x
  let u : ℕ → ℝ := fun k => chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval x -
    chebyshevAnalyticCoeff F k * I k
  have hu : HasSum u ((F x).re - (chebyshevAnalyticInterpolant F N).eval x) :=
    (hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse hρ hFd hM hx).sub
      (hasSum_chebyshevAnalyticCoeff_mul_eval_interpolate_T_of_open_ellipse hρ hFd hM N x)
  have hzero : ∑ k ∈ range (N + 1), u k = 0 := by
    apply sum_eq_zero
    intro k hk
    dsimp [u, I]
    rw [interpolate_eval_T_node_eq_T_of_le (Nat.le_of_lt_succ (mem_range.mp hk)), sub_self]
  have hsplit := hu.summable.sum_add_tsum_nat_add (N + 1)
  rw [hzero, zero_add, hu.tsum_eq] at hsplit
  have hq : |ρ⁻¹| < 1 := by
    rw [abs_of_pos (by positivity : 0 < ρ⁻¹)]
    exact (inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ
  have hgeom : Summable (fun i : ℕ => 4 * M / ρ ^ (i + (N + 1))) := by
    have h := ((summable_geometric_of_abs_lt_one hq).mul_right ((ρ⁻¹) ^ (N + 1))).mul_left (4 * M)
    convert h using 1 <;> try rfl
    funext i
    rw [div_eq_mul_inv, ← inv_pow, pow_add]
  have hterm : ∀ i : ℕ, ‖u (i + (N + 1))‖ ≤ 4 * M / ρ ^ (i + (N + 1)) := by
    intro i
    let k := i + (N + 1)
    have hc := abs_chebyshevAnalyticCoeff_le_of_open_ellipse hρ hFd hM
      (k := k) (by dsimp [k]; omega)
    have hT := abs_eval_T_real_le_one (k : ℤ) (abs_le.mpr hx)
    have hI : |I k| ≤ 1 := abs_eval_interpolate_eval_T_node_le_one_all N k hx
    have hsum : |(T ℝ (k : ℤ)).eval x - I k| ≤ 2 := by
      have h := abs_sub ((T ℝ (k : ℤ)).eval x) (I k)
      linarith
    change |chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval x -
      chebyshevAnalyticCoeff F k * I k| ≤ _
    rw [← mul_sub, abs_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (abs_nonneg (chebyshevAnalyticCoeff F k))
    have hc2 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2 by norm_num)
    calc |chebyshevAnalyticCoeff F k| * |(T ℝ (k : ℤ)).eval x - I k|
        ≤ |chebyshevAnalyticCoeff F k| * 2 := hmul
      _ = 2 * |chebyshevAnalyticCoeff F k| := mul_comm _ _
      _ ≤ 2 * (2 * M / ρ ^ k) := hc2
      _ = 4 * M / ρ ^ (i + (N + 1)) := by dsimp [k]; ring
  have hnorm := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm hgeom
  rw [← hsplit, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hterm hgeom).trans_eq ?_)
  have hterm_eq : ∀ i : ℕ, 4 * M / ρ ^ (i + (N + 1)) =
      4 * M * ((ρ⁻¹) ^ i * (ρ⁻¹) ^ (N + 1)) := by
    intro i
    rw [div_eq_mul_inv, ← inv_pow, pow_add]
  simp_rw [hterm_eq]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_abs_lt_one hq, pow_succ]
  simp only [inv_pow]
  field_simp [ne_of_gt (zero_lt_one.trans hρ)]

/-- Both canonical analytic Chebyshev approximations satisfy their exact source constants:
the coefficient truncation has error `2Mρ⁻ᴺ/(ρ-1)`, and the actual `(N+1)`-point grid
interpolant has error `4Mρ⁻ᴺ/(ρ-1)`. Both polynomials have degree at most `N`.
Source: Trefethen, ATAP, Theorem 8.2; original open-ellipse assumptions, with the `N=0`
grid convention inherited explicitly from Mathlib's `node`.
atlas: chebyshev-approx-analytic -/
theorem degree_le_and_abs_sub_chebyshev_approximations_le_of_open_ellipse
    {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ x ∈ Set.Icc (-1 : ℝ) 1, F x = (f x : ℂ)) (N : ℕ) :
    (chebyshevAnalyticTrunc F N).degree ≤ N ∧ (chebyshevAnalyticInterpolant F N).degree ≤ N ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |f x - (chebyshevAnalyticTrunc F N).eval x| ≤ 2 * M / ρ ^ N / (ρ - 1) ∧
        |f x - (chebyshevAnalyticInterpolant F N).eval x| ≤ 4 * M / ρ ^ N / (ρ - 1) := by
  refine ⟨degree_chebyshevAnalyticTrunc_le F N, degree_chebyshevAnalyticInterpolant_le F N, ?_⟩
  intro x hx
  have h1 := abs_re_sub_eval_chebyshevAnalyticTrunc_le_of_open_ellipse hρ hFd hM N hx
  have h2 := abs_re_sub_eval_chebyshevAnalyticInterpolant_le_of_open_ellipse hρ hFd hM N hx
  rw [hmatch x hx, Complex.ofReal_re] at h1 h2
  exact ⟨h1, h2⟩

end NLAlib
