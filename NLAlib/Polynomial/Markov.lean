import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Taylor
import NLAlib.Polynomial.Chebyshev

/-!
# Markov brothers' and Bernstein's inequalities

Layer 0 (no matrices). Derivative bounds for real polynomials bounded on `[−1, 1]`:

* `abs_eval_le_mul_of_forall_sqrt_one_sub_sq_mul_abs_eval_le` (Schur's inequality): if
  `deg r < q` and `√(1 − y²) |r(y)| ≤ M` on `[−1, 1]`, then `|r| ≤ q M` on `[−1, 1]`.
* `abs_eval_derivative_le_div_sqrt_of_forall_abs_eval_le` (Bernstein's inequality): if
  `deg p ≤ q` and `|p| ≤ M` on `[−1, 1]`, then `|p'(x)| ≤ q M / √(1 − x²)` for `|x| < 1`.
* `abs_eval_derivative_le_sq_mul_of_forall_abs_eval_le` (Markov brothers' inequality, sharp
  constant): `|p'(x)| ≤ q² M` on `[−1, 1]`; and the interval form
  `abs_eval_derivative_le_two_mul_sq_div_mul_of_forall_abs_eval_le` with constant `2 q²/(b − a)`.

Proof route: Schur's inequality by Lagrange interpolation at the zeros of `T_q` (Mathlib's
`Polynomial.Chebyshev.roots_T_real`, `Lagrange.eq_interpolate`, `Lagrange.derivative_nodal`);
Bernstein by applying Schur at `y = 1` to the polynomial `r` with
`p(cos(θ₀ + θ)) − p(cos(θ₀ − θ)) = −2 sin θ · r(cos θ)` (built from Hasse derivatives, no
trigonometric polynomials needed); Markov from Bernstein plus Schur applied to `p'`.

Atlas: `markov-brothers`, `bernstein-polynomial-inequality`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Real Finset

namespace NLAlib

namespace Markov

/-- The zeros of `T_q`. -/
private def zero (q k : ℕ) : ℝ := cos ((2 * k + 1) * π / (2 * q))

private lemma angle_mem {q k : ℕ} (hk : k < q) :
    0 < (2 * k + 1) * π / (2 * q) ∧ (2 * k + 1) * π / (2 * q) < π := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hk' : (2 * k + 1 : ℝ) < 2 * q := by
    have : (k : ℝ) + 1 ≤ q := by exact_mod_cast hk
    linarith
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

private lemma injOn_zero (q : ℕ) : Set.InjOn (zero q) (range q) :=
  (Finset.range q).nodup_map_iff_injOn.mp (roots_T_real_nodup q)

private lemma eval_T_zero {q k : ℕ} (hk : k < q) : (T ℝ q).eval (zero q k) = 0 := by
  have : zero q k ∈ (T ℝ q).roots := by
    rw [roots_T_real]; simp only [Finset.mem_val, Finset.mem_image]
    exact ⟨k, Finset.mem_range.mpr hk, rfl⟩
  exact (mem_roots'.mp this).2

private lemma T_eq_C_mul_nodal (q : ℕ) :
    Chebyshev.T ℝ q = C (2 ^ (q - 1) : ℝ) * Lagrange.nodal (range q) (zero q) := by
  refine Polynomial.eq_of_degree_le_of_eval_index_eq (range q) (injOn_zero q) ?_ ?_ ?_ ?_
  · simp [Chebyshev.degree_T]
  · rw [degree_C_mul (by positivity), Lagrange.degree_nodal, Chebyshev.degree_T]
    simp
  · rw [leadingCoeff_C_mul_of_isUnit (by simp), Lagrange.nodal_monic.leadingCoeff,
      Chebyshev.leadingCoeff_T]
    simp
  · intro i hi
    rw [eval_mul, Lagrange.eval_nodal_at_node hi, mul_zero]
    exact eval_T_zero (Finset.mem_range.mp hi)

private lemma eval_derivative_T (q : ℕ) (x : ℝ) :
    (derivative (T ℝ q)).eval x = q * (U ℝ ((q : ℤ) - 1)).eval x := by
  rw [T_derivative_eq_U, eval_mul]
  simp

private lemma sin_angle_eq_sqrt {q k : ℕ} (hk : k < q) :
    sin ((2 * k + 1) * π / (2 * q)) = √(1 - zero q k ^ 2) :=
  sin_eq_sqrt_one_sub_cos_sq (angle_mem hk).1.le (angle_mem hk).2.le

/-- At a zero `ξ_k = cos θ_k` of `T_q`, `|T_q'(ξ_k)| · sin θ_k = q`. -/
private lemma abs_eval_derivative_T_zero_mul_sqrt {q k : ℕ} (hk : k < q) :
    |(derivative (T ℝ q)).eval (zero q k)| * √(1 - zero q k ^ 2) = q := by
  set θ := (2 * k + 1) * π / (2 * q) with hθ
  have hU := U_real_cos θ ((q : ℤ) - 1)
  have hT := T_real_cos θ (q : ℤ)
  have h0 : (T ℝ q).eval (cos θ) = 0 := eval_T_zero hk
  rw [h0] at hT
  have hsin : |sin ((q : ℝ) * θ)| = 1 := by
    have := sin_sq_add_cos_sq ((q : ℝ) * θ)
    push_cast at hT
    rw [← hT] at this
    have h1 : sin ((q : ℝ) * θ) ^ 2 = 1 := by simpa using this
    rcases sq_eq_one_iff.mp h1 with h | h <;> simp [h]
  have hpos : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi (angle_mem hk).1.le (angle_mem hk).2.le
  rw [← sin_angle_eq_sqrt hk, eval_derivative_T]
  change |(q : ℝ) * (U ℝ ((q : ℤ) - 1)).eval (cos θ)| * sin θ = q
  rw [← abs_of_nonneg hpos, ← abs_mul, mul_assoc, hU]
  push_cast
  rw [sub_add_cancel, abs_mul, hsin]
  simp

private lemma zero_le_zero_zero {q k : ℕ} (hk : k < q) : zero q k ≤ zero q 0 := by
  have h0 := angle_mem (Nat.zero_lt_of_lt hk)
  have hk' := angle_mem hk
  unfold zero
  apply cos_le_cos_of_nonneg_of_le_pi h0.1.le hk'.2.le
  push_cast
  gcongr
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

private lemma eval_basis_eq {q i : ℕ} (hi : i ∈ range q) (y : ℝ) :
    (Lagrange.basis (range q) (zero q) i).eval y =
      Lagrange.nodalWeight (range q) (zero q) i *
        (Lagrange.nodal ((range q).erase i) (zero q)).eval y := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, ← Lagrange.nodal_erase_eq_nodal_div hi,
    eval_mul, eval_C]

/-- Schur's inequality on `[cos(π/(2q)), 1]`, by Lagrange interpolation at the zeros of `T_q`. -/
private lemma abs_eval_le_of_zero_le {q : ℕ} {r : ℝ[X]} {M y : ℝ} (hq : 0 < q)
    (hr : r.degree < q) (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |r.eval y| ≤ M)
    (hy0 : zero q 0 ≤ y) (hy1 : y ≤ 1) : |r.eval y| ≤ q * M := by
  set s := range q
  set v := zero q
  set N := Lagrange.nodal s v
  set c : ℝ := 2 ^ (q - 1) with hc
  have hcpos : 0 < c := by positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hM0 : 0 ≤ M := by
    have := hM 0 (by norm_num)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, sqrt_one,
      one_mul] at this
    exact (abs_nonneg _).trans this
  have hderiv : ∀ x, (derivative (T ℝ q)).eval x = c * (derivative N).eval x := by
    intro x
    rw [T_eq_C_mul_nodal q, derivative_C_mul, eval_mul, eval_C]
  have hinterp : r = Lagrange.interpolate s v (fun i => r.eval (v i)) :=
    Lagrange.eq_interpolate (injOn_zero q) (by simpa [s] using hr)
  -- nonnegativity of the partial nodal polynomials at `y`
  have hNi : ∀ i ∈ s, 0 ≤ (Lagrange.nodal (s.erase i) v).eval y := by
    intro i _
    rw [Lagrange.eval_nodal]
    refine Finset.prod_nonneg fun j hj => ?_
    have hj' : j < q := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    linarith [zero_le_zero_zero hj']
  -- the per-node weight bound
  have hterm : ∀ i ∈ s,
      |r.eval (v i)| * |Lagrange.nodalWeight s v i| ≤ c * M / q := by
    intro i hi
    have hik : i < q := Finset.mem_range.mp hi
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi, abs_inv]
    have hT := abs_eval_derivative_T_zero_mul_sqrt hik
    rw [hderiv, abs_mul, abs_of_pos hcpos] at hT
    set D := |(derivative N).eval (v i)|
    set S := √(1 - zero q i ^ 2)
    have hDpos : D ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_mul] at hT
      exact hqpos.ne' hT.symm
    have hinv : D⁻¹ = c * S / q := by
      rw [eq_div_iff hqpos.ne', ← hT]
      field_simp
    rw [hinv]
    have hSi : S * |r.eval (v i)| ≤ M := hM _ (cos_mem_Icc _)
    calc |r.eval (v i)| * (c * S / q) = c * (S * |r.eval (v i)|) / q := by ring
      _ ≤ c * M / q := by gcongr
  have hsum : (derivative N).eval y = ∑ i ∈ s, (Lagrange.nodal (s.erase i) v).eval y := by
    rw [Lagrange.derivative_nodal, eval_finsetSum]
  have hy : |y| ≤ 1 := by
    rw [abs_le]; constructor
    · have : -1 ≤ zero q 0 := neg_one_le_cos _
      linarith
    · exact hy1
  rw [hinterp, Lagrange.interpolate_apply, eval_finsetSum]
  calc |∑ i ∈ s, (C (r.eval (v i)) * Lagrange.basis s v i).eval y|
      ≤ ∑ i ∈ s, |(C (r.eval (v i)) * Lagrange.basis s v i).eval y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |r.eval (v i)| * |Lagrange.nodalWeight s v i| *
          (Lagrange.nodal (s.erase i) v).eval y := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [eval_mul, eval_C, eval_basis_eq hi, abs_mul, abs_mul, abs_of_nonneg (hNi i hi),
          mul_assoc]
    _ ≤ ∑ i ∈ s, c * M / q * (Lagrange.nodal (s.erase i) v).eval y :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hterm i hi) (hNi i hi)
    _ = M / q * (derivative (T ℝ q)).eval y := by
        rw [← Finset.mul_sum, ← hsum, hderiv]; ring
    _ ≤ M / q * (q : ℝ) ^ 2 := by
        gcongr
        exact (abs_le.mp (abs_eval_derivative_T_real_le hy q)).2
    _ = q * M := by field_simp

/-- Schur's inequality on `[−cos(π/(2q)), cos(π/(2q))]`, where `√(1 − y²) ≥ sin(π/(2q)) ≥ 1/q`. -/
private lemma abs_eval_le_of_abs_le_zero {q : ℕ} {r : ℝ[X]} {M y : ℝ} (hq : 0 < q)
    (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |r.eval y| ≤ M)
    (hy : |y| ≤ zero q 0) : |r.eval y| ≤ q * M := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set α := (2 * ((0 : ℕ) : ℝ) + 1) * π / (2 * q) with hα
  have hα0 : 0 ≤ α := (angle_mem hq).1.le
  have hαeq : α = π / 2 * (1 / q) := by rw [hα]; push_cast; ring
  have hαle : α ≤ π / 2 := by
    rw [hαeq]
    have : 1 / (q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast hq
    nlinarith [pi_pos]
  have hsin : 1 / (q : ℝ) ≤ sin α := by
    have := mul_le_sin hα0 hαle
    calc 1 / (q : ℝ) = 2 / π * α := by rw [hαeq]; field_simp
      _ ≤ _ := this
  have hcos : 0 ≤ cos α := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hαle⟩
  have hy2 : y ^ 2 ≤ cos α ^ 2 := by
    rw [← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hsqrt : sin α ≤ √(1 - y ^ 2) := by
    rw [← sqrt_sq (sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [pi_pos]))]
    apply sqrt_le_sqrt
    nlinarith [sin_sq_add_cos_sq α]
  have hyI : y ∈ Set.Icc (-1 : ℝ) 1 := by
    have : zero q 0 ≤ 1 := cos_le_one _
    exact ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have h1 : 1 / (q : ℝ) * |r.eval y| ≤ M :=
    (mul_le_mul_of_nonneg_right (hsin.trans hsqrt) (abs_nonneg _)).trans (hM y hyI)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hqpos] at h1
  linarith

end Markov

open Markov in
/-- **Schur's inequality.** If `r` has degree `< q` and `√(1 − y²) |r(y)| ≤ M` on `[−1, 1]`, then
`|r(x)| ≤ q M` on `[−1, 1]`.

Source: Rivlin, *Chebyshev Polynomials* (2nd ed., 1990), §2.7 (Schur's lemma); Cheney,
*Introduction to Approximation Theory*, Ch. 3. Proof: for `|x| ≤ cos(π/(2q))` directly from
`√(1 − x²) ≥ sin(π/(2q)) ≥ 1/q`; for `x ≥ cos(π/(2q))` by Lagrange interpolation at the zeros
`ξ_k` of `T_q`, where all partial nodal products are nonnegative and the weights satisfy
`|r(ξ_k)| / |T_q'(ξ_k)| ≤ M/q`, so `|r(x)| ≤ (M/q) T_q'(x) ≤ q M`; the case `x ≤ −cos(π/(2q))` by
reflection. Atlas: auxiliary for `markov-brothers` and `bernstein-polynomial-inequality`.
atlas: schur-polynomial-inequality -/
theorem abs_eval_le_mul_of_forall_sqrt_one_sub_sq_mul_abs_eval_le {q : ℕ} {r : ℝ[X]} {M x : ℝ}
    (hq : 0 < q) (hr : r.degree < q)
    (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |r.eval y| ≤ M)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |r.eval x| ≤ q * M := by
  rcases le_or_gt (zero q 0) x with h | h
  · exact abs_eval_le_of_zero_le hq hr hM h hx.2
  rcases le_or_gt x (-zero q 0) with h' | h'
  · -- reflect
    have hr' : (r.comp (-X)).degree < q := by
      rcases eq_or_ne r 0 with h0 | h0
      · simp [h0]
      have hnat : r.natDegree < q := (natDegree_lt_iff_degree_lt h0).mpr hr
      refine degree_le_natDegree.trans_lt ?_
      have : (r.comp (-X)).natDegree ≤ r.natDegree := by
        have := natDegree_comp_le (p := r) (q := -X)
        simpa using this
      exact_mod_cast this.trans_lt hnat
    have hM' : ∀ y ∈ Set.Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |(r.comp (-X)).eval y| ≤ M := by
      intro y hy
      have := hM (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
      simpa using this
    have := abs_eval_le_of_zero_le (y := -x) hq hr' hM' (by linarith) (by linarith [hx.1])
    simpa using this
  · exact abs_eval_le_of_abs_le_zero hq hM (abs_le.mpr ⟨h'.le, h.le⟩)


namespace Markov

/-- The "odd part" of `θ ↦ p(cos(θ₀ + θ))` divided by `sin θ`, as a polynomial in `cos θ`: with
`a = cos θ₀`, `b = sin θ₀`, it is `−∑_{k odd} b^k (Δ^k p)(a X) (1 − X²)^{(k−1)/2}` where `Δ^k` is
the `k`-th Hasse derivative. -/
private def oddPart (p : ℝ[X]) (a b : ℝ) : ℝ[X] :=
  -∑ k ∈ range (p.natDegree + 1),
    if Odd k then C (b ^ k) * (hasseDeriv k p).comp (C a * X) * (1 - X ^ 2) ^ (k / 2) else 0

private lemma eval_add_eq_sum_hasseDeriv (p : ℝ[X]) (c w : ℝ) :
    p.eval (c + w) = ∑ k ∈ range (p.natDegree + 1), (hasseDeriv k p).eval c * w ^ k := by
  rw [add_comm, ← taylor_eval, eval_eq_sum_range, natDegree_taylor]
  simp [taylor_coeff]

private lemma eval_oddPart (p : ℝ[X]) (a b y : ℝ) :
    (oddPart p a b).eval y = -∑ k ∈ range (p.natDegree + 1),
      if Odd k then b ^ k * (hasseDeriv k p).eval (a * y) * (1 - y ^ 2) ^ (k / 2) else 0 := by
  unfold oddPart
  rw [eval_neg, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [eval_comp]

/-- The defining identity: for `s² = 1 − y²`,
`p(a y − b s) − p(a y + b s) = 2 s · (oddPart p a b)(y)`. -/
private lemma eval_sub_eval_eq_two_mul_oddPart (p : ℝ[X]) (a b : ℝ) {y s : ℝ}
    (hs : s ^ 2 = 1 - y ^ 2) :
    p.eval (a * y - b * s) - p.eval (a * y + b * s) = 2 * s * (oddPart p a b).eval y := by
  rw [sub_eq_add_neg (a * y) (b * s), eval_add_eq_sum_hasseDeriv, eval_add_eq_sum_hasseDeriv,
    ← Finset.sum_sub_distrib, eval_oddPart, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := hk
    rw [Odd.neg_pow ⟨m, rfl⟩, show (2 * m + 1) / 2 = m by omega, ← hs]
    ring
  · rw [Even.neg_pow (Nat.not_odd_iff_even.mp hk)]
    ring

private lemma eval_oddPart_one {p : ℝ[X]} (hp : 0 < p.natDegree) (a b : ℝ) :
    (oddPart p a b).eval 1 = -(b * (derivative p).eval a) := by
  rw [eval_oddPart, Finset.sum_eq_single 1]
  · simp [hasseDeriv_one]
  · intro k _ hk1
    split_ifs with hk
    · obtain ⟨m, rfl⟩ := hk
      have hm : (2 * m + 1) / 2 ≠ 0 := by omega
      simp [zero_pow hm]
    · rfl
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma natDegree_oddPart_le (p : ℝ[X]) (a b : ℝ) :
    (oddPart p a b).natDegree ≤ p.natDegree - 1 := by
  unfold oddPart
  rw [natDegree_neg]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkd : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  split_ifs with hodd
  · have h1 : ((hasseDeriv k p).comp (C a * X)).natDegree ≤ p.natDegree - k := by
      refine natDegree_comp_le.trans ?_
      rw [natDegree_hasseDeriv]
      have : (C a * X).natDegree ≤ 1 := by compute_degree
      calc (p.natDegree - k) * (C a * X).natDegree ≤ (p.natDegree - k) * 1 :=
            Nat.mul_le_mul_left _ this
        _ = p.natDegree - k := mul_one _
    have h2 : ((1 - X ^ 2 : ℝ[X]) ^ (k / 2)).natDegree ≤ k / 2 * 2 := by
      refine natDegree_pow_le.trans (Nat.mul_le_mul_left _ ?_)
      compute_degree
    refine (natDegree_mul_le).trans ?_
    refine (add_le_add ((natDegree_C_mul_le _ _).trans h1) h2).trans ?_
    obtain ⟨m, rfl⟩ := hodd
    omega
  · simp

end Markov

open Markov in
/-- **Bernstein's inequality** for algebraic polynomials. If `p` has degree at most `q` and
`|p| ≤ M` on `[−1, 1]`, then `|p'(x)| ≤ q M / √(1 − x²)` for `|x| < 1`.

Source: Bernstein (1912); Rivlin, *Chebyshev Polynomials* (2nd ed., 1990), §2.7; Cheney,
*Introduction to Approximation Theory*, Ch. 3. Atlas: `bernstein-polynomial-inequality`.
Proof (algebraic form of the trigonometric argument): with `a = x = cos θ₀`, `b = √(1 − x²)`, the
odd part of `θ ↦ p(cos(θ₀ + θ))` is `sin θ · r(cos θ)` for a polynomial `r` of degree `< q` (built
from Hasse derivatives of `p`), `√(1 − y²) |r(y)| ≤ M` on `[−1, 1]`, and `r(1) = −b p'(x)`; Schur's
inequality `abs_eval_le_mul_of_forall_sqrt_one_sub_sq_mul_abs_eval_le` at `y = 1` gives
`b |p'(x)| ≤ q M`.
atlas: bernstein-polynomial-inequality -/
theorem abs_eval_derivative_le_div_sqrt_of_forall_abs_eval_le {q : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hp : p.degree ≤ q) (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval y| ≤ M) (hx : |x| < 1) :
    |(derivative p).eval x| ≤ q * M / √(1 - x ^ 2) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨by norm_num, by norm_num⟩)
  have hx2 : x ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg x]
  set b := √(1 - x ^ 2) with hbdef
  have hb : 0 < b := sqrt_pos.mpr (by linarith)
  have hb2 : b ^ 2 = 1 - x ^ 2 := sq_sqrt (by linarith)
  rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
  · rw [derivative_of_natDegree_zero hd, eval_zero, abs_zero]
    positivity
  have hqd : p.natDegree ≤ q := natDegree_le_of_degree_le hp
  have hq : 0 < q := lt_of_lt_of_le hd hqd
  set r := oddPart p x b
  have hr : r.degree < q := by
    refine degree_le_natDegree.trans_lt ?_
    have : r.natDegree ≤ p.natDegree - 1 := natDegree_oddPart_le p x b
    exact_mod_cast (show r.natDegree < q by omega)
  have hrM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |r.eval y| ≤ M := by
    intro y hy
    have hy2 : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    set s := √(1 - y ^ 2)
    have hs0 : 0 ≤ s := sqrt_nonneg _
    have hs2 : s ^ 2 = 1 - y ^ 2 := sq_sqrt hy2
    have key := eval_sub_eval_eq_two_mul_oddPart p x b hs2
    have hid : ∀ e : ℝ, e ^ 2 = 1 → (x * y + e * (b * s)) ^ 2 ≤ 1 := by
      intro e he
      have : (x * y + e * (b * s)) ^ 2 + (e * (x * s) - b * y) ^ 2 =
          (x ^ 2 + b ^ 2) * (y ^ 2 + s ^ 2) := by
        linear_combination (b ^ 2 * s ^ 2 + x ^ 2 * s ^ 2) * he
      rw [hb2, hs2] at this
      nlinarith [sq_nonneg (e * (x * s) - b * y)]
    have hmem : ∀ e : ℝ, e ^ 2 = 1 → x * y + e * (b * s) ∈ Set.Icc (-1 : ℝ) 1 := by
      intro e he
      have := hid e he
      constructor <;> nlinarith [sq_nonneg (x * y + e * (b * s) - 1),
        sq_nonneg (x * y + e * (b * s) + 1)]
    have h1 := hM _ (hmem (-1) (by norm_num))
    have h2 := hM _ (hmem 1 (by norm_num))
    simp only [neg_mul, one_mul, ← sub_eq_add_neg] at h1 h2
    have : |2 * s * r.eval y| ≤ 2 * M := by
      rw [← key]
      exact (abs_sub _ _).trans (by linarith)
    rw [abs_mul, abs_mul, abs_of_nonneg hs0] at this
    norm_num at this
    linarith
  have hS := abs_eval_le_mul_of_forall_sqrt_one_sub_sq_mul_abs_eval_le hq hr hrM
    (x := 1) ⟨by norm_num, le_rfl⟩
  rw [eval_oddPart_one hd, abs_neg, abs_mul, abs_of_pos hb] at hS
  rw [le_div_iff₀ hb]
  linarith

/-- **Markov brothers' inequality** (the first Markov inequality, sharp constant). If `p` has
degree at most `q` and `|p| ≤ M` on `[−1, 1]`, then `|p'(x)| ≤ q² M` for all `x ∈ [−1, 1]`.

Source: A. A. Markov (1889); Rivlin, *Chebyshev Polynomials* (2nd ed., 1990), Thm 2.24 / §2.7;
Cheney, *Introduction to Approximation Theory*, Ch. 3. Atlas: `markov-brothers`.
Proof: Bernstein's inequality `abs_eval_derivative_le_div_sqrt_of_forall_abs_eval_le` gives
`√(1 − y²) |p'(y)| ≤ q M` on `[−1, 1]`, and Schur's inequality
`abs_eval_le_mul_of_forall_sqrt_one_sub_sq_mul_abs_eval_le` applied to `p'` (degree `< q`) gives
`|p'(x)| ≤ q · q M`. The equality case (`p = ±M T_q`, `x = ±1`) is not formalised.
atlas: markov-brothers -/
theorem abs_eval_derivative_le_sq_mul_of_forall_abs_eval_le {q : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hp : p.degree ≤ q) (hM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval y| ≤ M)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(derivative p).eval x| ≤ (q : ℝ) ^ 2 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨by norm_num, by norm_num⟩)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : p.natDegree = 0 := Nat.le_zero.mp (natDegree_le_of_degree_le hp)
    rw [derivative_of_natDegree_zero this]
    simp
  have hr : (derivative p).degree < q := by
    rcases eq_or_ne p 0 with h0 | h0
    · simp [h0]
    · exact (degree_derivative_lt h0).trans_le hp
  have hrM : ∀ y ∈ Set.Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |(derivative p).eval y| ≤ q * M := by
    intro y hy
    rcases lt_or_eq_of_le (abs_le.mpr ⟨hy.1, hy.2⟩) with hy1 | hy1
    · have hpos : 0 < √(1 - y ^ 2) := by
        apply sqrt_pos.mpr
        nlinarith [abs_nonneg y, sq_abs y]
      have := abs_eval_derivative_le_div_sqrt_of_forall_abs_eval_le hp hM hy1
      rw [le_div_iff₀ hpos] at this
      linarith
    · have : 1 - y ^ 2 = 0 := by rw [← sq_abs, hy1]; norm_num
      rw [this, sqrt_zero, zero_mul]
      positivity
  have := abs_eval_le_mul_of_forall_sqrt_one_sub_sq_mul_abs_eval_le hq hr hrM hx
  linarith

/-- **Markov brothers' inequality on an interval.** If `p` has degree at most `q` and `|p| ≤ M` on
`[a, b]` (`a < b`), then `|p'(x)| ≤ 2 q² / (b − a) · M` for all `x ∈ [a, b]`.

Source: A. A. Markov (1889); Rivlin, *Chebyshev Polynomials* (2nd ed., 1990), §2.7 (affine
rescaling of `abs_eval_derivative_le_sq_mul_of_forall_abs_eval_le`). Atlas: `markov-brothers`.
atlas: markov-brothers -/
theorem abs_eval_derivative_le_two_mul_sq_div_mul_of_forall_abs_eval_le {q : ℕ} {p : ℝ[X]}
    {a b M x : ℝ} (hab : a < b) (hp : p.degree ≤ q)
    (hM : ∀ y ∈ Set.Icc a b, |p.eval y| ≤ M) (hx : x ∈ Set.Icc a b) :
    |(derivative p).eval x| ≤ 2 * (q : ℝ) ^ 2 / (b - a) * M := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set L : ℝ[X] := C ((a + b) / 2) + C ((b - a) / 2) * X
  have hL : ∀ t : ℝ, L.eval t = (a + b) / 2 + (b - a) / 2 * t := fun t => by simp [L]
  set P := p.comp L
  have hP : P.degree ≤ q := by
    refine degree_le_of_natDegree_le ?_
    refine natDegree_comp_le.trans ?_
    have h1 : L.natDegree ≤ 1 := by simp only [L]; compute_degree
    have h2 : p.natDegree ≤ q := natDegree_le_of_degree_le hp
    calc p.natDegree * L.natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ h1
      _ ≤ q := by rw [mul_one]; exact h2
  have hPM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ M := by
    intro t ht
    rw [eval_comp, hL]
    apply hM
    constructor <;> nlinarith [ht.1, ht.2]
  set t₀ := (2 * x - a - b) / (b - a)
  have ht₀ : L.eval t₀ = x := by
    rw [hL]; simp only [t₀]; field_simp; ring
  have ht₀mem : t₀ ∈ Set.Icc (-1 : ℝ) 1 := by
    simp only [t₀, Set.mem_Icc]
    constructor
    · rw [le_div_iff₀ hba]; linarith [hx.1]
    · rw [div_le_iff₀ hba]; linarith [hx.2]
  have hmk := abs_eval_derivative_le_sq_mul_of_forall_abs_eval_le hP hPM ht₀mem
  have hder : (derivative P).eval t₀ = (b - a) / 2 * (derivative p).eval x := by
    simp only [P, derivative_comp, eval_mul, eval_comp, ht₀]
    simp [L]
  rw [hder, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b - a) / 2)] at hmk
  rw [div_mul_eq_mul_div, le_div_iff₀ hba]
  linarith

end NLAlib
