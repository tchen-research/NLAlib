import NLAlib.Polynomial.FunctionApproximation.BernsteinWalsh
import NLAlib.Polynomial.FunctionApproximation.EllipseCompact
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-!
# Bernstein's converse theorem

Geometric polynomial approximation on the real unit interval provides a
holomorphic extension and locally uniform convergence on the open ellipse.
Realises `bernstein-converse`.
-/

noncomputable section

open Polynomial Finset Set Filter
open scoped Topology

namespace NLAlib

private def converseDifference (q : ℕ → ℂ[X]) : ℕ → ℂ[X]
  | 0 => q 0
  | n + 1 => q (n + 1) - q n

private theorem sum_eval_converseDifference (q : ℕ → ℂ[X]) (n : ℕ) (z : ℂ) :
    ∑ j ∈ range (n + 1), (converseDifference q j).eval z = (q n).eval z := by
  induction n with
  | zero => simp [converseDifference]
  | succ n ih => rw [sum_range_succ, ih]; simp [converseDifference]

private theorem norm_eval_converseDifference_succ_le {q : ℕ → ℂ[X]} {f : ℝ → ℂ}
    {C ρ r : ℝ} (_hC : 0 ≤ C) (hρ : 1 < ρ) (_hr : 1 ≤ r)
    (hq : ∀ n, (q n).degree ≤ n)
    (hE : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖(q n).eval (x : ℂ) - f x‖ ≤ C / ρ ^ n)
    (n : ℕ) {z : ℂ} (hz : z ∈ filledBernsteinEllipse r) :
    ‖(converseDifference q (n + 1)).eval z‖ ≤ C * (1 + ρ) * (r / ρ) ^ (n + 1) := by
  have hd : (converseDifference q (n + 1)).degree ≤ (n + 1 : ℕ) := by
    dsimp only [converseDifference]
    exact (degree_sub_le _ _).trans
      (max_le (hq _) ((hq n).trans (by exact_mod_cast Nat.le_succ n)))
  have hbound : ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖(converseDifference q (n + 1)).eval (x : ℂ)‖ ≤ C * (1 + ρ) / ρ ^ (n + 1) := by
    intro x hx
    simp only [converseDifference, eval_sub]
    calc ‖(q (n + 1)).eval (x : ℂ) - (q n).eval (x : ℂ)‖ ≤
          ‖(q (n + 1)).eval (x : ℂ) - f x‖ + ‖f x - (q n).eval (x : ℂ)‖ :=
            by
              have heq : (q (n + 1)).eval (x : ℂ) - (q n).eval (x : ℂ) =
                  ((q (n + 1)).eval (x : ℂ) - f x) + (f x - (q n).eval (x : ℂ)) := by ring
              rw [heq]
              exact norm_add_le _ _
      _ ≤ C / ρ ^ (n + 1) + C / ρ ^ n := by
        rw [norm_sub_rev (f x)]
        exact add_le_add (hE _ _ hx) (hE _ _ hx)
      _ = C * (1 + ρ) / ρ ^ (n + 1) := by rw [pow_succ]; field_simp
  have hw := norm_eval_le_mul_pow_of_mem_filledBernsteinEllipse hd hbound hz
  convert hw using 1
  rw [div_pow]
  ring

/-- Geometric uniform polynomial approximability implies holomorphic extension to
the open Bernstein ellipse, with locally uniform convergence of the supplied sequence.
Source: Trefethen, ATAP, Thm 8.3 (Bernstein); operator derivations §5.
Deviation: complex interval values and complex polynomial coefficients are permitted.
atlas: bernstein-converse -/
theorem exists_holomorphic_extension_of_geometric_polynomial_approximation
    {f : ℝ → ℂ} {q : ℕ → ℂ[X]} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 1 < ρ)
    (hq : ∀ n, (q n).degree ≤ n)
    (hE : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖(q n).eval (x : ℂ) - f x‖ ≤ C / ρ ^ n) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (openBernsteinEllipse ρ) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, F (x : ℂ) = f x) ∧
      TendstoLocallyUniformlyOn (fun n z => (q n).eval z) F atTop (openBernsteinEllipse ρ) := by
  let D : ℕ → ℂ → ℂ := fun n z => (converseDifference q n).eval z
  let F : ℂ → ℂ := fun z => ∑' n, D n z
  have hs : SummableLocallyUniformlyOn D (openBernsteinEllipse ρ) := by
    apply SummableLocallyUniformlyOn_of_locally_bounded (isOpen_openBernsteinEllipse hρ)
    intro K hsub hK
    obtain ⟨r, hr, hrρ, hKr⟩ := exists_lt_radius_subset_filledBernsteinEllipse hρ hK hsub
    let u : ℕ → ℝ := fun n => if n = 0 then ‖(q 0).coeff 0‖
      else C * (1 + ρ) * (r / ρ) ^ n
    have hratio0 : 0 ≤ r / ρ := by positivity
    have hratio1 : r / ρ < 1 := (div_lt_one (zero_lt_one.trans hρ)).mpr hrρ
    have hu : Summable u := by
      apply (summable_nat_add_iff 1).mp
      have hgeo := (summable_geometric_of_lt_one hratio0 hratio1).mul_left (C * (1 + ρ))
      simpa only [u, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false] using
        (summable_nat_add_iff 1).mpr hgeo
    refine ⟨u, hu, fun n z hz => ?_⟩
    cases n with
    | zero =>
      have hq0 : q 0 = Polynomial.C ((q 0).coeff 0) := eq_C_of_degree_le_zero (hq 0)
      simp only [D, converseDifference, u, if_pos rfl]
      rw [hq0, eval_C]
      simp
    | succ n =>
      simpa only [D, u, Nat.succ_ne_zero, if_false] using
        norm_eval_converseDifference_succ_le hC hρ hr.le hq hE n (hKr hz)
  have hsum := hs.hasSumLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hshift : TendstoLocallyUniformlyOn
      (fun n z => ∑ j ∈ range (n + 1), D j z) F atTop (openBernsteinEllipse ρ) := by
    intro u hu x hx
    obtain ⟨t, ht, h⟩ := hsum u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat 1).eventually h⟩
  have hlimit : TendstoLocallyUniformlyOn (fun n z => (q n).eval z) F atTop
      (openBernsteinEllipse ρ) := by
    apply hshift.congr
    intro n z hz
    exact sum_eval_converseDifference q n z
  refine ⟨F, hlimit.differentiableOn (Eventually.of_forall fun n => (q n).differentiableOn)
    (isOpen_openBernsteinEllipse hρ), ?_, hlimit⟩
  intro x hx
  have hxellipse := ofReal_mem_openBernsteinEllipse hρ hx
  have hpoint := hlimit.tendsto_at hxellipse
  have hrate : Tendsto (fun n : ℕ => C / ρ ^ n) atTop (𝓝 0) := by
    have hinv : |ρ⁻¹| < 1 := by
      rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans hρ)), inv_lt_one₀ (zero_lt_one.trans hρ)]
      exact hρ
    have hh := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hinv).const_mul C
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using hh
  have hnorm : Tendsto (fun n => ‖(q n).eval (x : ℂ) - f x‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => hE n x hx) hrate
  exact tendsto_nhds_unique hpoint ((tendsto_iff_norm_sub_tendsto_zero).mpr hnorm)

/-- Rates at every strictly smaller ellipse radius give a single holomorphic
extension on the whole open ellipse. The same telescoping series works on every
compact subset, with its geometric majorant chosen for that subset.
Source: ATAP, Thm 8.3 and Ex 8.11; operator derivations §5.
Helper for `bernstein-converse`. -/
theorem exists_holomorphic_extension_of_polynomial_approximation_rates
    {f : ℝ → ℂ} {q : ℕ → ℂ[X]} {ρ : ℝ} (hρ : 1 < ρ)
    (hq : ∀ n, (q n).degree ≤ n)
    (hE : ∀ s : ℝ, 1 < s → s < ρ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖(q n).eval (x : ℂ) - f x‖ ≤ C / s ^ n) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (openBernsteinEllipse ρ) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, F (x : ℂ) = f x) ∧
      TendstoLocallyUniformlyOn (fun n z => (q n).eval z) F atTop (openBernsteinEllipse ρ) := by
  let D : ℕ → ℂ → ℂ := fun n z => (converseDifference q n).eval z
  let F : ℂ → ℂ := fun z => ∑' n, D n z
  have hs : SummableLocallyUniformlyOn D (openBernsteinEllipse ρ) := by
    apply SummableLocallyUniformlyOn_of_locally_bounded (isOpen_openBernsteinEllipse hρ)
    intro K hsub hK
    obtain ⟨r, hr, hrρ, hKr⟩ := exists_lt_radius_subset_filledBernsteinEllipse hρ hK hsub
    obtain ⟨s, hrs, hsρ⟩ := exists_between hrρ
    have hs1 : 1 < s := hr.trans hrs
    obtain ⟨C, hC, hEs⟩ := hE s hs1 hsρ
    let u : ℕ → ℝ := fun n => if n = 0 then ‖(q 0).coeff 0‖
      else C * (1 + s) * (r / s) ^ n
    have hratio0 : 0 ≤ r / s := by positivity
    have hratio1 : r / s < 1 := (div_lt_one (zero_lt_one.trans hs1)).mpr hrs
    have hu : Summable u := by
      apply (summable_nat_add_iff 1).mp
      have hgeo := (summable_geometric_of_lt_one hratio0 hratio1).mul_left (C * (1 + s))
      simpa only [u, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false] using
        (summable_nat_add_iff 1).mpr hgeo
    refine ⟨u, hu, fun n z hz => ?_⟩
    cases n with
    | zero =>
      have hq0 : q 0 = Polynomial.C ((q 0).coeff 0) := eq_C_of_degree_le_zero (hq 0)
      simp only [D, converseDifference, u, if_pos rfl]
      rw [hq0, eval_C]
      simp
    | succ n =>
      simpa only [D, u, Nat.succ_ne_zero, if_false] using
        norm_eval_converseDifference_succ_le hC hs1 hr.le hq hEs n (hKr hz)
  have hsum := hs.hasSumLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hshift : TendstoLocallyUniformlyOn
      (fun n z => ∑ j ∈ range (n + 1), D j z) F atTop (openBernsteinEllipse ρ) := by
    intro u hu x hx
    obtain ⟨t, ht, h⟩ := hsum u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat 1).eventually h⟩
  have hlimit : TendstoLocallyUniformlyOn (fun n z => (q n).eval z) F atTop
      (openBernsteinEllipse ρ) := by
    apply hshift.congr
    intro n z hz
    exact sum_eval_converseDifference q n z
  refine ⟨F, hlimit.differentiableOn (Eventually.of_forall fun n => (q n).differentiableOn)
    (isOpen_openBernsteinEllipse hρ), ?_, hlimit⟩
  intro x hx
  obtain ⟨s, hs1, hsρ⟩ := exists_between hρ
  obtain ⟨C, hC, hEs⟩ := hE s hs1 hsρ
  have hpoint := hlimit.tendsto_at (ofReal_mem_openBernsteinEllipse hρ hx)
  have hrate : Tendsto (fun n : ℕ => C / s ^ n) atTop (𝓝 0) := by
    have hinv : |s⁻¹| < 1 := by
      rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans hs1)), inv_lt_one₀ (zero_lt_one.trans hs1)]
      exact hs1
    have hh := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hinv).const_mul C
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using hh
  have hnorm : Tendsto (fun n => ‖(q n).eval (x : ℂ) - f x‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => hEs n x hx) hrate
  exact tendsto_nhds_unique hpoint ((tendsto_iff_norm_sub_tendsto_zero).mpr hnorm)

/-- A finite upper root-limsup yields geometric bounds at every smaller radius.
The extended nonnegative codomain records the usual limsup even for initially
unbounded root sequences, without the default values of a conditional supremum.
Source: the root test; operator derivations §5, limsup variant of Bernstein's theorem. -/
theorem geometric_bound_of_root_limsup_le {e : ℕ → ℝ} {ρ s : ℝ}
    (he : ∀ n, 0 ≤ e n) (hρ : 1 < ρ) (hs : 1 < s) (hsρ : s < ρ)
    (hlim : limsup (fun n => ENNReal.ofReal (e n ^ ((n : ℝ)⁻¹))) atTop ≤
      ENNReal.ofReal ρ⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, e n ≤ C / s ^ n := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hinv : ρ⁻¹ < s⁻¹ := (inv_lt_inv₀ hρ0 hs0).mpr hsρ
  have hroot := eventually_lt_of_limsup_lt
    (hlim.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hs0)).mpr hinv))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hroot
  let C : ℝ := 1 + ∑ n ∈ range (N + 1), e n * s ^ n
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (sum_nonneg fun n _ => mul_nonneg (he n) (pow_nonneg hs0.le n))
  refine ⟨C, zero_le_one.trans hC1, fun n => ?_⟩
  by_cases hn : n ≤ N
  · have hterm : e n * s ^ n ≤ ∑ j ∈ range (N + 1), e j * s ^ j :=
      single_le_sum (fun j _ => mul_nonneg (he j) (pow_nonneg hs0.le j))
        (mem_range.mpr (by omega))
    exact (le_div_iff₀ (pow_pos hs0 n)).mpr (hterm.trans (by dsimp only [C]; linarith))
  · have hn0 : n ≠ 0 := by omega
    have hrootn : e n ^ ((n : ℝ)⁻¹) < s⁻¹ :=
      (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hs0)).mp (hN n (by omega))
    have hpow : e n ≤ (s⁻¹) ^ n := by
      rw [← Real.rpow_inv_natCast_pow (he n) hn0]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (he n) _) hrootn.le n
    calc e n ≤ 1 / s ^ n := by simpa only [inv_pow, one_div] using hpow
      _ ≤ C / s ^ n := div_le_div_of_nonneg_right hC1 (pow_nonneg hs0.le n)

/-- The root-limsup form of Bernstein's converse for any supplied nonnegative
uniform-error bounds. No single geometric constant at the limiting radius is
required: the rates on each smaller radius suffice.
Source: Trefethen, ATAP, Thm 8.3 and Ex 8.11; operator derivations §5.
Deviation: complex interval values and complex polynomial coefficients are permitted.
atlas: bernstein-converse -/
theorem exists_holomorphic_extension_of_polynomial_approximation_limsup
    {f : ℝ → ℂ} {q : ℕ → ℂ[X]} {e : ℕ → ℝ} {ρ : ℝ} (hρ : 1 < ρ)
    (hq : ∀ n, (q n).degree ≤ n) (he : ∀ n, 0 ≤ e n)
    (hE : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖(q n).eval (x : ℂ) - f x‖ ≤ e n)
    (hlim : limsup (fun n => ENNReal.ofReal (e n ^ ((n : ℝ)⁻¹))) atTop ≤
      ENNReal.ofReal ρ⁻¹) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (openBernsteinEllipse ρ) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, F (x : ℂ) = f x) ∧
      TendstoLocallyUniformlyOn (fun n z => (q n).eval z) F atTop (openBernsteinEllipse ρ) := by
  apply exists_holomorphic_extension_of_polynomial_approximation_rates hρ hq
  intro s hs hsρ
  obtain ⟨C, hC, hbound⟩ := geometric_bound_of_root_limsup_le he hρ hs hsρ hlim
  exact ⟨C, hC, fun n x hx => (hE n x hx).trans (hbound n)⟩

/-- Bernstein's converse using exactly the uniform norm of the interval error.
Its extended root-limsup formulation is the usual finite limsup condition, and
also excludes unbounded error-root sequences without an auxiliary boundedness hypothesis.
Source: Trefethen, ATAP, Thm 8.3 and Ex 8.11; operator derivations §5.
atlas: bernstein-converse -/
theorem exists_holomorphic_extension_of_polynomial_approximation_norm_limsup
    (f : C(Icc (-1 : ℝ) 1, ℂ)) {q : ℕ → ℂ[X]} {ρ : ℝ} (hρ : 1 < ρ)
    (hq : ∀ n, (q n).degree ≤ n)
    (hlim : limsup (fun n => ENNReal.ofReal
      (‖(⟨fun x : Icc (-1 : ℝ) 1 => (q n).eval (x : ℂ), by fun_prop⟩ :
          C(Icc (-1 : ℝ) 1, ℂ)) - f‖ ^ ((n : ℝ)⁻¹))) atTop ≤ ENNReal.ofReal ρ⁻¹) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (openBernsteinEllipse ρ) ∧
      (∀ (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1), F (x : ℂ) = f ⟨x, hx⟩) ∧
      TendstoLocallyUniformlyOn (fun n z => (q n).eval z) F atTop (openBernsteinEllipse ρ) := by
  let p : ℕ → C(Icc (-1 : ℝ) 1, ℂ) := fun n =>
    ⟨fun x => (q n).eval (x : ℂ), by fun_prop⟩
  have hE : ∀ n x, x ∈ Icc (-1 : ℝ) 1 →
      ‖(q n).eval (x : ℂ) - IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f x‖ ≤ ‖p n - f‖ := by
    intro n x hx
    rw [IccExtend_of_mem _ _ hx]
    exact (p n - f).norm_coe_le_norm ⟨x, hx⟩
  obtain ⟨F, hF, hFx, hconv⟩ :=
    exists_holomorphic_extension_of_polynomial_approximation_limsup
      (f := IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) (e := fun n => ‖p n - f‖)
      hρ hq (fun n => norm_nonneg _) hE hlim
  exact ⟨F, hF, fun x hx => by simpa only [IccExtend_of_mem _ _ hx] using hFx x hx, hconv⟩

end NLAlib
