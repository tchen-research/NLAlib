import NLAlib.Polynomial.AnalyticFourier
import NLAlib.ForMathlib.Analysis.FourierCircle

/-!
# Chebyshev series and truncation for a holomorphic Bernstein ellipse

The series is reconstructed through Mathlib's Fourier theorem; geometric coefficient decay
is proved from the original open-ellipse holomorphy hypotheses.
-/

noncomputable section

open Complex Set Metric Filter Polynomial Polynomial.Chebyshev Finset
open scoped Topology ComplexConjugate Real

namespace NLAlib

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Pairing opposite Fourier frequencies gives the positive Chebyshev series term.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, helper). -/
theorem re_fourier_pair_eq_chebyshevAnalyticCoeff_mul_eval_T (F : ℂ → ℂ)
    {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    ((fourierCoeff (chebyshevCircleFunction F) (k : ℤ) *
      fourier (k : ℤ) (θ : AddCircle (2 * Real.pi))) +
      (fourierCoeff (chebyshevCircleFunction F) (-(k : ℤ)) *
        fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)))).re =
      chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval (Real.cos θ) := by
  rw [fourierCoeff_chebyshevCircleFunction_neg, ← mul_add, fourier_neg, Complex.add_conj,
    T_real_cos, re_fourier_nat_coe_eq_cos]
  rw [chebyshevAnalyticCoeff, chebyshevComplexCoeff_eq_fourierCoeff, if_neg (Nat.ne_of_gt hk)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

set_option maxHeartbeats 800000 in
/-- The Chebyshev series on a real cosine argument reconstructs the original function's
real part from the genuine open-ellipse holomorphy and bound assumptions.
Source: Trefethen, ATAP, Theorems 3.1(a), 8.1 and 8.2.
Atlas `chebyshev-approx-analytic` (helper). -/
theorem hasSum_chebyshevAnalyticCoeff_mul_eval_T_cos_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) (θ : ℝ) :
    HasSum (fun k : ℕ => chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval (Real.cos θ))
      (F (Real.cos θ)).re := by
  let u : ℤ → ℂ := fun k => fourierCoeff (chebyshevCircleFunction F) k *
    fourier k (θ : AddCircle (2 * Real.pi))
  have hu : HasSum u (F (Real.cos θ)) := by
    simpa only [smul_eq_mul, chebyshevCircleFunction_coe_eq_cos] using
      hasSum_fourier_chebyshevCircleFunction_of_open_ellipse hρ hFd hM
        (θ : AddCircle (2 * Real.pi))
  have hp : Summable (fun k : ℕ => u (k : ℤ)) :=
    hu.summable.comp_injective Nat.cast_injective
  have hn : Summable (fun k : ℕ => u (-((k + 1 : ℕ) : ℤ))) :=
    hu.summable.comp_injective (show Function.Injective (fun k : ℕ => -((k + 1 : ℕ) : ℤ)) by
      intro a b hab
      have h := neg_injective hab
      exact Nat.add_right_cancel (Int.natCast_inj.mp h))
  have hps : Summable (fun k : ℕ => u ((k + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).mpr hp
  have hsum : (∑' k : ℕ, u (k : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ))) =
      F (Real.cos θ) := by
    rw [← hu.tsum_eq]
    exact (tsum_of_nat_of_neg_add_one hp hn).symm
  have hsplit := hp.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at hsplit
  have hpair := Complex.reCLM.hasSum (hps.hasSum.add hn.hasSum)
  have hterm : ∀ k : ℕ,
      (u ((k + 1 : ℕ) : ℤ) + u (-((k + 1 : ℕ) : ℤ))).re =
        chebyshevAnalyticCoeff F (k + 1) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) := by
    intro k
    exact re_fourier_pair_eq_chebyshevAnalyticCoeff_mul_eval_T F (Nat.succ_pos k) θ
  change HasSum (fun k : ℕ => (u ((k + 1 : ℕ) : ℤ) + u (-((k + 1 : ℕ) : ℤ))).re)
    ((∑' k : ℕ, u ((k + 1 : ℕ) : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ)))).re at hpair
  simp_rw [hterm] at hpair
  have hfull := hpair.zero_add (f := fun k : ℕ =>
    chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval (Real.cos θ))
  have hzero : chebyshevAnalyticCoeff F 0 * (T ℝ (0 : ℤ)).eval (Real.cos θ) = (u 0).re := by
    simp [chebyshevAnalyticCoeff, chebyshevComplexCoeff_eq_fourierCoeff, u]
  simp only [Nat.cast_zero] at hfull hsplit
  rw [hzero] at hfull
  have heq : (u 0).re +
      ((∑' k : ℕ, u ((k + 1 : ℕ) : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ)))).re =
        (F (Real.cos θ)).re := by
    rw [← Complex.add_re, ← add_assoc, hsplit, hsum]
  rw [heq] at hfull
  exact hfull

/-- The degree-`N` truncation of the canonical real Chebyshev coefficients.
Source: Trefethen, ATAP, Chapters 3 and 8 (`chebyshev-approx-analytic`, definition). -/
def chebyshevAnalyticTrunc (F : ℂ → ℂ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ range (N + 1), C (chebyshevAnalyticCoeff F k) * T ℝ (k : ℤ)

/-- The canonical Chebyshev truncation has degree at most its cutoff.
Source: Trefethen, ATAP, Chapter 3 (`chebyshev-approx-analytic`, helper). -/
theorem degree_chebyshevAnalyticTrunc_le (F : ℂ → ℂ) (N : ℕ) :
    (chebyshevAnalyticTrunc F N).degree ≤ N := by
  unfold chebyshevAnalyticTrunc
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
  rw [C_mul']
  refine (degree_smul_le _ _).trans ?_
  rw [degree_T, Int.natAbs_natCast]
  exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)

/-- The genuine Chebyshev series reconstructs the function on every point of `[-1,1]`.
Source: Trefethen, ATAP, Theorems 3.1(a), 8.1 and 8.2.
Atlas `chebyshev-approx-analytic` (helper). -/
theorem hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval x) (F x).re := by
  simpa only [Real.cos_arccos hx.1 hx.2] using
    hasSum_chebyshevAnalyticCoeff_mul_eval_T_cos_of_open_ellipse hρ hFd hM (Real.arccos x)

/-- A geometric tail of positive Chebyshev coefficients gives the exact truncation constant.
Source: Trefethen, ATAP, Theorem 8.2; coefficient decay and reconstruction are proved from
the original open-ellipse hypotheses, without boundary continuity.
atlas: chebyshev-approx-analytic (partial) -/
theorem abs_re_sub_eval_chebyshevAnalyticTrunc_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) (N : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(F x).re - (chebyshevAnalyticTrunc F N).eval x| ≤
      2 * M / ρ ^ N / (ρ - 1) := by
  let u : ℕ → ℝ := fun k => chebyshevAnalyticCoeff F k * (T ℝ (k : ℤ)).eval x
  have hu : HasSum u (F x).re := hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse hρ hFd hM hx
  have hsplit := hu.summable.sum_add_tsum_nat_add (N + 1)
  rw [hu.tsum_eq] at hsplit
  have hp : (chebyshevAnalyticTrunc F N).eval x = ∑ k ∈ range (N + 1), u k := by
    simp only [chebyshevAnalyticTrunc, eval_finsetSum, eval_mul, eval_C, u]
  have herr : (F x).re - (chebyshevAnalyticTrunc F N).eval x =
      ∑' i : ℕ, u (i + (N + 1)) := by rw [hp]; linarith
  have hq : |ρ⁻¹| < 1 := by
    rw [abs_of_pos (by positivity : 0 < ρ⁻¹)]
    exact (inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ
  have hgeom : Summable (fun i : ℕ => 2 * M / ρ ^ (i + (N + 1))) := by
    have h := ((summable_geometric_of_abs_lt_one hq).mul_right ((ρ⁻¹) ^ (N + 1))).mul_left (2 * M)
    convert h using 1 <;> try rfl
    funext i
    rw [div_eq_mul_inv, ← inv_pow, pow_add]
  have hterm : ∀ i : ℕ, ‖u (i + (N + 1))‖ ≤ 2 * M / ρ ^ (i + (N + 1)) := by
    intro i
    have hc := abs_chebyshevAnalyticCoeff_le_of_open_ellipse hρ hFd hM
      (k := i + (N + 1)) (by omega)
    have hT := abs_eval_T_real_le_one ((i + (N + 1) : ℕ) : ℤ) (abs_le.mpr hx)
    dsimp [u]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hT (abs_nonneg _)).trans (by simpa using hc)
  have hnorm := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm hgeom
  rw [herr, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hterm hgeom).trans_eq ?_)
  have hterm_eq : ∀ i : ℕ, 2 * M / ρ ^ (i + (N + 1)) =
      2 * M * ((ρ⁻¹) ^ i * (ρ⁻¹) ^ (N + 1)) := by
    intro i
    rw [div_eq_mul_inv, ← inv_pow, pow_add]
  simp_rw [hterm_eq]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_abs_lt_one hq]
  have hρ0 : ρ ≠ 0 := ne_of_gt (zero_lt_one.trans hρ)
  rw [pow_succ]
  simp only [inv_pow]
  field_simp [hρ0]

/-- A bounded holomorphic extension on the open Bernstein ellipse supplies a real polynomial
of degree at most `N` with the exact error `2M ρ⁻ᴺ/(ρ-1)` on `[-1,1]`.
Source: Trefethen, ATAP, Theorem 8.2; operator rederivations `rt:analytic-approx`.
No boundary continuity or coefficient/approximation conclusion is assumed.
atlas: bernstein-ellipse-approx -/
theorem exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse
    {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ x ∈ Icc (-1 : ℝ) 1, F x = (f x : ℂ)) (N : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ N ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |f x - p.eval x| ≤ 2 * M / ρ ^ N / (ρ - 1) := by
  refine ⟨chebyshevAnalyticTrunc F N, degree_chebyshevAnalyticTrunc_le F N, ?_⟩
  intro x hx
  have h := abs_re_sub_eval_chebyshevAnalyticTrunc_le_of_open_ellipse hρ hFd hM N hx
  rw [hmatch x hx, Complex.ofReal_re] at h
  exact h

/-- Affine transplantation of the Bernstein-ellipse polynomial rate to any real interval.
The analytic extension is of `t ↦ f(((c-a)t+c+a)/2)` on the original open ellipse.
Source: Trefethen, ATAP, Theorem 8.2; operator rederivations `rt:analytic-approx`.
atlas: bernstein-ellipse-approx -/
theorem exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a c ρ M : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ))
    (N : ℕ) : ∃ p : ℝ[X], p.degree ≤ N ∧ ∀ x ∈ Icc a c,
      |f x - p.eval x| ≤ 2 * M / ρ ^ N / (ρ - 1) := by
  obtain ⟨p, hp, hE⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse
    (f := fun t => f (((c - a) * t + c + a) / 2)) hρ hFd hM hmatch N
  let s : ℝ[X] := C (2 / (c - a)) * X - C ((c + a) / (c - a))
  refine ⟨p.comp s, ?_, ?_⟩
  · apply degree_le_of_natDegree_le
    refine natDegree_comp_le.trans ?_
    have hpN := natDegree_le_of_degree_le hp
    have hs : s.natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
      · simp
    nlinarith
  · intro x hx
    have hca : 0 < c - a := sub_pos.mpr hac
    let t := 2 / (c - a) * x - (c + a) / (c - a)
    have ht : t ∈ Icc (-1 : ℝ) 1 := by
      have htform : t = (2 * x - c - a) / (c - a) := by dsimp [t]; ring
      rw [htform]
      constructor
      · rw [le_div_iff₀ hca]
        nlinarith [hx.1]
      · rw [div_le_iff₀ hca]
        nlinarith [hx.2]
    have heq : ((c - a) * t + c + a) / 2 = x := by
      dsimp [t]
      field_simp [ne_of_gt hca]
      ring
    have h := hE t ht
    rw [heq] at h
    simpa only [eval_comp, s, eval_sub, eval_mul, eval_C, eval_X, t] using h

end NLAlib
