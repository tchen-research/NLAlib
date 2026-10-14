import NLAlib.Polynomial.BestApproximation.Absolute
import NLAlib.Polynomial.FunctionApproximation.AbsoluteFiniteGrowth

/-!
# Uniform finite growth of scaled absolute-value approximants

An explicit source-degree threshold makes the complex growth bound independent
of that degree. All objects are finite polynomials.
Source: the focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section

open Polynomial Set Complex

namespace NLAlib

private theorem one_div_sqrt_one_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) :
    1 / Real.sqrt (1 - q) ≤ 1 + 2 * q := by
  have hp : 0 < 1 - q := by linarith
  have hs : 0 < Real.sqrt (1 - q) := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hl : 1 - q ≤ Real.sqrt (1 - q) := by nlinarith
  refine (one_div_le_one_div_of_le hp hl).trans ?_
  apply (div_le_iff₀ hp).mpr
  nlinarith

private theorem two_mul_cube_le_sq_of_threshold {R n : ℝ} (hR : 0 ≤ R)
    (hthreshold : 2 * max 1 (R^2) ≤ n) : 2 * R^3 ≤ n^2 := by
  have hn2 : 2 ≤ n := by nlinarith [le_max_left (1 : ℝ) (R^2)]
  have hnR : 2 * R^2 ≤ n := by nlinarith [le_max_right (1 : ℝ) (R^2)]
  by_cases hR1 : R ≤ 1
  · have hR2 : R^2 ≤ 1 := by nlinarith
    have hR3 : R^3 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hR1 (sq_nonneg R)
      nlinarith
    nlinarith
  · have hR1' : 1 ≤ R := le_of_not_ge hR1
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * R^2) hnR 2
    have hR3 : 0 ≤ R^3 := by positivity
    have hm := mul_nonneg (sub_nonneg.mpr hR1') hR3
    nlinarith

/-- The explicit source-degree threshold gives a complex sine coordinate whose
scaled norm and scaled imaginary part have bounds independent of the degree. -/
theorem exists_sin_eq_scaled_of_threshold {R n : ℝ} (hR : 0 ≤ R)
    (hthreshold : 2 * max 1 (R^2) ≤ n) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∃ u : ℂ, Complex.sin u = z / (n : ℂ) ∧
      n * ‖u‖ ≤ 2 * R ∧ n * |u.im| ≤ |z.im| + 1 := by
  have hn2 : 2 ≤ n := by nlinarith [le_max_left (1 : ℝ) (R^2)]
  have hn : 0 < n := by linarith
  have hRmax : R ≤ max 1 (R^2) := by
    by_cases hR1 : R ≤ 1
    · exact hR1.trans (le_max_left _ _)
    · have hR1' : 1 ≤ R := le_of_not_ge hR1
      exact (by nlinarith : R ≤ R^2).trans (le_max_right _ _)
  have hnR : 2 * R ≤ n := by linarith
  have hnorm : ‖z / (n : ℂ)‖ = ‖z‖ / n := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hr : 0 ≤ ‖z‖ / n := div_nonneg (norm_nonneg _) hn.le
  have hrh : ‖z‖ / n ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by nlinarith)
  have hzhalf : ‖z / (n : ℂ)‖ ≤ 1 / 2 := by rw [hnorm]; exact hrh
  obtain ⟨u, hu, hunorm, hum⟩ := Complex.exists_sin_eq_of_norm_le_half hzhalf
  have hnormu : n * ‖u‖ ≤ 2 * R := by
    rw [hnorm] at hunorm
    have h := mul_le_mul_of_nonneg_left hunorm hn.le
    have he : n * (2 * (‖z‖ / n)) = 2 * ‖z‖ := by field_simp
    rw [he] at h
    exact h.trans (by linarith)
  let q := (‖z‖ / n)^2
  have hq : q ≤ 1 / 4 := by dsimp [q]; nlinarith
  have hq0 : 0 ≤ q := sq_nonneg _
  have hinv := one_div_sqrt_one_sub_le hq0 hq
  have him : n * |u.im| ≤ |z.im| / Real.sqrt (1 - q) := by
    rw [hnorm, Complex.div_ofReal_im, abs_div, abs_of_pos hn] at hum
    have h := mul_le_mul_of_nonneg_left hum hn.le
    have he : n * (|z.im| / n / Real.sqrt (1 - q)) =
        |z.im| / Real.sqrt (1 - q) := by field_simp
    exact h.trans_eq he
  have him' : n * |u.im| ≤ |z.im| * (1 + 2 * q) :=
    him.trans (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hinv (abs_nonneg z.im))
  have hcorr : |z.im| * (2 * q) ≤ 1 := by
    have hy : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hz
    have hz2 : ‖z‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hmult := mul_le_mul hy hz2 (sq_nonneg _) hR
    have hcube := two_mul_cube_le_sq_of_threshold hR hthreshold
    dsimp [q]
    rw [div_pow, ← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hn 2)).mpr
    nlinarith
  refine ⟨u, hu, hnormu, ?_⟩
  nlinarith

/-- Every even-degree approximant meeting the actual Chebyshev comparison error
has uniform finite complex growth after scaling, above the explicit source-degree
threshold. This applies in particular to each attained best approximant.
Source: the focused polynomial Bernstein reroute, uniform finite bound. -/
theorem norm_scaled_absolute_approximant_le {m : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ (2 * m : ℕ))
    (herr : ∀ x ∈ Icc (-1 : ℝ) 1,
      |(|x|) - p.eval x| ≤ 2 / (Real.pi * (2 * m + 1)))
    {R : ℝ} (hR : 0 ≤ R) (hthreshold : 2 * max 1 (R^2) ≤ (2 * m : ℕ))
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖((2 * m : ℕ) : ℂ) * (p.map Complex.ofRealHom).eval (z / ((2 * m : ℕ) : ℂ))‖ ≤
      6 * (1 + R^2) / Real.pi * Real.exp (|z.im| + 1) := by
  let n : ℝ := (2 * m : ℕ)
  let S := chebyshevTrunc (fun x : ℝ => |x|) (2 * m)
  have hnc : 2 * (m : ℝ) = n := by simp [n]
  rw [hnc] at herr
  have hn2 : 2 ≤ n := by
    dsimp [n]
    nlinarith [le_max_left (1 : ℝ) (R^2)]
  have hn : 0 < n := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨u, hu, hunorm, hum⟩ := exists_sin_eq_scaled_of_threshold hR hthreshold hz
  have hdiff : ((p - S).map Complex.ofRealHom).degree ≤ (2 * m : ℕ) :=
    (degree_map_le).trans ((degree_sub_le _ _).trans (max_le hp (degree_chebyshevTrunc_le _ _)))
  have hbound : ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖((p - S).map Complex.ofRealHom).eval (x : ℂ)‖ ≤ 4 / (Real.pi * n) := by
    intro x hx
    rw [show (x : ℂ) = Complex.ofRealHom x by rfl, eval_map_apply,
      Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs, eval_sub]
    have hS := abs_abs_sub_eval_chebyshevTrunc_le m hx
    rw [hnc] at hS
    change |(|x|) - S.eval x| ≤ 2 / (Real.pi * (n + 1)) at hS
    have he : |p.eval x - S.eval x| ≤ 4 / (Real.pi * (n + 1)) := by
      have h := abs_sub_le (p.eval x) |x| (S.eval x)
      rw [abs_sub_comm (p.eval x) |x|] at h
      calc
        |p.eval x - S.eval x| ≤ |(|x|) - p.eval x| + |(|x|) - S.eval x| := h
        _ ≤ 2 / (Real.pi * (n + 1)) + 2 / (Real.pi * (n + 1)) :=
          add_le_add (herr x hx) hS
        _ = 4 / (Real.pi * (n + 1)) := by ring
    exact he.trans (div_le_div_of_nonneg_left (by norm_num)
      (mul_pos hπ hn) (by nlinarith))
  let c := Real.exp (n * |u.im|)
  have hc : 0 < c := Real.exp_pos _
  have hc1 : 1 ≤ c := Real.one_le_exp_iff.mpr (mul_nonneg hn.le (abs_nonneg _))
  have hdiffNorm := norm_eval_sin_le_mul_exp_abs_im hdiff hbound u
  have hdiffScaled : n * ‖((p - S).map Complex.ofRealHom).eval (Complex.sin u)‖ ≤
      4 / Real.pi * c := by
    have h := mul_le_mul_of_nonneg_left hdiffNorm hn.le
    change n * ‖((p - S).map Complex.ofRealHom).eval (Complex.sin u)‖ ≤
      n * (4 / (Real.pi * n) * c) at h
    have he : n * (4 / (Real.pi * n) * c) = 4 / Real.pi * c := by field_simp
    exact h.trans_eq he
  have hcomp := norm_eval_chebyshevTrunc_abs_even_sin_le m u
  rw [hnc] at hcomp
  have hcompScaled : n * ‖(S.map Complex.ofRealHom).eval (Complex.sin u)‖ ≤
      (2 / Real.pi + 16 * R^2 / (3 * Real.pi)) * c := by
    have h := mul_le_mul_of_nonneg_left hcomp hn.le
    have hconst : n * (2 / (Real.pi * (n + 1))) ≤ 2 / Real.pi := by
      apply (le_div_iff₀ hπ).mpr
      field_simp
      nlinarith
    have hsq : (n * ‖u‖)^2 ≤ (2 * R)^2 := pow_le_pow_left₀ (by positivity) hunorm 2
    have hquad : n * (8 * m / (3 * Real.pi) * ‖u‖^2 * c) ≤
        16 * R^2 / (3 * Real.pi) * c := by
      have h := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 4 / (3 * Real.pi) * c by positivity)
      calc
        n * (8 * m / (3 * Real.pi) * ‖u‖^2 * c) =
            (n * ‖u‖)^2 * (4 / (3 * Real.pi) * c) := by
          dsimp only [n]
          push_cast
          ring
        _ ≤ (2 * R)^2 * (4 / (3 * Real.pi) * c) := h
        _ = 16 * R^2 / (3 * Real.pi) * c := by ring
    change n * ‖(S.map Complex.ofRealHom).eval (Complex.sin u)‖ ≤
      n * (2 / (Real.pi * (n + 1)) + 8 * m / (3 * Real.pi) * ‖u‖^2 * c) at h
    have hconstc : n * (2 / (Real.pi * (n + 1))) ≤ 2 / Real.pi * c :=
      hconst.trans (le_mul_of_one_le_right (by positivity) hc1)
    nlinarith
  have htriangle : n * ‖(p.map Complex.ofRealHom).eval (Complex.sin u)‖ ≤
      n * ‖((p - S).map Complex.ofRealHom).eval (Complex.sin u)‖ +
        n * ‖(S.map Complex.ofRealHom).eval (Complex.sin u)‖ := by
    have he : (p.map Complex.ofRealHom).eval (Complex.sin u) =
        ((p - S).map Complex.ofRealHom).eval (Complex.sin u) +
          (S.map Complex.ofRealHom).eval (Complex.sin u) := by
      rw [Polynomial.map_sub, eval_sub]
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hn.le).trans_eq (mul_add _ _ _)
  have hpoly : n * ‖(p.map Complex.ofRealHom).eval (Complex.sin u)‖ ≤
      6 * (1 + R^2) / Real.pi * c := by
    have hconst : 4 / Real.pi + (2 / Real.pi + 16 * R^2 / (3 * Real.pi)) ≤
        6 * (1 + R^2) / Real.pi := by
      field_simp
      nlinarith [sq_nonneg R]
    have h := mul_le_mul_of_nonneg_right hconst hc.le
    nlinarith
  rw [hu] at hpoly
  rw [norm_mul, Complex.norm_natCast]
  refine hpoly.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr hum

end NLAlib
