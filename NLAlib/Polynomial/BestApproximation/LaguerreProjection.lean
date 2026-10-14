import NLAlib.Polynomial.OrthogonalPolynomials.LaguerreMeasure

/-!
# Finite Laguerre projection of the growing exponential

The finite Gram identity gives the exact least-square residual used in the
reciprocal exponential approximation certificate. No infinite Laguerre expansion
or best rational approximation is assumed.
Source: reciprocal exponential certificates (RC6)--(RC8).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
open scoped Nat
namespace NLAlib

/-- The exact Fourier--Laguerre coefficient of `exp (x/4)`.
Source: reciprocal exponential certificate (RC6). -/
def laguerreExponentialCoefficient (j : ℕ) : ℝ := 4 * (-1 : ℝ)^j / 3^(j+1)

/-- The degree-`n` finite Laguerre projection of `exp (x/4)`.
Source: reciprocal exponential certificate (RC8). -/
def laguerreExponentialProjection (n : ℕ) : ℝ[X] :=
  ∑ j : Fin (n + 1), laguerreExponentialCoefficient j.val • laguerrePolynomial j.val

private theorem moment_laguerrePolynomial_three_quarters (j : ℕ) :
    exponentialPolynomialMoment (3/4) (laguerrePolynomial j) =
      laguerreExponentialCoefficient j := by
  rw [exponentialPolynomialMoment_laguerrePolynomial (by norm_num)]
  rw [laguerreExponentialCoefficient, show (3 : ℝ)/4 - 1 = (-1)/4 by norm_num]
  rw [div_pow, div_pow, pow_succ]
  field_simp
  ring

/-- The finite Laguerre projection is degree bounded.
Source: reciprocal exponential certificate (RC8). -/
theorem degree_laguerreExponentialProjection_le (n : ℕ) :
    (laguerreExponentialProjection n).degree ≤ n := by
  apply mem_degreeLE.mp
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  apply mem_degreeLE.mpr
  rw [degree_laguerrePolynomial]
  exact_mod_cast Nat.le_of_lt_succ j.isLt

/-- The finite Laguerre projection has a positive explicit top coefficient.
Source: the explicit reciprocal denominator reroute. -/
theorem coeff_laguerreExponentialProjection_self (n : ℕ) :
    (laguerreExponentialProjection n).coeff n = 4 / (3^(n+1) * (n ! : ℝ)) := by
  rw [laguerreExponentialProjection, finsetSum_coeff, Finset.sum_eq_single (Fin.last n)]
  · simp only [coeff_smul, Fin.val_last, smul_eq_mul, coeff_laguerrePolynomial_self,
      laguerreExponentialCoefficient]
    have hsign : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by rw [← mul_pow]; norm_num
    field_simp
    nlinarith [hsign]
  · intro j _ hj
    have hjn : j.val < n := by
      have hjne : j.val ≠ n := fun h => hj (Fin.ext h)
      omega
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by simpa using hjn), smul_zero]
  · simp

/-- The Laguerre moment of the finite projection equals its exact coefficient.
Source: reciprocal exponential certificate (RC6)--(RC8). -/
theorem exponentialPolynomialMoment_laguerreExponentialProjection_mul
    (n : ℕ) (i : Fin (n+1)) :
    exponentialPolynomialMoment 1
      (laguerreExponentialProjection n * laguerrePolynomial i.val) =
      laguerreExponentialCoefficient i.val := by
  rw [laguerreExponentialProjection, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, map_smul,
    exponentialPolynomialMoment_laguerrePolynomial_mul_laguerrePolynomial]
  simp [← Fin.ext_iff]

/-- On all degree-`n` polynomials, the finite projection represents the
Laplace functional with weight `exp (-3*x/4)`.
Source: reciprocal exponential certificate (RC8), finite orthogonal projection. -/
theorem exponentialPolynomialMoment_laguerreExponentialProjection_mul_eq
    {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    exponentialPolynomialMoment 1 (laguerreExponentialProjection n * p) =
      exponentialPolynomialMoment (3/4) p := by
  obtain ⟨a, rfl⟩ := exists_sum_smul_laguerrePolynomial hp
  rw [Finset.mul_sum, map_sum, map_sum]
  simp_rw [mul_smul_comm, map_smul,
    exponentialPolynomialMoment_laguerreExponentialProjection_mul,
    moment_laguerrePolynomial_three_quarters]

private theorem sum_sq_laguerreExponentialCoefficient (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), (laguerreExponentialCoefficient j)^2) =
      2 - 2 / 3^(2*n+2) := by
  induction n with
  | zero => norm_num [laguerreExponentialCoefficient]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hsign : ((-1 : ℝ)^(n+1))^2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    simp only [laguerreExponentialCoefficient, div_pow, mul_pow, hsign]
    have hpow : (3 : ℝ)^(2*(n+1)+2) = 9 * 3^(2*n+2) := by
      rw [show 2*(n+1)+2 = (2*n+2)+2 by omega, pow_add]
      norm_num
      ring
    have hpow' : ((3 : ℝ)^(n+1+1))^2 = 3^(2*n+2)*9 := by
      rw [← pow_mul, show (n+1+1)*2 = (2*n+2)+2 by omega, pow_add]
      norm_num
    rw [hpow, hpow']
    field_simp
    ring

/-- The squared exponential norm of the finite projection is the exact finite
geometric sum. Source: reciprocal exponential certificate (RC8). -/
theorem exponentialPolynomialMoment_laguerreExponentialProjection_sq (n : ℕ) :
    exponentialPolynomialMoment 1 ((laguerreExponentialProjection n)^2) =
      2 - 2 / 3^(2*n+2) := by
  rw [pow_two]
  rw [show laguerreExponentialProjection n * laguerreExponentialProjection n =
    laguerreExponentialProjection n *
      (∑ j : Fin (n+1), laguerreExponentialCoefficient j.val • laguerrePolynomial j.val)
    by rfl]
  rw [Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, map_smul,
    exponentialPolynomialMoment_laguerreExponentialProjection_mul, smul_eq_mul]
  simp only [← pow_two]
  rw [Fin.sum_univ_eq_sum_range (fun j => (laguerreExponentialCoefficient j)^2) (n+1)]
  exact sum_sq_laguerreExponentialCoefficient n

private theorem exp_quarter_sub_eval_sq_mul_exp_neg (p : ℝ[X]) (x : ℝ) :
    (Real.exp (x/4) - p.eval x)^2 * Real.exp (-x) =
      Real.exp (-((1/2)*x)) - 2 * (p.eval x * Real.exp (-((3/4)*x))) +
        (p^2).eval x * Real.exp (-x) := by
  have h1 : (Real.exp (x/4))^2 * Real.exp (-x) = Real.exp (-((1/2)*x)) := by
    rw [pow_two, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (x/4) * Real.exp (-x) = Real.exp (-((3/4)*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Polynomial.eval_pow]
  calc
    _ = (Real.exp (x/4))^2 * Real.exp (-x) -
        2 * (p.eval x * (Real.exp (x/4) * Real.exp (-x))) +
        (p.eval x)^2 * Real.exp (-x) := by ring
    _ = _ := by rw [h1, h2]

/-- The finite growing-exponential residual has finite exponential square norm.
Source: reciprocal exponential certificate (RC8). -/
theorem integrableOn_exp_quarter_sub_eval_sq_mul_exp_neg (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => (Real.exp (x/4) - p.eval x)^2 * Real.exp (-x))
      (Ioi 0) := by
  have h0 := integrableOn_pow_mul_exp_neg_mul_Ioi 0 (by norm_num : 0 < (1:ℝ)/2)
  simp only [pow_zero, one_mul] at h0
  have h1 := (integrableOn_eval_mul_exp_neg_mul_Ioi p
    (by norm_num : 0 < (3:ℝ)/4)).const_mul 2
  have h2 := integrableOn_eval_mul_exp_neg_mul_Ioi (p^2) zero_lt_one
  simp only [one_mul] at h2
  exact ((h0.sub h1).add h2).congr_fun
    (fun x _ => (exp_quarter_sub_eval_sq_mul_exp_neg p x).symm) measurableSet_Ioi

/-- The growing-exponential squared residual has a finite moment expansion.
Source: reciprocal exponential certificate (RC8), square expansion. -/
theorem integral_exp_quarter_sub_eval_sq_mul_exp_neg (p : ℝ[X]) :
    (∫ x : ℝ in Ioi 0, (Real.exp (x/4) - p.eval x)^2 * Real.exp (-x)) =
      2 - 2 * exponentialPolynomialMoment (3/4) p +
        exponentialPolynomialMoment 1 (p^2) := by
  simp_rw [exp_quarter_sub_eval_sq_mul_exp_neg]
  have h0 := integrableOn_pow_mul_exp_neg_mul_Ioi 0 (by norm_num : 0 < (1:ℝ)/2)
  simp only [pow_zero, one_mul] at h0
  have h1 := (integrableOn_eval_mul_exp_neg_mul_Ioi p
    (by norm_num : 0 < (3:ℝ)/4)).const_mul 2
  have h2 := integrableOn_eval_mul_exp_neg_mul_Ioi (p^2) zero_lt_one
  simp only [one_mul] at h2
  have hadd := integral_add (h0.sub h1) h2
  simp only [Pi.sub_apply] at hadd
  rw [hadd]
  have hsub := integral_sub h0 h1
  rw [hsub, integral_const_mul]
  have he : (∫ x : ℝ in Ioi 0, Real.exp (-((1/2)*x))) = 2 := by
    simpa using integral_pow_mul_exp_neg_mul_Ioi 0 (by norm_num : 0 < (1:ℝ)/2)
  rw [he, integral_eval_mul_exp_neg_mul_Ioi p (by norm_num)]
  rw [show (∫ x : ℝ in Ioi 0, (p^2).eval x * Real.exp (-x)) =
    exponentialPolynomialMoment 1 (p^2) by
    simpa only [one_mul] using integral_eval_mul_exp_neg_mul_Ioi (p^2) zero_lt_one]

/-- The exact finite Laguerre residual identity: the degree-`n` projection has
squared residual `2/3^(2n+2)`, and every competitor adds its nonnegative squared
distance from that projection. Source: reciprocal exponential certificate (RC8).
atlas: exp-rational-halfline (partial) -/
theorem integral_exp_quarter_sub_eval_sq_eq_laguerreResidual_add
    {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    (∫ x : ℝ in Ioi 0, (Real.exp (x/4) - p.eval x)^2 * Real.exp (-x)) =
      2 / 3^(2*n+2) +
        ∫ x : ℝ in Ioi 0, (p.eval x - (laguerreExponentialProjection n).eval x)^2 *
          Real.exp (-x) := by
  rw [integral_exp_quarter_sub_eval_sq_mul_exp_neg]
  have hpoly : (p - laguerreExponentialProjection n)^2 = p^2 -
      (2 : ℝ) • (laguerreExponentialProjection n * p) +
      (laguerreExponentialProjection n)^2 := by
    simp only [smul_eq_C_mul, map_ofNat]
    ring
  have hint : (∫ x : ℝ in Ioi 0,
      (p.eval x - (laguerreExponentialProjection n).eval x)^2 * Real.exp (-x)) =
      exponentialPolynomialMoment 1 ((p - laguerreExponentialProjection n)^2) := by
    have h := integral_eval_mul_exp_neg_mul_Ioi ((p - laguerreExponentialProjection n)^2)
      zero_lt_one
    simp_rw [Polynomial.eval_pow, Polynomial.eval_sub, one_mul] at h
    exact h
  rw [hint, hpoly, map_add, map_sub, map_smul,
    exponentialPolynomialMoment_laguerreExponentialProjection_mul_eq hp,
    exponentialPolynomialMoment_laguerreExponentialProjection_sq]
  simp only [smul_eq_mul]
  ring

/-- Every degree-`n` polynomial has growing-exponential squared residual at least
`2/3^(2n+2)`. Source: reciprocal exponential certificate (RC8).
atlas: exp-rational-halfline (partial) -/
theorem laguerreResidual_le_integral_exp_quarter_sub_eval_sq
    {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    2 / 3^(2*n+2) ≤
      ∫ x : ℝ in Ioi 0, (Real.exp (x/4) - p.eval x)^2 * Real.exp (-x) := by
  rw [integral_exp_quarter_sub_eval_sq_eq_laguerreResidual_add hp]
  apply le_add_of_nonneg_right
  apply integral_nonneg
  intro x
  positivity

end NLAlib
