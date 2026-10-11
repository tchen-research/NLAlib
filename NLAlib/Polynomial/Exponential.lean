import NLAlib.Polynomial.Monomial
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Explicit low-degree approximation of the exponential

The finite Chebyshev compression of the exponential series gives the degree bound of
Sachdeva–Vishnoi, Theorem 4.1 (atlas `exp-polynomial-approx`).
-/

noncomputable section

open Polynomial Finset Real

namespace NLAlib

/-- The scalar exponential is the sum of its factorial power series.
Mathlib's general Banach-algebra theorem, specialized to reals; used by
Sachdeva–Vishnoi, Theorem 4.1 (`exp-polynomial-approx`). -/
theorem hasSum_pow_div_factorial_exp (x : ℝ) :
    HasSum (fun i : ℕ => x ^ i / (i.factorial : ℝ)) (exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- A nonnegative exponential-series tail is at most the full series.
Source: exponential power series, used by Sachdeva–Vishnoi, Theorem 4.1
(`exp-polynomial-approx`). -/
theorem tsum_pow_div_factorial_nat_add_le_exp {x : ℝ} (hx : 0 ≤ x) (t : ℕ) :
    (∑' i : ℕ, x ^ (i + t) / ((i + t).factorial : ℝ)) ≤ exp x := by
  have hsum := hasSum_pow_div_factorial_exp x
  have h := hsum.summable.sum_add_tsum_nat_add t
  rw [hsum.tsum_eq] at h
  have hn : 0 ≤ ∑ i ∈ range t, x ^ i / (i.factorial : ℝ) :=
    sum_nonneg fun i _ => by positivity
  linarith

/-- Exponential tilting with parameter two bounds the factorial series tail by `exp(-t)`
when `t ≥ exp(2) ℓ`; this avoids any probability-space construction.
Source: Sachdeva–Vishnoi, Theorem 4.1; operator rederivations `pg:exp-series-tail`.
The displayed bound is the second inequality of that lemma.
Atlas `exp-polynomial-approx` (helper). -/
theorem exp_neg_mul_tsum_pow_div_factorial_nat_add_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (t : ℕ) (ht : exp 2 * ℓ ≤ (t : ℝ)) :
    exp (-ℓ) * (∑' i : ℕ, ℓ ^ (i + t) / ((i + t).factorial : ℝ)) ≤ exp (-(t : ℝ)) := by
  have hsℓ := ((summable_nat_add_iff t).mpr (hasSum_pow_div_factorial_exp ℓ).summable)
  have hsx := ((summable_nat_add_iff t).mpr
    (hasSum_pow_div_factorial_exp (ℓ * exp 2)).summable)
  have hterm : ∀ i : ℕ, ℓ ^ (i + t) / ((i + t).factorial : ℝ) ≤
      exp (-2 * (t : ℝ)) * ((ℓ * exp 2) ^ (i + t) / ((i + t).factorial : ℝ)) := by
    intro i
    have he : 1 ≤ exp (-2 * (t : ℝ)) * (exp 2) ^ (i + t) := by
      rw [← exp_nat_mul, ← exp_add]
      apply one_le_exp_iff.mpr
      push_cast
      nlinarith
    rw [mul_pow]
    have hp : 0 ≤ ℓ ^ (i + t) / ((i + t).factorial : ℝ) := by positivity
    have heq : exp (-2 * (t : ℝ)) *
        (ℓ ^ (i + t) * exp 2 ^ (i + t) / ((i + t).factorial : ℝ)) =
        (exp (-2 * (t : ℝ)) * exp 2 ^ (i + t)) *
          (ℓ ^ (i + t) / ((i + t).factorial : ℝ)) := by ring
    rw [heq]
    exact le_mul_of_one_le_left hp he
  have htail := hsℓ.tsum_le_tsum hterm (hsx.mul_left (exp (-2 * (t : ℝ))))
  rw [tsum_mul_left] at htail
  have hfull := tsum_pow_div_factorial_nat_add_le_exp
    (show 0 ≤ ℓ * exp 2 by positivity) t
  have h : exp (-ℓ) * (∑' i : ℕ, ℓ ^ (i + t) / ((i + t).factorial : ℝ)) ≤
      exp (-ℓ) * (exp (-2 * (t : ℝ)) * exp (ℓ * exp 2)) :=
    (mul_le_mul_of_nonneg_left htail (by positivity)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfull (by positivity))
        (by positivity))
  refine h.trans ?_
  rw [← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  nlinarith

/-- Absolute error of an exponential-series truncation, bounded by a nonnegative factorial
tail on `|u| ≤ ℓ`. Source: Sachdeva–Vishnoi, Theorem 4.1 (`exp-polynomial-approx`). -/
theorem abs_exp_sub_sum_pow_div_factorial_le {ℓ u : ℝ} (_hℓ : 0 ≤ ℓ) (hu : |u| ≤ ℓ)
    (t : ℕ) :
    |exp u - ∑ i ∈ range t, u ^ i / (i.factorial : ℝ)| ≤
      ∑' i : ℕ, ℓ ^ (i + t) / ((i + t).factorial : ℝ) := by
  have hsu := hasSum_pow_div_factorial_exp u
  have hsℓ := (summable_nat_add_iff t).mpr (hasSum_pow_div_factorial_exp ℓ).summable
  have hterm : ∀ i : ℕ, ‖u ^ (i + t) / ((i + t).factorial : ℝ)‖ ≤
      ℓ ^ (i + t) / ((i + t).factorial : ℝ) := by
    intro i
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg (i + t).factorial : (0 : ℝ) ≤ (i + t).factorial)]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hu _) (Nat.cast_nonneg _)
  have hsn : Summable (fun i : ℕ => ‖u ^ (i + t) / ((i + t).factorial : ℝ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsℓ
  have hsplit := hsu.summable.sum_add_tsum_nat_add t
  rw [hsu.tsum_eq] at hsplit
  have heq : exp u - ∑ i ∈ range t, u ^ i / (i.factorial : ℝ) =
      ∑' i : ℕ, u ^ (i + t) / ((i + t).factorial : ℝ) := by linarith
  rw [heq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hterm hsℓ)

/-- The degree-`d` Chebyshev compression of the first `t` exponential-series terms.
Source: Sachdeva–Vishnoi, Theorem 4.1 (`exp-polynomial-approx`). -/
def exponentialChebyshevApprox (ℓ : ℝ) (t d : ℕ) : ℝ[X] :=
  C (exp (-ℓ)) * ∑ i ∈ range t,
    C ((-ℓ) ^ i / (i.factorial : ℝ)) * monomialChebyshevApprox i d

/-- The compressed exponential-series polynomial has degree at most `d`.
Source: Sachdeva–Vishnoi, Theorem 4.1 (`exp-polynomial-approx`). -/
theorem degree_exponentialChebyshevApprox_le (ℓ : ℝ) (t d : ℕ) :
    (exponentialChebyshevApprox ℓ t d).degree ≤ d := by
  unfold exponentialChebyshevApprox
  rw [C_mul']
  refine (degree_smul_le _ _).trans ((degree_sum_le _ _).trans ?_)
  refine Finset.sup_le fun i _ => ?_
  rw [C_mul']
  exact (degree_smul_le _ _).trans (degree_monomialChebyshevApprox_le i d)

/-- A finite initial segment of a nonnegative exponential series is at most the full sum.
Source: exponential series, used by Sachdeva–Vishnoi, Theorem 4.1 (`exp-polynomial-approx`). -/
theorem sum_pow_div_factorial_le_exp {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (t : ℕ) :
    (∑ i ∈ range t, ℓ ^ i / (i.factorial : ℝ)) ≤ exp ℓ := by
  have hs := hasSum_pow_div_factorial_exp ℓ
  exact (hs.summable.sum_le_tsum (range t) (fun i _ => by positivity)).trans_eq hs.tsum_eq

/-- The Chebyshev-compressed exponential has error at most the factorial tail plus the
uniform monomial-compression error.
Source: Sachdeva–Vishnoi, Theorem 4.1; operator rederivations `pg:exponential`.
Atlas `exp-polynomial-approx` (helper). -/
theorem abs_exp_sub_eval_exponentialChebyshevApprox_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    {t : ℕ} (_ht0 : 0 < t) (ht : exp 2 * ℓ ≤ (t : ℝ)) (d : ℕ) {y : ℝ}
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |exp (-ℓ) * exp (-ℓ * y) - (exponentialChebyshevApprox ℓ t d).eval y| ≤
      exp (-(t : ℝ)) + 2 * exp (-(d : ℝ) ^ 2 / (2 * t)) := by
  let E := 2 * exp (-(d : ℝ) ^ 2 / (2 * t))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hmono : ∀ i ∈ range t, |y ^ i - (monomialChebyshevApprox i d).eval y| ≤ E := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa only [pow_zero, monomialChebyshevApprox_zero, eval_one, sub_self, abs_zero] using hE
    · have h := abs_pow_sub_eval_monomialChebyshevApprox_le hi0 d hy
      refine h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num))
      have hit : (i : ℝ) ≤ t := by exact_mod_cast (mem_range.mp hi).le
      have hip : (0 : ℝ) < i := by exact_mod_cast hi0
      have hdiv := div_le_div_of_nonneg_left (sq_nonneg (d : ℝ))
        (show (0 : ℝ) < 2 * i by positivity) (show (2 : ℝ) * i ≤ 2 * t by linarith)
      simpa [neg_div] using neg_le_neg hdiv
  let S := ∑ i ∈ range t, (-ℓ * y) ^ i / (i.factorial : ℝ)
  let V := ∑ i ∈ range t, ((-ℓ) ^ i / (i.factorial : ℝ)) *
    (monomialChebyshevApprox i d).eval y
  have hdiff : S - V = ∑ i ∈ range t, ((-ℓ) ^ i / (i.factorial : ℝ)) *
      (y ^ i - (monomialChebyshevApprox i d).eval y) := by
    dsimp [S, V]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rw [mul_pow]
    ring
  have hcompress : |S - V| ≤ E * (∑ i ∈ range t, ℓ ^ i / (i.factorial : ℝ)) := by
    rw [hdiff, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hℓ,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hmono i hi) (by positivity)).trans_eq (mul_comm _ _)
  have hu : |-ℓ * y| ≤ ℓ := by
    rw [abs_mul, abs_neg, abs_of_nonneg hℓ]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr hy) hℓ).trans_eq (mul_one _)
  have hTaylor := abs_exp_sub_sum_pow_div_factorial_le hℓ hu t
  change |exp (-ℓ * y) - S| ≤ _ at hTaylor
  have htail := exp_neg_mul_tsum_pow_div_factorial_nat_add_le hℓ t ht
  have hfirst := (mul_le_mul_of_nonneg_left hTaylor (by positivity)).trans htail
  have hweight : exp (-ℓ) * (∑ i ∈ range t, ℓ ^ i / (i.factorial : ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le_exp hℓ t)
      (show 0 ≤ exp (-ℓ) by positivity)
    simpa [← exp_add] using h
  have hsecond : exp (-ℓ) * |S - V| ≤ E := by
    have h1 := mul_le_mul_of_nonneg_left hcompress (show 0 ≤ exp (-ℓ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hweight hE
    nlinarith
  have htri := abs_sub_le (exp (-ℓ * y)) S V
  have hfinal := mul_le_mul_of_nonneg_left htri (show 0 ≤ exp (-ℓ) by positivity)
  have hev : (exponentialChebyshevApprox ℓ t d).eval y = exp (-ℓ) * V := by
    simp only [exponentialChebyshevApprox, eval_mul, eval_C, eval_finsetSum, V]
  rw [hev, ← mul_sub, abs_mul, abs_of_pos (exp_pos _)]
  dsimp [E] at hsecond
  nlinarith

/-- The explicit Taylor cutoff `ceil(max(e² b/2, log(2/δ)))` for approximating `exp(-x)`.
Source: Sachdeva–Vishnoi, Theorem 4.1; explicit constants in operator rederivations
`pg:exponential`. Atlas `exp-polynomial-approx` (definition). -/
def exponentialApproxCutoff (b δ : ℝ) : ℕ :=
  ⌈max (exp 1 ^ 2 * b / 2) (log (2 / δ))⌉₊

/-- The explicit compressed degree `ceil(sqrt(2t log(4/δ)))`.
Source: Sachdeva–Vishnoi, Theorem 4.1; operator rederivations `pg:exponential`.
Atlas `exp-polynomial-approx` (definition). -/
def exponentialApproxDegree (b δ : ℝ) : ℕ :=
  ⌈sqrt (2 * exponentialApproxCutoff b δ * log (4 / δ))⌉₊

/-- The explicitly defined polynomial approximating `exp(-x)` on `[0,b]`.
Source: Sachdeva–Vishnoi, Theorem 4.1; operator rederivations `pg:exponential`.
Atlas `exp-polynomial-approx` (definition). -/
def exponentialApprox (b δ : ℝ) : ℝ[X] :=
  (exponentialChebyshevApprox (b / 2) (exponentialApproxCutoff b δ)
    (exponentialApproxDegree b δ)).comp (C (2 / b) * X - 1)

/-- Affine rescaling preserves the compressed degree upper bound.
Source: Sachdeva–Vishnoi, Theorem 4.1 (`exp-polynomial-approx`). -/
theorem degree_exponentialApprox_le (b δ : ℝ) :
    (exponentialApprox b δ).degree ≤ exponentialApproxDegree b δ := by
  apply degree_le_of_natDegree_le
  unfold exponentialApprox
  refine natDegree_comp_le.trans ?_
  have h1 := natDegree_le_of_degree_le
    (degree_exponentialChebyshevApprox_le (b / 2) (exponentialApproxCutoff b δ)
      (exponentialApproxDegree b δ))
  have h2 : (C (2 / b) * X - 1 : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    · simp
  nlinarith

/-- The explicit polynomial with the source's two ceiling parameters approximates `exp(-x)`
within `δ` on `[0,b]`, for `b>0` and `0<δ≤1`.
Source: Sachdeva–Vishnoi, Theorem 4.1; operator rederivations `pg:exponential` supplies the
displayed ceilings. Its proof uses only the genuine finite monomial approximation and
factorial exponential series, with no assumed approximation or coefficient-decay premise.
atlas: exp-polynomial-approx -/
theorem abs_exp_neg_sub_eval_exponentialApprox_le {b δ : ℝ} (hb : 0 < b)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) b) :
    |exp (-x) - (exponentialApprox b δ).eval x| ≤ δ := by
  let t := exponentialApproxCutoff b δ
  let d := exponentialApproxDegree b δ
  have hcut : max (exp 1 ^ 2 * b / 2) (log (2 / δ)) ≤ (t : ℝ) := Nat.le_ceil _
  have ht : exp 2 * (b / 2) ≤ (t : ℝ) := by
    have hexp : exp 2 = exp 1 ^ 2 := by rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add, sq]
    rw [hexp]
    have h := (le_max_left (exp 1 ^ 2 * b / 2) (log (2 / δ))).trans hcut
    nlinarith
  have ht0 : 0 < t := by
    have hpos : 0 < exp 1 ^ 2 * b / 2 := by positivity
    have hp := hpos.trans_le ((le_max_left _ _).trans hcut)
    exact_mod_cast hp
  have htlog : log (2 / δ) ≤ (t : ℝ) := (le_max_right _ _).trans hcut
  have hlog4 : 0 ≤ log (4 / δ) := log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hroot : sqrt (2 * (t : ℝ) * log (4 / δ)) ≤ (d : ℝ) := Nat.le_ceil _
  have hd : 2 * (t : ℝ) * log (4 / δ) ≤ (d : ℝ) ^ 2 := by
    have hs := sq_sqrt (show 0 ≤ 2 * (t : ℝ) * log (4 / δ) by positivity)
    have hn := sqrt_nonneg (2 * (t : ℝ) * log (4 / δ))
    nlinarith
  have hTaylor : exp (-(t : ℝ)) ≤ δ / 2 := by
    have h := exp_le_exp.mpr (neg_le_neg htlog)
    rw [exp_neg, exp_neg, exp_log (by positivity : 0 < 2 / δ), inv_div] at h
    simpa only [exp_neg] using h
  have hcompression : 2 * exp (-(d : ℝ) ^ 2 / (2 * t)) ≤ δ / 2 := by
    have he : -(d : ℝ) ^ 2 / (2 * t) ≤ -log (4 / δ) := by
      rw [div_le_iff₀ (show (0 : ℝ) < 2 * t by positivity)]
      nlinarith
    have h := exp_le_exp.mpr he
    rw [exp_neg, exp_log (by positivity : 0 < 4 / δ), inv_div] at h
    nlinarith
  have hy : 2 / b * x - 1 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [div_mul_cancel₀ (2 : ℝ) hb.ne',
      mul_nonneg (show 0 ≤ 2 / b by positivity) hx.1,
      mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ 2 / b by positivity)]
  have h := abs_exp_sub_eval_exponentialChebyshevApprox_le
    (show 0 ≤ b / 2 by positivity) ht0 ht d hy
  have hexp : exp (-(b / 2)) * exp (-(b / 2) * (2 / b * x - 1)) = exp (-x) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  rw [hexp] at h
  have hev : (exponentialApprox b δ).eval x =
      (exponentialChebyshevApprox (b / 2) t d).eval (2 / b * x - 1) := by
    simp only [exponentialApprox, eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one, t, d]
  rw [hev]
  linarith

/-- Exponential approximation in the existential polynomial interface, with the exact source
degree `ceil(sqrt(2t log(4/δ)))` and `t=ceil(max(e²b/2,log(2/δ)))`.
Source: Sachdeva–Vishnoi, Theorem 4.1; operator rederivations `pg:exponential`.
atlas: exp-polynomial-approx -/
theorem exists_degree_le_abs_exp_neg_sub_eval_le {b δ : ℝ} (hb : 0 < b)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ p : ℝ[X], p.degree ≤ exponentialApproxDegree b δ ∧
      ∀ x ∈ Set.Icc (0 : ℝ) b, |exp (-x) - p.eval x| ≤ δ :=
  ⟨exponentialApprox b δ, degree_exponentialApprox_le b δ,
    fun _ hx => abs_exp_neg_sub_eval_exponentialApprox_le hb hδ hδ1 hx⟩

end NLAlib
