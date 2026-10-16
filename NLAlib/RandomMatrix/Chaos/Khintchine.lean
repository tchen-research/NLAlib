import NLAlib.RandomMatrix.Chaos.BudgetBounds

/-!
# Iterated and strong subgaussian matrix-chaos bounds

The invariant product logarithm is converted to the advertised
`log(max(rows,cols)+coordinates)`. Both constants depend only on the degree.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, Theorems 2.4–2.5, with the
finite-Hermite and scalar-comparison reroutes recorded in the derivation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

/-- An explicit admissible degree-only constant for ordinary iterated matrix
Khintchine: `200^q (q+4)^(q/2)`.
atlas: matrix-chaos-iterated-khintchine (partial) -/
def chaosKhintchineConstant (q : ℕ) : ℝ :=
  200 ^ q * (q + 4 : ℝ) ^ ((q : ℝ) / 2)

/-- An explicit admissible degree-only constant for the advertised strong chaos
bound: `200^q (1 + q (q+4)^(q/2)/(2 log 2))`.
atlas: matrix-chaos-strong-khintchine (partial) -/
def chaosStrongKhintchineConstant (q : ℕ) : ℝ :=
  200 ^ q * (1 + (q : ℝ) * (q + 4 : ℝ) ^ ((q : ℝ) / 2) / (2 * Real.log 2))

/-- The ordinary chaos constant is positive and depends only on the degree.
atlas: matrix-chaos-iterated-khintchine (partial) -/
theorem chaosKhintchineConstant_pos (q : ℕ) : 0 < chaosKhintchineConstant q := by
  unfold chaosKhintchineConstant
  positivity

/-- The strong chaos constant is positive and depends only on the degree.
atlas: matrix-chaos-strong-khintchine (partial) -/
theorem chaosStrongKhintchineConstant_pos (q : ℕ) :
    0 < chaosStrongKhintchineConstant q := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold chaosStrongKhintchineConstant
  positivity

private theorem rpow_le_rpow_add_one_div_log_two {x s : ℝ}
    (hx : Real.log 2 ≤ x) : x ^ s ≤ x ^ (s + 1) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 < x := hlog.trans_le hx
  rw [le_div_iff₀ hlog, Real.rpow_add hx0, Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hx0.le _)

universe u
variable {τ ι m n : Type u} [Fintype τ] [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq τ] [DecidableEq ι] [DecidableEq m] [DecidableEq n]
  [Nonempty ι] [Nonempty m] [Nonempty n]
  (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

private theorem log_dimension_lower :
    Real.log 2 ≤ Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι) := by
  apply Real.log_le_log (by norm_num)
  have hm : (1 : ℝ) ≤ Fintype.card m := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card m ≠ 0))
  have hi : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card ι ≠ 0))
  linarith [le_max_left (Fintype.card m : ℝ) (Fintype.card n : ℝ)]

private theorem chaosLogBudget_le_dimension_log :
    chaosLogBudget τ ι m n ≤ (Fintype.card τ + 4 : ℝ) *
      Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι) := by
  have hm : (1 : ℝ) ≤ Fintype.card m := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card m ≠ 0))
  have hn : (1 : ℝ) ≤ Fintype.card n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card n ≠ 0))
  have hi : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card ι ≠ 0))
  simpa [chaosLogBudget, chaosDimensionProduct, Nat.cast_mul, Nat.cast_pow, mul_assoc] using
    Real.log_four_mul_mul_mul_pow_le hm hn hi (Fintype.card τ)

/-- The ordinary iterated noncommutative Khintchine bound for a genuine
decoupled subgaussian matrix chaos, with the explicit degree-only constant
`200^q (q+4)^(q/2)`. Centered coordinate laws with a common exponential-square
bound may vary with the coordinate index, strengthening the IID source; zero coefficient arrays
and the deterministic degree-zero endpoint are included.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, Theorem 2.4, upper bound.
atlas: matrix-chaos-iterated-khintchine -/
theorem expectedDecoupledMatrixChaosNorm_le_sigma_mul_log_rpow
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (A : (τ → ι) → Matrix m n ℝ) :
    expectedDecoupledMatrixChaosNorm ν A ≤
      chaosKhintchineConstant (Fintype.card τ) * K ^ Fintype.card τ *
        (Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι)) ^
          ((Fintype.card τ : ℝ) / 2) * chaosSigma A := by
  let s := (Fintype.card τ : ℝ) / 2
  let L := Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι)
  have hL0 : 0 ≤ L := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans
    (log_dimension_lower (ι := ι) (m := m) (n := n))
  have hB0 : 0 ≤ chaosLogBudget τ ι m n := by
    apply (Real.one_lt_log_four_mul _).le.trans' (by norm_num : (0 : ℝ) ≤ 1)
    have hp : 0 < chaosDimensionProduct τ ι m n := by
      unfold chaosDimensionProduct
      positivity
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hb : chaosLogBudget τ ι m n ^ s ≤
      (Fintype.card τ + 4 : ℝ) ^ s * L ^ s := by
    have h := Real.rpow_le_rpow hB0
      (chaosLogBudget_le_dimension_log (τ := τ) (ι := ι) (m := m) (n := n))
      (show 0 ≤ s by dsimp [s]; positivity)
    change chaosLogBudget τ ι m n ^ s ≤ ((Fintype.card τ + 4 : ℝ) * L) ^ s at h
    rwa [Real.mul_rpow (by positivity : (0 : ℝ) ≤ Fintype.card τ + 4) hL0] at h
  have h := (expectedDecoupledMatrixChaosNorm_le_budget ν K hK hcenter hpsi A).1
  apply h.trans
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb
      (pow_nonneg (show 0 ≤ 200 * K by positivity) (Fintype.card τ)))
    (chaosSigma_nonneg A)
  dsimp [s, L] at hmul
  convert hmul using 1 <;> simp only [chaosKhintchineConstant, mul_pow] <;> ring

/-- The full strong subgaussian matrix-chaos estimate, with a dimension-free
leading variance term and covariance error exponent `(q+2)/2`. Its explicit
positive constant depends only on the degree. The proof derives its linear
step from finite Gaussian Hermite matrices and scalar convex comparison.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, Theorem 2.5, via the reroute.
atlas: matrix-chaos-strong-khintchine -/
theorem expectedDecoupledMatrixChaosNorm_le_sigma_add_covariance_mul_log_rpow
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (A : (τ → ι) → Matrix m n ℝ) :
    expectedDecoupledMatrixChaosNorm ν A ≤
      chaosStrongKhintchineConstant (Fintype.card τ) * K ^ Fintype.card τ *
        (chaosSigma A +
          (Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι)) ^
            (((Fintype.card τ : ℝ) + 2) / 2) * chaosCovariance A) := by
  let q := Fintype.card τ
  let s := (q : ℝ) / 2
  let L := Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι)
  let b := (q : ℝ) / 2 * (q + 4 : ℝ) ^ s / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ L := log_dimension_lower (ι := ι) (m := m) (n := n)
  have hL0 : 0 ≤ L := hlog.le.trans hL
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hB0 : 0 ≤ chaosLogBudget τ ι m n := by
    apply (Real.one_lt_log_four_mul _).le.trans' (by norm_num : (0 : ℝ) ≤ 1)
    have hp : 0 < chaosDimensionProduct τ ι m n := by
      unfold chaosDimensionProduct
      positivity
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hb : chaosLogBudget τ ι m n ^ s ≤ (q + 4 : ℝ) ^ s * L ^ s := by
    have h := Real.rpow_le_rpow hB0
      (chaosLogBudget_le_dimension_log (τ := τ) (ι := ι) (m := m) (n := n))
      (show 0 ≤ s by dsimp [s]; positivity)
    change chaosLogBudget τ ι m n ^ s ≤ ((q + 4 : ℝ) * L) ^ s at h
    rwa [Real.mul_rpow (by positivity : (0 : ℝ) ≤ q + 4) hL0] at h
  have he : (q : ℝ) / 2 * chaosLogBudget τ ι m n ^ s ≤ b * L ^ (s + 1) := by
    calc
      _ ≤ (q : ℝ) / 2 * ((q + 4 : ℝ) ^ s * L ^ s) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (q : ℝ) / 2 * ((q + 4 : ℝ) ^ s * (L ^ (s + 1) / Real.log 2)) := by
        gcongr
        exact rpow_le_rpow_add_one_div_log_two hL
      _ = _ := by dsimp [b]; ring
  have hinner : chaosSigma A + (q : ℝ) / 2 * chaosLogBudget τ ι m n ^ s *
        chaosCovariance A ≤ (1 + b) * (chaosSigma A + L ^ (s + 1) * chaosCovariance A) := by
    have hv := mul_le_mul_of_nonneg_right he (chaosCovariance_nonneg A)
    have hσ := mul_nonneg hb0 (chaosSigma_nonneg A)
    have hcv := mul_nonneg (Real.rpow_nonneg hL0 (s + 1)) (chaosCovariance_nonneg A)
    nlinarith only [hv, hσ, hcv]
  have h := (expectedDecoupledMatrixChaosNorm_le_budget ν K hK hcenter hpsi A).2
  apply h.trans
  have hm := mul_le_mul_of_nonneg_left hinner
    (pow_nonneg (show 0 ≤ 200 * K by positivity) q)
  have hexp : s + 1 = ((Fintype.card τ : ℝ) + 2) / 2 := by dsimp [s, q]; ring
  rw [hexp] at hm
  convert hm using 1 <;> simp only [chaosStrongKhintchineConstant, mul_pow] <;>
    dsimp [b, s, q] <;> ring

end NLAlib
