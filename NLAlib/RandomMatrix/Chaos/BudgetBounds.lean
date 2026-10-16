import NLAlib.RandomMatrix.Chaos.Induction
import NLAlib.Probability.Concentration.Matrix.SubgaussianRectangularSeries

/-!
# Matrix-chaos estimates with the invariant dimension budget

The proved scalar Gaussian comparison and partial-transpose linear estimate
instantiate the simultaneous finite-array induction. The resulting stronger
covariance error has exponent `q/2` on the invariant logarithmic budget.
Source: the matrix-chaos reroute, §§4.4–4.5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

universe u

/-- The common logarithmic budget, four times the total scalar coefficient
dimension product. It is greater than one for all positive dimensions. -/
def chaosLogBudget (τ ι m n : Type*) [Fintype τ] [Fintype ι]
    [Fintype m] [Fintype n] : ℝ := Real.log (4 * chaosDimensionProduct τ ι m n)

private theorem sqrt_pow_eq_rpow_half {b : ℝ} (hb : 0 ≤ b) (q : ℕ) :
    Real.sqrt b ^ q = b ^ ((q : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  ring

variable {τ ι m n : Type u} [Fintype τ] [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq τ] [DecidableEq ι] [DecidableEq m] [DecidableEq n]
  [Nonempty ι] [Nonempty m] [Nonempty n]
  (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

/-- The full ordinary and strong chaos estimates follow from actual centered
coordinate laws with a common exponential-square moment bound. Constants are
`(200 K)^q`; the stronger covariance error is `(q/2) log(4 d1 d2 m^q)^(q/2) v`.
The zero-degree deterministic endpoint is included.
atlas: matrix-chaos-iterated-khintchine (partial)
atlas: matrix-chaos-strong-khintchine (partial) -/
theorem expectedDecoupledMatrixChaosNorm_le_budget
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (A : (τ → ι) → Matrix m n ℝ) :
    (expectedDecoupledMatrixChaosNorm ν A ≤
      (200 * K) ^ Fintype.card τ *
        chaosLogBudget τ ι m n ^ ((Fintype.card τ : ℝ) / 2) * chaosSigma A) ∧
    (expectedDecoupledMatrixChaosNorm ν A ≤
      (200 * K) ^ Fintype.card τ *
        (chaosSigma A + (Fintype.card τ : ℝ) / 2 *
          chaosLogBudget τ ι m n ^ ((Fintype.card τ : ℝ) / 2) * chaosCovariance A)) := by
  let D := chaosDimensionProduct τ ι m n
  let L := chaosLogBudget τ ι m n
  let t := Real.sqrt L
  have hD : 1 ≤ (D : ℝ) := by
    have hp : 0 < D := by dsimp [D, chaosDimensionProduct]; positivity
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hL : 1 ≤ L := (Real.one_lt_log_four_mul hD).le
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have ht : 1 ≤ t := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have ht2 : t ^ 2 = L := Real.sq_sqrt hL0
  have hν : ∀ i, Integrable id (ν i) := fun i =>
    (hasSubgaussianMGF_of_lintegral_exp_sq_le_two aemeasurable_id K hK
      (hcenter i) (hpsi i)).integrable
  have hdim (p r : Type u) [Fintype p] [Fintype r] [Nonempty p] [Nonempty r]
      (hpr : Fintype.card p * Fintype.card r ≤ D) :
      Real.log (2 * ((Fintype.card p : ℝ) + Fintype.card r)) ≤ t ^ 2 := by
    rw [ht2]
    apply Real.log_two_mul_add_le_log_four_mul
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card p ≠ 0)
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card r ≠ 0)
    · exact_mod_cast hpr
  have ho : ∀ (p r : Type u) [Fintype p] [Fintype r]
      [DecidableEq p] [DecidableEq r] [Nonempty p] [Nonempty r],
      Fintype.card p * Fintype.card r ≤ D → ∀ B : ι → Matrix p r ℝ,
      (∫ y, specNorm (∑ i, y i • B i) ∂Measure.pi ν) ≤
        ((100 * K) * t) * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)) := by
    intro p r _ _ _ _ _ _ hpr B
    exact integral_specNorm_subgaussian_rectangular_le ν K hK hcenter hpsi B ht (hdim p r hpr)
  have hs : ∀ (p r : Type u) [Fintype p] [Fintype r]
      [DecidableEq p] [DecidableEq r] [Nonempty p] [Nonempty r],
      Fintype.card p * Fintype.card r ≤ D → ∀ B : ι → Matrix p r ℝ,
      (∫ y, specNorm (∑ i, y i • B i) ∂Measure.pi ν) ≤
        (100 * K) * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)) +
          ((100 * K) * t) * specNorm (coefficientEntryRows B) := by
    intro p r _ _ _ _ _ _ hpr B
    exact integral_specNorm_subgaussian_rectangular_strong_le ν K hK hcenter hpsi B ht
      (hdim p r hpr)
  have h := expectedDecoupledMatrixChaosNorm_bounds_of_linear_bounds ν hν (100 * K) t
    (by positivity) ht D ho hs (Fintype.card τ) τ rfl m n A le_rfl
  have hconst : 2 * (100 * K) = 200 * K := by ring
  have hconstt : 2 * (100 * K) * t = (200 * K) * t := by ring
  rw [hconstt, hconst, mul_pow, sqrt_pow_eq_rpow_half hL0] at h
  exact h

end NLAlib
