import NLAlib.Matrix.Spectral.MatrixPowerReal

/-! # Powers after removing a fixed projector

The identity `(T-P)^k = T^k-P` holds for positive exponents when `P` is
idempotent and both products with `T` equal `P`. The zero exponent is handled
separately in the geometric norm estimate.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/

noncomputable section
open Filter
open scoped Matrix Topology
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Powers of a matrix act as the identity on a fixed right projector. -/
theorem matrix_pow_mul_eq_of_mul_eq {K : Type*} [Semiring K]
    (T P : Matrix ι ι K) (hTP : T * P = P) (k : ℕ) : T ^ k * P = P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Matrix.mul_assoc, hTP, ih]

/-- Removing a commuting fixed idempotent removes it from every positive power. -/
theorem matrix_sub_projector_pow_succ {K : Type*} [Ring K]
    (T P : Matrix ι ι K) (hPP : P * P = P) (hTP : T * P = P) (hPT : P * T = P)
    (k : ℕ) : (T - P) ^ (k + 1) = T ^ (k + 1) - P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      matrix_pow_mul_eq_of_mul_eq T P hTP, hPT, hPP, ← pow_succ]
    abel

open scoped Matrix.Norms.L2Operator in
/-- Subunit spectrum after deflation gives convergence to the projector.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem tendsto_matrix_pow_projector_of_deflated_spectralRadius_lt_one
    (T P : Matrix ι ι ℝ) (hPP : P * P = P) (hTP : T * P = P) (hPT : P * T = P)
    (hρ : spectralRadius ℂ ((T - P).map Complex.ofReal) < 1) :
    Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 P) := by
  have hzero := (tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one (T - P)).mpr hρ
  have hlim : Tendsto (fun k : ℕ => (T - P) ^ k + P) atTop (𝓝 P) := by
    simpa only [zero_add] using hzero.add_const P
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [show j.succ = j + 1 from rfl, matrix_sub_projector_pow_succ T P hPP hTP hPT]
  exact sub_add_cancel _ _

open scoped Matrix.Norms.L2Operator in
/-- Every rate above the deflated spectral radius controls every power error,
including exponent zero, with a finite constant. No diagonalizability is needed.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem exists_specNorm_matrix_pow_sub_projector_le_geometric
    (T P : Matrix ι ι ℝ) (hPP : P * P = P) (hTP : T * P = P) (hPT : P * T = P)
    {θ : ℝ} (hθ : (spectralRadius ℂ ((T - P).map Complex.ofReal)).toReal < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, specNorm (T ^ k - P) ≤ C * θ ^ k := by
  have hθpos : 0 < θ := ENNReal.toReal_nonneg.trans_lt hθ
  obtain ⟨N, hN⟩ := exists_prefix_specNorm_real_matrix_pow_le_complex_spectralRadius_add
    (T - P) (sub_pos.mpr hθ)
  have hN' (k : ℕ) : specNorm ((T - P) ^ k) ≤
      matrixPowerBoundConstant ((T - P).map Complex.ofReal) θ N * θ ^ k := by
    simpa only [add_sub_cancel] using hN k
  let c := matrixPowerBoundConstant ((T - P).map Complex.ofReal) θ N
  have hc : 0 ≤ c := zero_le_one.trans (one_le_matrixPowerBoundConstant _ hθpos N)
  refine ⟨specNorm (1 - P) + c, add_nonneg (specNorm_nonneg _) hc, fun k => ?_⟩
  cases k with
  | zero => simp only [pow_zero, mul_one]; exact le_add_of_nonneg_right hc
  | succ k =>
    rw [← matrix_sub_projector_pow_succ T P hPP hTP hPT]
    exact (hN' _).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (specNorm_nonneg _)) (pow_nonneg hθpos.le _))

end NLAlib
