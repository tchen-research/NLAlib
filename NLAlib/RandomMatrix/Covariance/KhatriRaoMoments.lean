import NLAlib.Probability.Moments.GaussianRadialization
import NLAlib.ForMathlib.MeasureTheory.WeightedCauchySchwarz
import NLAlib.ForMathlib.Analysis.FactorialMomentBounds
import Mathlib.MeasureTheory.Function.L2Space

/-! # Direction-preserving covariance moment budgets

Scalar directional moments and independent Gaussian averaging bound a rank-one
matrix moment in each test direction. Source: Heidary, *The Sharp Logarithmic
Cost of Khatri--Rao Subspace Embeddings*, Appendix `appendix:factorial`.
Atlas: `khatri-rao-sharp-growth`.
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

/-- Cauchy--Schwarz and Gaussian averaging retain a test direction in a raw
rank-one covariance moment. The returned scalar expression is the quadratic
form of the expected matrix power `E[(y yᵀ)^p]`.
Source: the radialization route of Heidary, Appendix `appendix:factorial`,
with a coarser higher-moment Cauchy--Schwarz bound.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_sq_integral_rankOneProbe_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {r p : ℕ} (hr : 1 ≤ r) (hp : 2 ≤ p) (y : Ω → Fin r → ℝ)
    (hy : Measurable y) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfour : ∀ a : Fin r → ℝ,
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ 4) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ 4 ∂μ) ≤ A * (a ⬝ᵥ a) ^ 2)
    (hhigh : ∀ a : Fin r → ℝ,
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ (2 * (2 * p - 2))) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ (2 * (2 * p - 2)) ∂μ) ≤
          B * (a ⬝ᵥ a) ^ (2 * p - 2))
    (x : Fin r → ℝ) :
    Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2) μ ∧
      (∫ ω, (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ^ 2 ≤
        (A * (x ⬝ᵥ x) ^ 2) *
          (B * gaussianRadialMoment r (2 * p - 2) / gaussianEvenMoment (2 * p - 2)) := by
  have hrad := integrable_and_gaussianEvenMoment_mul_integral_dotProduct_self_pow_le
    hr (by omega) y hy hB hhigh
  let f : Ω → ℝ := fun ω => (y ω ⬝ᵥ y ω) ^ (p - 1)
  let g : Ω → ℝ := fun ω => (x ⬝ᵥ y ω) ^ 2
  have hfi : Integrable (fun ω => f ω ^ 2) μ := by
    simpa only [f, ← pow_mul, show (p - 1) * 2 = 2 * p - 2 by omega] using hrad.1
  have hgi : Integrable (fun ω => g ω ^ 2) μ := by
    simpa only [g, ← pow_mul] using (hfour x).1
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq (by dsimp [f]; fun_prop)).2 hfi
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq (by dsimp [g]; fun_prop)).2 hgi
  have hprod := hf.integrable_mul hg
  refine ⟨hprod, ?_⟩
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hprod hfi hgi
  have hfbound : (∫ ω, f ω ^ 2 ∂μ) ≤
      B * gaussianRadialMoment r (2 * p - 2) / gaussianEvenMoment (2 * p - 2) := by
    apply (le_div_iff₀ (gaussianEvenMoment_pos _)).2
    simpa only [f, ← pow_mul, show (p - 1) * 2 = 2 * p - 2 by omega, mul_comm]
      using hrad.2
  have hgbound : (∫ ω, g ω ^ 2 ∂μ) ≤ A * (x ⬝ᵥ x) ^ 2 := by
    simpa only [g, ← pow_mul] using (hfour x).2
  apply hcs.trans
  rw [mul_comm]
  exact mul_le_mul hgbound hfbound (integral_nonneg fun _ => sq_nonneg _) (by positivity)

/-- The square-root form of the direction-preserving raw matrix moment bound.
Source: Cauchy--Schwarz and Gaussian radialization.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_rankOneProbe_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {r p : ℕ} (hr : 1 ≤ r) (hp : 2 ≤ p) (y : Ω → Fin r → ℝ)
    (hy : Measurable y) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfour : ∀ a : Fin r → ℝ,
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ 4) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ 4 ∂μ) ≤ A * (a ⬝ᵥ a) ^ 2)
    (hhigh : ∀ a : Fin r → ℝ,
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ (2 * (2 * p - 2))) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ (2 * (2 * p - 2)) ∂μ) ≤
          B * (a ⬝ᵥ a) ^ (2 * p - 2))
    (x : Fin r → ℝ) :
    Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2) μ ∧
      (∫ ω, (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤
        Real.sqrt (A * (B * gaussianRadialMoment r (2 * p - 2) /
          gaussianEvenMoment (2 * p - 2))) * (x ⬝ᵥ x) := by
  have h := integrable_and_sq_integral_rankOneProbe_le hr hp y hy hA hB hfour hhigh x
  refine ⟨h.1, ?_⟩
  have hD : 0 ≤ gaussianRadialMoment r (2 * p - 2) := by
    unfold gaussianRadialMoment
    exact Finset.prod_nonneg fun _ _ => by positivity
  have hC : 0 ≤ A * (B * gaussianRadialMoment r (2 * p - 2) /
      gaussianEvenMoment (2 * p - 2)) := by
    have hg := gaussianEvenMoment_pos (2 * p - 2)
    positivity
  have hx : 0 ≤ x ⬝ᵥ x := dotProduct_self_nonneg x
  apply (sq_le_sq₀
    (integral_nonneg fun ω => mul_nonneg
      (pow_nonneg (dotProduct_self_nonneg (y ω)) _) (sq_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) hx)).1
  rw [mul_pow, Real.sq_sqrt hC]
  nlinarith [h.2]

/-- The Gaussian divisor saves one factorial order in a radial covariance budget.
Source: Gaussian averaging and the central binomial estimate.
Atlas: `khatri-rao-sharp-growth`. -/
theorem factorial_mul_gaussianRadialMoment_div_gaussianEvenMoment_le_sq
    {r k d : ℕ} (hd : 1 ≤ d) :
    (4 : ℝ) ^ d * (2 * ((2 * k).factorial : ℝ)) ^ d * gaussianRadialMoment r (2 * k) /
        gaussianEvenMoment (2 * k) ≤
      (4 ^ d * 2 ^ (k * (d - 1)) * (k.factorial : ℝ) ^ (d - 1) *
        ((r : ℝ) + 4 * (k + 1)) ^ k) ^ 2 := by
  let F : ℝ := ((2 * k).factorial : ℝ)
  let G : ℝ := (k.factorial : ℝ)
  let S : ℝ := (r : ℝ) + 4 * (k + 1)
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hdup : F ≤ 4 ^ k * G ^ 2 := by
    dsimp [F, G]
    exact_mod_cast factorial_two_mul_le_four_pow_mul_factorial_sq k
  have hgauss := factorial_le_gaussianEvenMoment (2 * k)
  have hrad : gaussianRadialMoment r (2 * k) ≤ S ^ (2 * k) := by
    apply (gaussianRadialMoment_le_pow r (2 * k)).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [S]
    push_cast
    linarith
  have hfirst : (4 : ℝ) ^ d * (2 * F) ^ d / gaussianEvenMoment (2 * k) ≤
      (8 : ℝ) ^ d * F ^ (d - 1) := by
    apply (div_le_iff₀ (gaussianEvenMoment_pos _)).2
    calc
      (4 : ℝ) ^ d * (2 * F) ^ d = (8 : ℝ) ^ d * F ^ (d - 1) * F := by
        rw [mul_pow, ← mul_assoc, ← mul_pow]
        norm_num only [show (4 : ℝ) * 2 = 8 by norm_num]
        rw [mul_assoc, ← pow_succ, show d - 1 + 1 = d by omega]
      _ ≤ (8 : ℝ) ^ d * F ^ (d - 1) * gaussianEvenMoment (2 * k) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
  have hpow : (8 : ℝ) ^ d * F ^ (d - 1) ≤
      ((4 : ℝ) ^ d) ^ 2 * (4 ^ k * G ^ 2) ^ (d - 1) := by
    apply mul_le_mul
    · rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
    · exact pow_le_pow_left₀ hF.le hdup _
    · positivity
    · positivity
  calc
    (4 : ℝ) ^ d * (2 * ((2 * k).factorial : ℝ)) ^ d * gaussianRadialMoment r (2 * k) /
        gaussianEvenMoment (2 * k) =
      ((4 : ℝ) ^ d * (2 * F) ^ d / gaussianEvenMoment (2 * k)) *
        gaussianRadialMoment r (2 * k) := by ring
    _ ≤ ((4 : ℝ) ^ d) ^ 2 * (4 ^ k * G ^ 2) ^ (d - 1) * S ^ (2 * k) := by
      apply mul_le_mul (hfirst.trans hpow) hrad
      · unfold gaussianRadialMoment
        exact Finset.prod_nonneg fun _ _ => by positivity
      · positivity
    _ = _ := by
      change _ = ((4 : ℝ) ^ d * 2 ^ (k * (d - 1)) * G ^ (d - 1) * S ^ k) ^ 2
      have h4 : ((4 : ℝ) ^ k) ^ (d - 1) = (2 ^ (k * (d - 1)) : ℝ) ^ 2 := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        ring
      have hGpow : (G ^ 2) ^ (d - 1) = (G ^ (d - 1)) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      have hSpow : S ^ (2 * k) = (S ^ k) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [mul_pow, h4, hGpow, hSpow]
      ring

/-- An explicit variance scale for tensor directional sub-Gaussian moments.
Source: the coarsened Gaussian averaging factorial envelope.
Atlas: `khatri-rao-sharp-growth`. -/
def khatriRaoVarianceBudget (d : ℕ) (K : ℝ) (r : ℕ) : ℝ :=
  2 ^ (3 * d + 4) * K ^ (4 * d) * r

/-- An explicit raw covariance moment radius at natural order `p`.
Source: the coarsened Gaussian averaging factorial envelope.
Atlas: `khatri-rao-sharp-growth`. -/
def khatriRaoMomentRadius (d : ℕ) (K : ℝ) (r p : ℕ) : ℝ :=
  2 ^ (d - 1) * K ^ (2 * d) * (p : ℝ) ^ (d - 2) * ((r : ℝ) + 4 * p)

/-- The explicit raw covariance radius increases with the moment order.
Source: monotonicity of nonnegative natural powers.
Atlas: `khatri-rao-sharp-growth`. -/
theorem khatriRaoMomentRadius_mono {d r : ℕ} {K : ℝ} (hK : 0 ≤ K) :
    Monotone (khatriRaoMomentRadius d K r) := by
  intro a b hab
  unfold khatriRaoMomentRadius
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  gcongr

/-- The explicit raw covariance variance is positive in positive rank and scale.
Source: the explicit factorial envelope.
Atlas: `khatri-rao-sharp-growth`. -/
theorem khatriRaoVarianceBudget_pos {d r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 < K) :
    0 < khatriRaoVarianceBudget d K r := by
  unfold khatriRaoVarianceBudget
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  positivity

/-- Capping the scale below by one makes the raw variance at least two.
Source: the explicit factorial envelope.
Atlas: `khatri-rao-sharp-growth`. -/
theorem two_le_khatriRaoVarianceBudget {d r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 1 ≤ K) :
    2 ≤ khatriRaoVarianceBudget d K r := by
  unfold khatriRaoVarianceBudget
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkp : 1 ≤ K ^ (4 * d) := one_le_pow₀ hK
  have htwo : (2 : ℝ) ≤ 2 ^ (3 * d + 4) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ 3 * d + 4 by omega)
  calc
    (2 : ℝ) ≤ 2 ^ (3 * d + 4) := htwo
    _ ≤ 2 ^ (3 * d + 4) * K ^ (4 * d) := le_mul_of_one_le_right (by positivity) hkp
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hrR

/-- Positive rank and a capped sub-Gaussian scale give a radius of at least one.
Source: the explicit factorial envelope.
Atlas: `khatri-rao-sharp-growth`. -/
theorem one_le_khatriRaoMomentRadius {d r p : ℕ} {K : ℝ}
    (hp : 1 ≤ p) (hK : 1 ≤ K) : 1 ≤ khatriRaoMomentRadius d K r p := by
  unfold khatriRaoMomentRadius
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : (1 : ℝ) ≤ 2 ^ (d - 1) := one_le_pow₀ (by norm_num)
  have hkp : 1 ≤ K ^ (2 * d) := one_le_pow₀ hK
  have hpp : 1 ≤ (p : ℝ) ^ (d - 2) := one_le_pow₀ hpR
  have hlast : (1 : ℝ) ≤ r + 4 * p := by
    have hr0 : (0 : ℝ) ≤ r := by positivity
    linarith
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le htwo hkp) hpp) hlast

/-- Directional product-factor moment budgets imply a raw factorial covariance
budget retaining each test direction. This is the finite-moment input needed
for the sharp Khatri--Rao rank logarithm.
Source: Heidary, Appendix `appendix:factorial`; all numerical constants here
are explicit and coarser than the optimized manuscript constants.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_rankOneProbe_le_factorial
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {r p d : ℕ} (hr : 1 ≤ r) (hp : 2 ≤ p) (hd : 2 ≤ d)
    (y : Ω → Fin r → ℝ) (hy : Measurable y) {K : ℝ} (hK : 0 ≤ K)
    (hdir : ∀ n : ℕ, 1 ≤ n → ∀ a : Fin r → ℝ,
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ (2 * n)) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ (2 * n) ∂μ) ≤
          (2 * (n.factorial : ℝ) * K ^ (2 * n)) ^ d * (a ⬝ᵥ a) ^ n)
    (x : Fin r → ℝ) :
    Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2) μ ∧
      (∫ ω, (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤
        ((p.factorial : ℝ) / 2) * khatriRaoVarianceBudget d K r *
          khatriRaoMomentRadius d K r p ^ (p - 2) * (x ⬝ᵥ x) := by
  let L := 2 * p - 2
  let P : ℝ := 4 ^ d * 2 ^ ((p - 1) * (d - 1)) *
    ((p - 1).factorial : ℝ) ^ (d - 1) * ((r : ℝ) + 4 * p) ^ (p - 1)
  have hLp : L + 2 = 2 * p := by dsimp [L]; omega
  have hfour (a : Fin r → ℝ) := hdir 2 (by omega) a
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at hfour
  have h := integrable_and_sq_integral_rankOneProbe_le hr hp y hy
    (show 0 ≤ (4 * K ^ 4) ^ d by positivity)
    (show 0 ≤ (2 * (L.factorial : ℝ) * K ^ (2 * L)) ^ d by positivity)
    hfour (hdir L (by dsimp [L]; omega)) x
  have hco : (4 : ℝ) ^ d * (2 * (L.factorial : ℝ)) ^ d *
      gaussianRadialMoment r L / gaussianEvenMoment L ≤ P ^ 2 := by
    have h0 := factorial_mul_gaussianRadialMoment_div_gaussianEvenMoment_le_sq
      (r := r) (k := p - 1) (d := d) (by omega)
    have hpcast : ((p - 1 : ℕ) : ℝ) + 1 = p := by exact_mod_cast (show p - 1 + 1 = p by omega)
    simpa only [P, show 2 * (p - 1) = L by omega,
      hpcast] using h0
  have hKP : K ^ (4 * d) * K ^ ((2 * L) * d) = (K ^ (2 * d * p)) ^ 2 := by
    rw [← pow_add, ← pow_mul]
    congr 1
    nlinarith
  have he :
      ((4 * K ^ 4) ^ d * (x ⬝ᵥ x) ^ 2) *
          ((2 * (L.factorial : ℝ) * K ^ (2 * L)) ^ d *
            gaussianRadialMoment r L / gaussianEvenMoment L) =
        (K ^ (2 * d * p)) ^ 2 * (x ⬝ᵥ x) ^ 2 *
          ((4 : ℝ) ^ d * (2 * (L.factorial : ℝ)) ^ d *
            gaussianRadialMoment r L / gaussianEvenMoment L) := by
    simp only [mul_pow, ← pow_mul]
    have heK : 4 * d + 2 * L * d = 2 * d * p * 2 := by nlinarith
    rw [show K ^ (2 * d * p * 2) = K ^ (4 * d) * K ^ (2 * L * d) by
      rw [← pow_add, heK]]
    ring
  have hraw : (∫ ω, (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤
      K ^ (2 * d * p) * P * (x ⬝ᵥ x) := by
    have hx := dotProduct_self_nonneg x
    apply (sq_le_sq₀
      (integral_nonneg fun ω => mul_nonneg
        (pow_nonneg (dotProduct_self_nonneg (y ω)) _) (sq_nonneg _))
      (by dsimp [P]; positivity)).1
    calc
      (∫ ω, (y ω ⬝ᵥ y ω) ^ (p - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ^ 2 ≤ _ := h.2
      _ = _ := he
      _ ≤ (K ^ (2 * d * p)) ^ 2 * (x ⬝ᵥ x) ^ 2 * P ^ 2 :=
        mul_le_mul_of_nonneg_left hco (by positivity)
      _ = _ := by ring
  have hN : 2 * P ≤ (p.factorial : ℝ) * 2 ^ (3 * d + 4) * r *
      ((2 : ℝ) ^ (d - 1) * (p : ℝ) ^ (d - 2) * ((r : ℝ) + 4 * p)) ^ (p - 2) := by
    dsimp [P]
    have h0 :
        2 * (4 : ℝ) ^ d * 2 ^ ((p - 1) * (d - 1)) *
          ((p - 1).factorial : ℝ) ^ (d - 1) * ((r : ℝ) + 4 * p) ^ (p - 1) ≤
        (p.factorial : ℝ) * 2 ^ (3 * d + 4) * r *
          ((2 : ℝ) ^ (d - 1) * (p : ℝ) ^ (d - 2) * ((r : ℝ) + 4 * p)) ^ (p - 2) := by
      exact_mod_cast factorial_radial_coefficient_le hr hp hd
    simpa only [mul_assoc] using h0
  have hKsplit : K ^ (2 * d * p) = K ^ (4 * d) * (K ^ (2 * d)) ^ (p - 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    have hp' : p - 2 + 2 = p := by omega
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hN (pow_nonneg hK (2 * d * p))
  have hfinal : K ^ (2 * d * p) * P ≤
      ((p.factorial : ℝ) / 2) * khatriRaoVarianceBudget d K r *
        khatriRaoMomentRadius d K r p ^ (p - 2) := by
    have heq : K ^ (2 * d * p) * ((p.factorial : ℝ) * 2 ^ (3 * d + 4) * r *
        ((2 : ℝ) ^ (d - 1) * (p : ℝ) ^ (d - 2) * ((r : ℝ) + 4 * p)) ^ (p - 2)) =
      2 * (((p.factorial : ℝ) / 2) * khatriRaoVarianceBudget d K r *
        khatriRaoMomentRadius d K r p ^ (p - 2)) := by
      rw [hKsplit]
      simp only [khatriRaoVarianceBudget, khatriRaoMomentRadius, mul_pow]
      ring
    rw [heq] at hscale
    nlinarith
  exact ⟨h.1, hraw.trans (mul_le_mul_of_nonneg_right hfinal (dotProduct_self_nonneg x))⟩

end NLAlib
