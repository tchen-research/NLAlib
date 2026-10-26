import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricSum
import NLAlib.RandomMatrix.Gaussian.Spectral.Deviation
import NLAlib.ForMathlib.Probability.ExponentialTailMoments

/-!
# Norm moments of the unnormalized symmetric Gaussian ensemble

The actual law `G ↦ G + Gᴴ`, with `G` a real iid standard Gaussian matrix,
has even norm moments bounded by a universal constant times
`sqrt r + sqrt p`. Integrability and the moment bound follow from the proved
Gaussian spectral-norm tail, the deterministic transpose triangle inequality,
and shifted-exponential tail integration. No moment or concentration estimate
is assumed as a hypothesis.

Source: the Gaussian singular-value deviation bound of Davidson--Szarek
(2001), Theorem II.13, and elementary tail integration.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

/-- Symmetrizing a real matrix increases its spectral norm by at most a
factor of two. -/
theorem specNorm_gaussianSymmetricSum_le_two_mul {n : Type*}
    [Fintype n] [DecidableEq n] (G : Matrix n n ℝ) :
    specNorm (gaussianSymmetricSum G) ≤ 2 * specNorm G := by
  calc
    specNorm (gaussianSymmetricSum G) ≤ specNorm G + specNorm Gᴴ := specNorm_add_le _ _
    _ = 2 * specNorm G := by rw [specNorm_conjTranspose]; ring

/-- The squared norm of the actual symmetric Gaussian sum has a shifted
unit-exponential tail, with explicit dimension and scale constants. -/
theorem measure_sq_specNorm_gaussianSymmetricSum_le (r : ℕ) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix (Fin r) (Fin r)).real
      {G | 32 * (r : ℝ) + 16 * t < specNorm (gaussianSymmetricSum G) ^ 2} ≤
      Real.exp (-t) := by
  have htail := measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix
    (N := r) (n := r) (Real.sqrt (2 * t)) (Real.sqrt_nonneg _)
  have hrt : (Real.sqrt (2 * t)) ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
  have hrr : (Real.sqrt (r : ℝ)) ^ 2 = r := Real.sq_sqrt (Nat.cast_nonneg _)
  have hexp : -(Real.sqrt (2 * t)) ^ 2 / 2 = -t := by rw [hrt]; ring
  rw [hexp] at htail
  apply le_trans (measureReal_mono ?_) htail
  intro G hG
  simp only [Set.mem_ofPred_eq] at hG ⊢
  have hsym := specNorm_gaussianSymmetricSum_le_two_mul G
  have hgnn := specNorm_nonneg G
  have hsnn := specNorm_nonneg (gaussianSymmetricSum G)
  have hnormsq : specNorm (gaussianSymmetricSum G) ^ 2 ≤ 4 * specNorm G ^ 2 := by
    nlinarith
  have hthreshold :
      (Real.sqrt (r : ℝ) + Real.sqrt (r : ℝ) + Real.sqrt (2 * t)) ^ 2 ≤
        8 * (r : ℝ) + 4 * t := by
    nlinarith [sq_nonneg (2 * Real.sqrt (r : ℝ) - Real.sqrt (2 * t))]
  by_contra hbad
  have hlt : specNorm G < Real.sqrt (r : ℝ) + Real.sqrt (r : ℝ) + Real.sqrt (2 * t) :=
    lt_of_not_ge hbad
  have hpow := pow_le_pow_left₀ hgnn hlt.le 2
  nlinarith

private theorem measurable_sq_specNorm_gaussianSymmetricSum (r : ℕ) :
    Measurable (fun G : Matrix (Fin r) (Fin r) ℝ =>
      specNorm (gaussianSymmetricSum G) ^ 2) := by
  have hc : Continuous (specNorm : Matrix (Fin r) (Fin r) ℝ → ℝ) :=
    continuous_of_abs_sub_le_mul_frobNorm specNorm 1 fun X Y => by
      simpa only [one_mul] using abs_specNorm_sub_specNorm_le_frobNorm X Y
  exact ((hc.comp continuous_gaussianSymmetricSum).pow 2).measurable

/-- The squared symmetric Gaussian norm belongs to every positive integer
`L^p`, with its actual norm bounded by `32 r + 16 p`. -/
theorem memLp_and_lpNorm_sq_specNorm_gaussianSymmetricSum_le
    (r p : ℕ) (hp : 0 < p) :
    MemLp (fun G : Matrix (Fin r) (Fin r) ℝ => specNorm (gaussianSymmetricSum G) ^ 2)
      (p : ℝ≥0∞) (gaussianMatrix (Fin r) (Fin r)) ∧
    lpNorm (fun G : Matrix (Fin r) (Fin r) ℝ => specNorm (gaussianSymmetricSum G) ^ 2)
      (p : ℝ≥0∞) (gaussianMatrix (Fin r) (Fin r)) ≤ 32 * (r : ℝ) + 16 * p := by
  exact memLp_and_lpNorm_le_of_shifted_exponential_tail
    (gaussianMatrix (Fin r) (Fin r))
    (fun G => specNorm (gaussianSymmetricSum G) ^ 2)
    (measurable_sq_specNorm_gaussianSymmetricSum r).aemeasurable
    (fun G => sq_nonneg _) (by positivity) (by norm_num : (0 : ℝ) < 16)
    (fun t ht => measure_sq_specNorm_gaussianSymmetricSum_le r t ht) p hp

/-- Every even spectral-norm moment of the symmetric Gaussian sum is
integrable under the actual iid Gaussian matrix law. -/
theorem integrable_specNorm_gaussianSymmetricSum_pow_two_mul (r p : ℕ) :
    Integrable (fun G : Matrix (Fin r) (Fin r) ℝ =>
      specNorm (gaussianSymmetricSum G) ^ (2 * p)) (gaussianMatrix (Fin r) (Fin r)) := by
  by_cases hp : p = 0
  · simp only [hp, mul_zero, pow_zero]
    exact integrable_const 1
  have hmem := (memLp_and_lpNorm_sq_specNorm_gaussianSymmetricSum_le r p
    (Nat.pos_of_ne_zero hp)).1
  have hi := (integrable_norm_rpow_iff hmem.aestronglyMeasurable
    (by exact_mod_cast hp : (p : ℝ≥0∞) ≠ 0) (by simp : (p : ℝ≥0∞) ≠ ∞)).2 hmem
  simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_pow, sq_abs,
    Real.rpow_natCast, ← pow_mul] using hi

/-- Rooted even moments of the symmetric Gaussian sum satisfy the universal
bound `8 (sqrt r + sqrt p)`. The law and integrability are proved, rather
than provided as moment hypotheses. The dimension may be zero.
Source: Davidson--Szarek (2001), Theorem II.13, followed by tail integration. -/
theorem integral_specNorm_gaussianSymmetricSum_pow_two_mul_root_le
    (r p : ℕ) (hp : 0 < p) :
    (∫ G : Matrix (Fin r) (Fin r) ℝ,
      specNorm (gaussianSymmetricSum G) ^ (2 * p) ∂gaussianMatrix (Fin r) (Fin r)) ^
        (((2 * p : ℕ) : ℝ)⁻¹) ≤ 8 * (Real.sqrt r + Real.sqrt p) := by
  obtain ⟨hmem, hbound⟩ := memLp_and_lpNorm_sq_specNorm_gaussianSymmetricSum_le r p hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 (by simp) hmem.aestronglyMeasurable] at hbound
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_pow, sq_abs,
    Real.rpow_natCast, ← pow_mul] at hbound
  let M : ℝ := ∫ G : Matrix (Fin r) (Fin r) ℝ,
    specNorm (gaussianSymmetricSum G) ^ (2 * p) ∂gaussianMatrix (Fin r) (Fin r)
  have hM : 0 ≤ M := integral_nonneg fun G => pow_nonneg (specNorm_nonneg _) _
  have hroot : M ^ (((2 * p : ℕ) : ℝ)⁻¹) = Real.sqrt (M ^ ((p : ℝ)⁻¹)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM]
    congr 1
    push_cast
    field_simp
  change M ^ (((2 * p : ℕ) : ℝ)⁻¹) ≤ _
  rw [hroot]
  calc
    Real.sqrt (M ^ ((p : ℝ)⁻¹)) ≤ Real.sqrt (32 * (r : ℝ) + 16 * p) :=
      Real.sqrt_le_sqrt hbound
    _ ≤ 8 * (Real.sqrt r + Real.sqrt p) := by
      rw [Real.sqrt_le_left (by positivity)]
      have hr := Real.sq_sqrt (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      have hp' := Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
      nlinarith [mul_nonneg (Real.sqrt_nonneg (r : ℝ)) (Real.sqrt_nonneg (p : ℝ))]

/-- The even spectral-norm moments of the actual symmetric Gaussian sum are
bounded by the corresponding powers of `8 (sqrt r + sqrt p)`. This includes
the zeroth moment and the zero-dimensional ensemble. -/
theorem integral_specNorm_gaussianSymmetricSum_pow_two_mul_le (r p : ℕ) :
    (∫ G : Matrix (Fin r) (Fin r) ℝ,
      specNorm (gaussianSymmetricSum G) ^ (2 * p) ∂gaussianMatrix (Fin r) (Fin r)) ≤
      (8 * (Real.sqrt r + Real.sqrt p)) ^ (2 * p) := by
  by_cases hp : p = 0
  · subst p
    simp
  have hroot := integral_specNorm_gaussianSymmetricSum_pow_two_mul_root_le r p
    (Nat.pos_of_ne_zero hp)
  have hM : 0 ≤ ∫ G : Matrix (Fin r) (Fin r) ℝ,
      specNorm (gaussianSymmetricSum G) ^ (2 * p) ∂gaussianMatrix (Fin r) (Fin r) :=
    integral_nonneg fun G => pow_nonneg (specNorm_nonneg _) _
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hM _) hroot
    (Nat.cast_nonneg (2 * p))
  rw [Real.rpow_inv_rpow hM (by exact_mod_cast (by omega : 2 * p ≠ 0))] at hpow
  simpa only [Real.rpow_natCast] using hpow

end NLAlib
