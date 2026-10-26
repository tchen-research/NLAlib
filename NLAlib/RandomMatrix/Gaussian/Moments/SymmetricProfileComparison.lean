import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricSumPairings
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricSumNormMoments
import NLAlib.Matrix.Norms.TraceSpectral
import NLAlib.Matrix.Norms.SchattenEvenMoments

/-!
# Profile-sensitive Gaussian even-moment comparison

The weighted connected-graph inequality compares the actual symmetric
Gaussian profile ensemble with a smaller homogeneous Gaussian ensemble.
The hypotheses are deterministic power sums of the variance profile; the
conclusion concerns the actual Gaussian trace moment. No probabilistic
moment estimate is supplied as a hypothesis.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 2.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Normalized profile power sums imply an actual even Gaussian trace
comparison. The homogeneous comparator is the explicit ensemble `G + Gᴴ`.
Its dimension depends on the profile power sums, and is independent of the
moment order when those normalized profile bounds hold. -/
theorem integral_trace_symmetricGaussianMatrix_pow_two_mul_le_comparator
    (b : Matrix n n ℝ) (hb : b.IsSymm) (p r : ℕ) (hp : 0 < p) (hr : 0 < r)
    (s : n → ℝ) (hcap : ∀ i j, b i j ^ 2 ≤ s i)
    (hd : (∑ i, (∑ j, b i j ^ 2) ^ p) ≤ (r : ℝ) ^ p)
    (hs : (∑ i, s i ^ p) ≤ 1) :
    (∫ G, ((symmetricGaussianMatrix b G) ^ (2 * p)).trace ∂gaussianMatrix n n) ≤
      (r : ℝ)⁻¹ *
        ∫ G, ((gaussianSymmetricSum G) ^ (2 * p)).trace
          ∂gaussianMatrix (Fin r) (Fin r) := by
  classical
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2 * p ≠ 0)
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hdiag (π : GaussianPairings (k + 1))
      (flip : Fin (gaussianPairingEdges π).length → Bool) :
      (∑ x : Fin (k + 1) → n, symmetricCycleDiagramWeight b π flip x) ≤
        (r : ℝ)⁻¹ *
          ∑ x : Fin (k + 1) → Fin r,
            symmetricCycleDiagramWeight (Matrix.of fun _ _ => (1 : ℝ)) π flip x := by
    have hlen : (gaussianPairingEdges π).length = p := by
      have hlen := two_mul_gaussianPairingEdges_length π
      omega
    have h := sum_symmetricCycleDiagramWeight_le_of_power_sums b hb π flip
      s hcap r 1 hr' zero_lt_one (by simpa only [hlen] using hd)
      (by simpa only [hlen, one_pow] using hs)
    rw [one_pow, mul_one] at h
    apply h.trans_eq
    rw [sum_symmetricCycleDiagramWeight_one]
    let Q := symmetricCycleVertexQuotient π flip
    let : Nonempty Q := ⟨Quotient.mk'' (0 : Fin (k + 1))⟩
    have hv : 1 ≤ Nat.card Q := Nat.card_pos
    change (r : ℝ) ^ (Nat.card Q - 1) = (r : ℝ)⁻¹ * (r : ℝ) ^ Nat.card Q
    have hpow : (r : ℝ) ^ Nat.card Q = (r : ℝ) ^ (Nat.card Q - 1) * r := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    field_simp
  have hsum :
      (∑ π : GaussianPairings (k + 1),
        ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
          ∑ x : Fin (k + 1) → n, symmetricCycleDiagramWeight b π flip x) ≤
      (r : ℝ)⁻¹ *
        ∑ π : GaussianPairings (k + 1),
          ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
            ∑ x : Fin (k + 1) → Fin r,
              symmetricCycleDiagramWeight (Matrix.of fun _ _ => (1 : ℝ)) π flip x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro π _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun flip _ => hdiag π flip
  have h := (integral_trace_symmetricGaussianMatrix_pow_le_sum_diagrams b hb k).trans
    (hsum.trans (mul_le_mul_of_nonneg_left
      (sum_symmetricCycleDiagramWeight_one_le_integral_trace_gaussianSymmetricSum_pow r k)
      (inv_nonneg.mpr hr'.le)))
  have hk' : k + 1 = 2 * p := by omega
  simpa only [hk'] using h

open scoped Matrix.Norms.L2Operator in
/-- The actual homogeneous Gaussian trace moment is bounded by its
dimension times the universal even norm-moment bound. -/
theorem integral_trace_gaussianSymmetricSum_pow_two_mul_le
    (r p : ℕ) (hr : 0 < r) (hp : 0 < p) :
    (∫ G, ((gaussianSymmetricSum G) ^ (2 * p)).trace
      ∂gaussianMatrix (Fin r) (Fin r)) ≤
        (r : ℝ) * (8 * (Real.sqrt r + Real.sqrt p)) ^ (2 * p) := by
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2 * p ≠ 0)
  have hk' : k + 1 = 2 * p := by omega
  have hi := integrable_trace_gaussianSymmetricSum_pow r k
  rw [hk'] at hi
  have hbound (G : Matrix (Fin r) (Fin r) ℝ) :
      ((gaussianSymmetricSum G) ^ (2 * p)).trace ≤
        (r : ℝ) * specNorm (gaussianSymmetricSum G) ^ (2 * p) := by
    have hpow : specNorm ((gaussianSymmetricSum G) ^ (2 * p)) ≤
        specNorm (gaussianSymmetricSum G) ^ (2 * p) := by
      simpa only [specNorm_eq_norm] using norm_pow_le (gaussianSymmetricSum G) (2 * p)
    calc
      _ ≤ ‖((gaussianSymmetricSum G) ^ (2 * p)).trace‖ := le_abs_self _
      _ ≤ (r : ℝ) * specNorm ((gaussianSymmetricSum G) ^ (2 * p)) := by
        simpa only [Fintype.card_fin] using
          norm_trace_le_card_mul_specNorm ((gaussianSymmetricSum G) ^ (2 * p))
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  calc
    _ ≤ ∫ G : Matrix (Fin r) (Fin r) ℝ,
        (r : ℝ) * specNorm (gaussianSymmetricSum G) ^ (2 * p)
          ∂gaussianMatrix (Fin r) (Fin r) :=
      integral_mono hi ((integrable_specNorm_gaussianSymmetricSum_pow_two_mul r p).const_mul r) hbound
    _ = (r : ℝ) * ∫ G : Matrix (Fin r) (Fin r) ℝ,
        specNorm (gaussianSymmetricSum G) ^ (2 * p)
          ∂gaussianMatrix (Fin r) (Fin r) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_specNorm_gaussianSymmetricSum_pow_two_mul_le r p) (Nat.cast_nonneg _)

/-- With normalized deterministic profile power sums, the actual even
Schatten moment is bounded by `8 (sqrt r + sqrt p)`, raised to that moment
order. This is an unconditional Gaussian estimate, including zero profiles. -/
theorem integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_le_of_power_sums
    (b : Matrix n n ℝ) (hb : b.IsSymm) (p r : ℕ) (hp : 0 < p) (hr : 0 < r)
    (s : n → ℝ) (hcap : ∀ i j, b i j ^ 2 ≤ s i)
    (hd : (∑ i, (∑ j, b i j ^ 2) ^ p) ≤ (r : ℝ) ^ p)
    (hs : (∑ i, s i ^ p) ≤ 1) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix b G) (2 * p : ℕ) ^ (2 * p)
      ∂gaussianMatrix n n) ≤ (8 * (Real.sqrt r + Real.sqrt p)) ^ (2 * p) := by
  have htrace (G : Matrix n n ℝ) :
      schattenNormReal (symmetricGaussianMatrix b G) (2 * p : ℕ) ^ (2 * p) =
        ((symmetricGaussianMatrix b G) ^ (2 * p)).trace := by
    simpa only [RCLike.re_to_real] using
      schattenNormReal_pow_even_eq_re_trace (symmetricGaussianMatrix b G)
        (Matrix.isHermitian_iff_isSymm.mpr (symmetricGaussianMatrix_isSymm b G)) hp
  simp_rw [htrace]
  calc
    _ ≤ (r : ℝ)⁻¹ * ∫ G, ((gaussianSymmetricSum G) ^ (2 * p)).trace
        ∂gaussianMatrix (Fin r) (Fin r) :=
      integral_trace_symmetricGaussianMatrix_pow_two_mul_le_comparator b hb p r hp hr s hcap hd hs
    _ ≤ (r : ℝ)⁻¹ * ((r : ℝ) * (8 * (Real.sqrt r + Real.sqrt p)) ^ (2 * p)) :=
      mul_le_mul_of_nonneg_left (integral_trace_gaussianSymmetricSum_pow_two_mul_le r p hr hp)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), one_mul]

end NLAlib
