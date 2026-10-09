import NLAlib.Matrix.UnshiftedGramSoftMin
import NLAlib.Matrix.InversePowerGrowth
import NLAlib.Matrix.SpectralContinuity
import NLAlib.ForMathlib.Analysis.Calculus.CompactTestSupport

/-!
# Global calculus for cut off unshifted Gram vector fields

Smooth tests supported away from zero turn the unshifted resolvent gradient into
a globally differentiable field. At deficient matrices it vanishes on a whole
neighborhood; at positive definite Gram points its derivative is the usual operator
chain rule. Atlas: wishart-lambda-min-tail.
-/

noncomputable section

open Matrix Set Filter
open scoped Matrix Topology ContDiff Matrix.Norms.L2Operator

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
/-- A deficient real Gram matrix has zero smallest singular value.
Source: the positive smallest-singular-value inverse criterion;
atlas wishart-lambda-min-tail (cutoff helper). -/
theorem sigmaMin_transpose_eq_zero_of_not_posDef_gram (G : Matrix ι κ ℝ)
    (hnot : ¬(G * Gᵀ).PosDef) : sigmaMin Gᵀ = 0 := by
  have hh := sigmaMin_transpose_sq_eq_zero_of_not_posDef G hnot
  nlinarith

/-- A cut off unshifted coordinate gradient has its actual chain-rule derivative
on every matrix, including the rank-deficient domain. The singular case is proved
by local vanishing, not by differentiating the total inverse there.
Source: the user's unshifted cutoff operator route;
atlas wishart-lambda-min-tail (Stein calculus helper). -/
theorem hasDerivAt_test_mul_unshiftedGramGradient_single [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioi 0)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    HasDerivAt (fun t : ℝ =>
      ψ (inversePowerSoftMin n ((G + t • Matrix.single i j 1) *
        (G + t • Matrix.single i j 1)ᵀ)) *
      gramSoftMinGradient n 0 (G + t • Matrix.single i j 1) i j)
      (deriv ψ (inversePowerSoftMin n (G * Gᵀ)) * gramSoftMinGradient n 0 G i j ^ 2 +
        ψ (inversePowerSoftMin n (G * Gᵀ)) *
          gramSoftMinSecond n 0 G (Matrix.single i j 1)) 0 := by
  by_cases hpd : (G * Gᵀ).PosDef
  · have hF := hasDerivAt_gramSoftMin_unshifted_single_zero n hn G hpd i j
    have hD := hasDerivAt_gramSoftMinGradient_unshifted_single_zero n hn G hpd i j
    convert! (((hψ.differentiable (by simp)
      (inversePowerSoftMin n ((G + (0 : ℝ) • Matrix.single i j 1) *
        (G + (0 : ℝ) • Matrix.single i j 1)ᵀ))).hasDerivAt.comp 0 hF).mul hD) using 1
    simp only [Function.comp_def, zero_smul, add_zero]
    ring
  · obtain ⟨a, b, ha, hab, hbound, hdbound⟩ :=
      exists_pos_bounds_tsupport_and_deriv ψ hψc hψs
    have hX := sigmaMin_transpose_eq_zero_of_not_posDef_gram G hpd
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    have hcont : Continuous (fun t : ℝ => sigmaMin (G + t • E)ᵀ ^ 2) :=
      continuous_sigmaMin_transpose_sq_array.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    have hXlim : Tendsto (fun t : ℝ => sigmaMin (G + t • E)ᵀ ^ 2) (𝓝 0) (𝓝 (0 : ℝ)) := by
      have hh : ContinuousAt (fun t : ℝ => sigmaMin (G + t • E)ᵀ ^ 2) 0 := hcont.continuousAt
      simpa only [zero_smul, add_zero, hX, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hh.tendsto
    have hzero :
        (fun t : ℝ => ψ (inversePowerSoftMin n ((G + t • E) * (G + t • E)ᵀ)) *
          gramSoftMinGradient n 0 (G + t • E) i j) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [(tendsto_order.mp hXlim).2 a ha] with t ht
      have hlow : inversePowerSoftMin n ((G + t • E) * (G + t • E)ᵀ) < a :=
        (inversePowerSoftMin_gram_le_sigmaMin_sq n hn (G + t • E)).trans_lt ht
      have hψzero : ψ (inversePowerSoftMin n ((G + t • E) * (G + t • E)ᵀ)) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => not_le.mpr hlow (hbound h).1
      rw [hψzero, zero_mul]
    have hFzero := inversePowerSoftMin_gram_eq_zero_of_not_posDef n hn G hpd
    have hψzero : ψ 0 = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => lt_irrefl (0 : ℝ) (hψs h)
    have hψdzero : deriv ψ 0 = 0 :=
      deriv_of_notMem_tsupport fun h => lt_irrefl (0 : ℝ) (hψs h)
    rw [hFzero, hψzero, hψdzero, zero_mul, zero_mul, zero_add]
    exact (hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hzero

/-- On a positive spectral cutoff interval the inverse-power Hessian has a
uniform bound in the squared direction size, independent of any identity shift.
Source: inverse norm and soft-minimum coefficient bounds;
atlas wishart-lambda-min-tail (unshifted cutoff helper). -/
theorem abs_inversePowerSoftMinSecond_le_cutoff [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.IsHermitian)
    (a b : ℝ) (ha : 0 < a) (hlow : a ≤ inversePowerSoftMin n A)
    (hupp : inversePowerSoftMin n A ≤ b) :
    |inversePowerSoftMinSecond n A B| ≤
      b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobSq B := by
  have hb : 0 < b := ha.trans_le (hlow.trans hupp)
  have hc : Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) ≤ b ^ (n + 1) := by
    rw [inversePowerSoftMin_coefficient_eq_pow n hn A hA]
    exact pow_le_pow_left₀ (ha.le.trans hlow) hupp _
  have hinv : specNorm A⁻¹ ≤ a⁻¹ := by
    apply (specNorm_inv_le_inv_inversePowerSoftMin n hn A hA).trans
    simpa only [one_div] using one_div_le_one_div_of_le ha hlow
  have hpow := pow_le_pow_left₀ (specNorm_nonneg A⁻¹) hinv (n + 2)
  have hkernel :
      ((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B ≤
      ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobSq B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
      (frobSq_nonneg B)
  have hk0 : 0 ≤ ((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (specNorm_nonneg A⁻¹) _))
      (frobSq_nonneg B)
  calc
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        (((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobSq B) :=
      abs_inversePowerSoftMinSecond_le n A B hA hB
    _ ≤ b ^ (n + 1) * (((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobSq B) :=
      mul_le_mul hc hkernel hk0 (pow_nonneg hb.le _)
    _ = _ := by ring

/-- On an active positive cutoff, a second coordinate Gram derivative grows at
most linearly in Gaussian Frobenius size. Positive cutoff alone forces the Gram
matrix to be positive definite. Source: the unshifted operator cutoff argument;
atlas wishart-lambda-min-tail (Stein domination helper). -/
theorem abs_gramSoftMinSecond_unshifted_single_le_cutoff [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (i : ι) (j : κ)
    (a b : ℝ) (ha : 0 < a) (hlow : a ≤ inversePowerSoftMin n (G * Gᵀ))
    (hupp : inversePowerSoftMin n (G * Gᵀ) ≤ b) :
    |gramSoftMinSecond n 0 G (Matrix.single i j 1)| ≤
      2 + 4 * b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobSq G := by
  have hpd : (G * Gᵀ).PosDef := by
    by_contra hnot
    rw [inversePowerSoftMin_gram_eq_zero_of_not_posDef n hn G hnot] at hlow
    linarith
  have hb : 0 < b := ha.trans_le (hlow.trans hupp)
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  let A := G * Gᵀ
  let P := inversePowerSoftMinWeight n A
  have hP : P.PosSemidef := inversePowerSoftMinWeight_posSemidef n hpd.posSemidef
  have hPdiag (k : ι) : 0 ≤ P k k := hP.diag_nonneg
  have hPi : P i i ≤ 1 := by
    have hh : P i i ≤ Matrix.trace P := by
      simpa only [Matrix.trace, Matrix.diag] using
        Finset.single_le_sum (fun k _ => hPdiag k) (Finset.mem_univ i)
    exact hh.trans (trace_inversePowerSoftMinWeight_le_one n hn hpd)
  have hEE : E * Eᵀ = Matrix.single i i 1 := by
    simp only [E, Matrix.transpose_single, Matrix.single_mul_single_same, one_mul]
  have hfirst : inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ)) = 2 * P i i := by
    rw [inversePowerSoftMinFirst_eq_trace_weight_mul, hEE, mul_smul_comm,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_single]
    simp [P]
  have hfirstabs : |inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ))| ≤ 2 := by
    rw [hfirst, abs_of_nonneg (mul_nonneg (by norm_num) (hPdiag i))]
    linarith
  have hdir : (E * Gᵀ + G * Eᵀ).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp only [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    exact add_comm _ _
  have hsecond := abs_inversePowerSoftMinSecond_le_cutoff n hn A (E * Gᵀ + G * Eᵀ)
    hpd hdir a b ha hlow hupp
  have hB := frobSq_single_gram_direction_le G i j
  have hc0 : 0 ≤ b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) := by positivity
  simp only [gramSoftMinSecond, regularizedGram_zero]
  change |inversePowerSoftMinSecond n A (E * Gᵀ + G * Eᵀ) +
    inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ))| ≤ _
  calc
    _ ≤ |inversePowerSoftMinSecond n A (E * Gᵀ + G * Eᵀ)| +
        |inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᵀ))| := abs_add_le _ _
    _ ≤ b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) *
        frobSq (E * Gᵀ + G * Eᵀ) + 2 := add_le_add hsecond hfirstabs
    _ ≤ b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * (4 * frobSq G) + 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hB hc0) (le_refl _)
    _ = _ := by ring

/-- Every unshifted coordinate gradient square is bounded by four times input
Frobenius size, including singular matrices. Source: the global gradient energy
bound; atlas wishart-lambda-min-tail (Stein domination helper). -/
theorem sq_gramSoftMinGradient_unshifted_single_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    gramSoftMinGradient n 0 G i j ^ 2 ≤ 4 * frobSq G := by
  let D := gramSoftMinGradient n 0 G
  have hrow : D i j ^ 2 ≤ ∑ j', D i j' ^ 2 :=
    Finset.single_le_sum (fun j' _ => sq_nonneg (D i j')) (Finset.mem_univ j)
  have hall : (∑ j', D i j' ^ 2) ≤ ∑ i', ∑ j', D i' j' ^ 2 :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg (D i' j'))
      (Finset.mem_univ i)
  have hD : D i j ^ 2 ≤ frobSq D := by
    simpa only [frobSq, frobInner, ← pow_two] using hrow.trans hall
  exact hD.trans ((frobSq_gramSoftMinGradient_unshifted_le_of_pos n hn G).trans
    (mul_le_mul_of_nonneg_left
      ((inversePowerSoftMin_gram_le_sigmaMin_sq n hn G).trans (sigmaMin_transpose_sq_le_frobSq G))
      (by norm_num)))

end NLAlib
