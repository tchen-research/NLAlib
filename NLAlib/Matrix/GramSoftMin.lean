import NLAlib.Matrix.InversePowerConcavity
import NLAlib.Matrix.GramTrace
import NLAlib.Matrix.QuadraticProbe
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Regularized Gram resolvent derivatives

The resolvent approximation to the smallest eigenvalue of `GGᵀ + εI`
has coordinate second derivatives whose sum is at most twice the column
dimension. This supplies the global Laplacian bound for the operator
integration-by-parts argument.

Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A Gram matrix regularized by a scalar multiple of the identity.
Source: resolvent operator proof; atlas `wishart-lambda-min-tail` (helper). -/
def regularizedGram (ε : ℝ) (G : Matrix ι κ ℝ) : Matrix ι ι ℝ := G * Gᵀ + ε • 1

omit [DecidableEq κ] in
/-- Positive regularization makes every real Gram matrix positive definite.
Source: Gram positivity; atlas `wishart-lambda-min-tail` (helper). -/
theorem regularizedGram_posDef {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    (regularizedGram ε G).PosDef := by
  have hG : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose G
  exact Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hε)

omit [Fintype ι] [DecidableEq κ] in
/-- The exact quadratic expansion of the Gram curve in one matrix direction.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper). -/
theorem regularizedGram_add_smul (ε t : ℝ) (G E : Matrix ι κ ℝ) :
    regularizedGram ε (G + t • E) = regularizedGram ε G +
      t • (E * Gᵀ + G * Eᵀ) + t ^ 2 • (E * Eᵀ) := by
  simp only [regularizedGram, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, pow_two]
  module

omit [DecidableEq κ] in
/-- The first derivative of the regularized Gram curve.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper). -/
theorem hasDerivAt_regularizedGram_add_smul (ε : ℝ) (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => regularizedGram ε (G + x • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) t := by
  have hlin := ((hasDerivAt_id t).smul_const (E * Gᵀ + G * Eᵀ)).const_add
    (regularizedGram ε G)
  have hquad := ((hasDerivAt_id t).pow 2).smul_const (E * Eᵀ)
  have h := hlin.add hquad
  simpa only [regularizedGram_add_smul, id_eq, Pi.add_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one, mul_one, one_smul, Nat.cast_ofNat] using! h

omit [DecidableEq κ] in
/-- The first Gram derivative has constant derivative `2EEᵀ`.
Source: Gram chain rule; atlas `wishart-lambda-min-tail` (helper). -/
theorem hasDerivAt_regularizedGram_first (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => E * Gᵀ + G * Eᵀ + (2 * x) • (E * Eᵀ))
      ((2 : ℝ) • (E * Eᵀ)) t := by
  simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul 2).smul_const (E * Eᵀ)
    |>.const_add (E * Gᵀ + G * Eᵀ)

/-- The explicit second derivative along one Gram direction after
composition with the resolvent approximation. Source: Gram chain rule;
atlas `wishart-lambda-min-tail` (helper). -/
def gramSoftMinSecond (n : ℕ) (ε : ℝ) (G E : Matrix ι κ ℝ) : ℝ :=
  inversePowerSoftMinSecond n (regularizedGram ε G) (E * Gᵀ + G * Eᵀ) +
    inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᵀ))

/-- The coordinate gradient of the resolvent regularized Gram functional.
Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper). -/
def gramSoftMinGradient (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  (2 : ℝ) • (inversePowerSoftMinWeight n (regularizedGram ε G) * G)

omit [DecidableEq κ] in
/-- The Euler gradient contraction is a trace pairing with the Gram
matrix. Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper). -/
theorem frobInner_gramSoftMinGradient_eq_trace (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) :
    frobInner G (gramSoftMinGradient n ε G) =
      2 * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G) * (G * Gᵀ)) := by
  rw [gramSoftMinGradient, frobInner_smul_right, frobInner_eq_trace]
  congr 1
  calc _ = Matrix.trace ((Gᵀ * inversePowerSoftMinWeight n (regularizedGram ε G)) * G) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (G * (Gᵀ * inversePowerSoftMinWeight n (regularizedGram ε G))) := by
          simpa only [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle Gᵀ (inversePowerSoftMinWeight n (regularizedGram ε G)) G)
    _ = Matrix.trace ((G * Gᵀ) * inversePowerSoftMinWeight n (regularizedGram ε G)) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

omit [DecidableEq κ] in
/-- The squared gradient is four times the quadratic gradient-weight
Gram trace. Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper). -/
theorem frobSq_gramSoftMinGradient_eq_trace (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    frobSq (gramSoftMinGradient n ε G) = 4 *
      Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G) ^ 2 * (G * Gᵀ)) := by
  have hP : (inversePowerSoftMinWeight n (regularizedGram ε G))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram ε G) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n hpd.posSemidef).isHermitian).eq
  rw [gramSoftMinGradient, frobSq_smul]
  norm_num only
  congr 1
  rw [frobSq, frobInner_eq_trace, Matrix.transpose_mul, hP, pow_two]
  calc _ = Matrix.trace (Gᵀ * (inversePowerSoftMinWeight n (regularizedGram ε G) *
        inversePowerSoftMinWeight n (regularizedGram ε G) * G)) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((inversePowerSoftMinWeight n (regularizedGram ε G) *
        inversePowerSoftMinWeight n (regularizedGram ε G) * G) * Gᵀ) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; simp only [Matrix.mul_assoc]

/-- The resolvent gradient weight has spectral norm at most one.
Source: positivity and its trace bound; atlas `wishart-lambda-min-tail` (helper). -/
theorem specNorm_inversePowerSoftMinWeight_le_one [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {A : Matrix ι ι ℝ} (hA : A.PosDef) : specNorm (inversePowerSoftMinWeight n A) ≤ 1 :=
  (specNorm_le_trace_of_posSemidef (inversePowerSoftMinWeight_posSemidef n hA.posSemidef)).trans
    (trace_inversePowerSoftMinWeight_le_one n hn hA)

omit [DecidableEq κ] in
/-- The resolvent Gram gradient is bounded in Frobenius norm uniformly
in both approximation parameters. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem frobNorm_gramSoftMinGradient_le [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    frobNorm (gramSoftMinGradient n ε G) ≤ 2 * frobNorm G := by
  have hP := specNorm_inversePowerSoftMinWeight_le_one n hn (regularizedGram_posDef hε G)
  rw [gramSoftMinGradient, frobNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc _ ≤ 2 * (specNorm (inversePowerSoftMinWeight n (regularizedGram ε G)) * frobNorm G) := by
        gcongr
        exact frobNorm_mul_le_specNorm_mul_frobNorm _ _
    _ ≤ 2 * frobNorm G := by nlinarith [frobNorm_nonneg G]

omit [DecidableEq κ] in
/-- The squared resolvent Gram gradient is bounded by four times the
Gram trace, uniformly in approximation parameters. Source: operator tail
proof; atlas `wishart-lambda-min-tail` (helper). -/
theorem frobSq_gramSoftMinGradient_le [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    frobSq (gramSoftMinGradient n ε G) ≤ 4 * frobSq G := by
  have h := pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_gramSoftMinGradient_le n hn hε G) 2
  simpa only [frobNorm_sq, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

omit [DecidableEq κ] in
/-- The Euler contraction of the resolvent Gram gradient is bounded by
twice the Gram trace. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (helper). -/
theorem abs_frobInner_gramSoftMinGradient_le [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    |frobInner G (gramSoftMinGradient n ε G)| ≤ 2 * frobSq G := by
  calc _ ≤ frobNorm G * frobNorm (gramSoftMinGradient n ε G) := abs_frobInner_le_frobNorm_mul_frobNorm _ _
    _ ≤ frobNorm G * (2 * frobNorm G) := by
        exact mul_le_mul_of_nonneg_left (frobNorm_gramSoftMinGradient_le n hn hε G)
          (frobNorm_nonneg G)
    _ = 2 * frobSq G := by rw [← frobNorm_sq]; ring

omit [DecidableEq κ] in
/-- The resolvent regularized Gram curve has the first derivative given
by the Gram chain rule at every point. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem hasDerivAt_gramSoftMin [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => inversePowerSoftMin n (regularizedGram ε (G + x • E)))
      (inversePowerSoftMinFirst n (regularizedGram ε (G + t • E))
        (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ))) t := by
  have hpd := regularizedGram_posDef hε (G + t • E)
  exact hasDerivAt_inversePowerSoftMin_curve n hn
    (hasDerivAt_regularizedGram_add_smul ε G E t) hpd.isUnit
    (trace_pow_pos_of_posDef hpd.inv n)

/-- The first Gram chain coefficient along a coordinate line equals the
corresponding actual gradient entry at every point. Source: operator tail
proof; atlas `wishart-lambda-min-tail` (helper). -/
theorem inversePowerSoftMinFirst_gram_single_eq_gradient (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (G : Matrix ι κ ℝ) (i : ι) (j : κ) (t : ℝ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    inversePowerSoftMinFirst n (regularizedGram ε (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = gramSoftMinGradient n ε (G + t • E) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hD : E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ) =
      E * (G + t • E)ᵀ + (G + t • E) * Eᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  have hP : (inversePowerSoftMinWeight n (regularizedGram ε (G + t • E)))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram ε (G + t • E)) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n
      (regularizedGram_posDef hε (G + t • E)).posSemidef).isHermitian).eq
  change inversePowerSoftMinFirst n (regularizedGram ε (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)) = _
  rw [hD, inversePowerSoftMinFirst_eq_trace_weight_mul, trace_mul_gram_direction _ hP]
  rfl

/-- At a coordinate line's origin, the resolvent Gram function has its
actual gradient entry as derivative. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem hasDerivAt_gramSoftMin_single_zero [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    HasDerivAt (fun x : ℝ => inversePowerSoftMin n
      (regularizedGram ε (G + x • Matrix.single i j 1)))
      (gramSoftMinGradient n ε G i j) 0 := by
  have h := hasDerivAt_gramSoftMin n hn hε G (Matrix.single i j 1) 0
  rw [inversePowerSoftMinFirst_gram_single_eq_gradient n hε] at h
  simpa only [zero_smul, add_zero] using h

/-- Each actual coordinate derivative equals the corresponding entry of
the explicit resolvent Gram gradient. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem deriv_inversePowerSoftMin_regularizedGram_single_eq [Nonempty ι]
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    deriv (fun x : ℝ => inversePowerSoftMin n
      (regularizedGram ε (G + x • Matrix.single i j 1))) 0 = gramSoftMinGradient n ε G i j := by
  have h := (hasDerivAt_gramSoftMin n hn hε G (Matrix.single i j 1) 0).deriv
  simp only [zero_smul, add_zero, mul_zero] at h
  rw [h, inversePowerSoftMinFirst_eq_trace_weight_mul]
  have hP : (inversePowerSoftMinWeight n (regularizedGram ε G))ᵀ =
      inversePowerSoftMinWeight n (regularizedGram ε G) :=
    (Matrix.isHermitian_iff_isSymm.mp (inversePowerSoftMinWeight_posSemidef n
      (regularizedGram_posDef hε G).posSemidef).isHermitian).eq
  rw [trace_mul_gram_direction _ hP G i j]
  rfl

omit [DecidableEq κ] in
/-- The derivative of the first resolvent Gram directional derivative at
zero is the explicit second Gram derivative. Source: Gram chain rule;
atlas `wishart-lambda-min-tail` (helper). -/
theorem hasDerivAt_gramSoftMin_first [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G E : Matrix ι κ ℝ) :
    HasDerivAt (fun t : ℝ => inversePowerSoftMinFirst n
      (regularizedGram ε (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ)))
      (gramSoftMinSecond n ε G E) 0 := by
  have hA := hasDerivAt_regularizedGram_add_smul ε G E 0
  have hD := hasDerivAt_regularizedGram_first G E 0
  have hpd := regularizedGram_posDef hε G
  have h := hasDerivAt_inversePowerSoftMinFirst_curve n hn hA hD
    (by simpa only [zero_smul, add_zero] using hpd.isUnit)
    (by simpa only [zero_smul, add_zero] using trace_pow_pos_of_posDef hpd.inv n)
  simpa only [mul_zero, zero_smul, add_zero, gramSoftMinSecond] using h

/-- The actual gradient entry has the explicit second Gram derivative
as derivative along its own coordinate line at zero. Source: operator
tail proof; atlas `wishart-lambda-min-tail` (helper). -/
theorem hasDerivAt_gramSoftMinGradient_single_zero [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    HasDerivAt (fun x : ℝ => gramSoftMinGradient n ε (G + x • Matrix.single i j 1) i j)
      (gramSoftMinSecond n ε G (Matrix.single i j 1)) 0 := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have h := hasDerivAt_gramSoftMin_first n hn hε G E
  have heq : (fun t : ℝ => inversePowerSoftMinFirst n
      (regularizedGram ε (G + t • E))
      (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ))) =
      (fun t : ℝ => gramSoftMinGradient n ε (G + t • E) i j) := by
    funext t
    exact inversePowerSoftMinFirst_gram_single_eq_gradient n hε G i j t
  rw [heq] at h
  exact h

omit [DecidableEq κ] in
/-- The explicit second Gram resolvent derivative equals the actual
iterated scalar derivative along its matrix line. Source: Gram chain
rule; atlas `wishart-lambda-min-tail` (helper). -/
theorem deriv_deriv_inversePowerSoftMin_regularizedGram_eq [Nonempty ι]
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (G E : Matrix ι κ ℝ) :
    deriv (fun t => deriv (fun x : ℝ => inversePowerSoftMin n
      (regularizedGram ε (G + x • E))) t) 0 = gramSoftMinSecond n ε G E := by
  have hfirst : (fun t => deriv (fun x : ℝ => inversePowerSoftMin n
      (regularizedGram ε (G + x • E))) t) =
      (fun t => inversePowerSoftMinFirst n (regularizedGram ε (G + t • E))
        (E * Gᵀ + G * Eᵀ + (2 * t) • (E * Eᵀ))) := by
    funext t
    exact (hasDerivAt_gramSoftMin n hn hε G E t).deriv
  rw [hfirst]
  exact (hasDerivAt_gramSoftMin_first n hn hε G E).deriv

/-- One coordinate's second Gram resolvent derivative is bounded by
twice the corresponding diagonal gradient weight. Source: Hessian
nonpositivity and Gram chain rule; atlas `wishart-lambda-min-tail` (helper). -/
theorem gramSoftMinSecond_single_le [Nonempty ι] (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    gramSoftMinSecond n ε G (Matrix.single i j 1) ≤
      2 * inversePowerSoftMinWeight n (regularizedGram ε G) i i := by
  set E : Matrix ι κ ℝ := Matrix.single i j 1 with hE
  have hdir : (E * Gᵀ + G * Eᵀ).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp only [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    exact add_comm _ _
  have hnonpos := inversePowerSoftMinSecond_nonpos n (regularizedGram_posDef hε G) hdir
  have hEE : E * Eᵀ = Matrix.single i i 1 := by
    rw [hE, Matrix.transpose_single, Matrix.single_mul_single_same, one_mul]
  have hfirst : inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᵀ)) =
      2 * inversePowerSoftMinWeight n (regularizedGram ε G) i i := by
    rw [inversePowerSoftMinFirst_eq_trace_weight_mul, hEE, mul_smul_comm,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_single]
    simp
  change inversePowerSoftMinSecond n (regularizedGram ε G) (E * Gᵀ + G * Eᵀ) +
    inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᵀ)) ≤ _
  rw [hfirst]
  linarith

/-- The sum of all coordinate second Gram resolvent derivatives is at
most twice the column dimension. Source: `tr(P) ≤ 1` and Hessian
nonpositivity; atlas `wishart-lambda-min-tail` (helper). -/
theorem sum_gramSoftMinSecond_single_le [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    (∑ i, ∑ j, gramSoftMinSecond n ε G (Matrix.single i j 1)) ≤ 2 * Fintype.card κ := by
  have hP := trace_inversePowerSoftMinWeight_le_one n hn (regularizedGram_posDef hε G)
  calc _ ≤ ∑ i, ∑ _j : κ, 2 * inversePowerSoftMinWeight n (regularizedGram ε G) i i := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ => gramSoftMinSecond_single_le n hε G i j
    _ = 2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.trace, Matrix.diag]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ 2 * Fintype.card κ := by nlinarith

/-- The actual coordinate Laplacian of the resolvent regularized Gram
curve is at most twice the column dimension. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem sum_deriv_deriv_inversePowerSoftMin_regularizedGram_single_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (G : Matrix ι κ ℝ) :
    (∑ i, ∑ j, deriv (fun t => deriv (fun x : ℝ => inversePowerSoftMin n
      (regularizedGram ε (G + x • Matrix.single i j 1))) t) 0) ≤ 2 * Fintype.card κ := by
  simp_rw [deriv_deriv_inversePowerSoftMin_regularizedGram_eq n hn hε]
  exact sum_gramSoftMinSecond_single_le n hn hε G

/-- The coordinate Laplacian represented by the explicit Gram Hessian.
Source: operator tail proof; atlas `wishart-lambda-min-tail` (helper). -/
def gramSoftMinLaplacian (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, gramSoftMinSecond n ε G (Matrix.single i j 1)

/-- Contracting the inverse-power Hessian over all Gram coordinates gives
an exact finite sum of trace products. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (helper). -/
theorem sum_inversePowerHessianKernel_gram_direction_eq
    (R : Matrix ι ι ℝ) (hR : R.PosSemidef) (G : Matrix ι κ ℝ) (n : ℕ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      inversePowerHessianKernel R (E * Gᵀ + G * Eᵀ) n) =
      ∑ a ∈ Finset.range (n + 1),
        (2 * Matrix.trace (R ^ (n + 2) * (G * Gᵀ)) +
          Matrix.trace (R ^ (n - a + 1)) * Matrix.trace (R ^ (a + 1) * (G * Gᵀ)) +
          Matrix.trace (R ^ (a + 1)) * Matrix.trace (R ^ (n - a + 1) * (G * Gᵀ))) := by
  unfold inversePowerHessianKernel
  dsimp only
  calc _ = (∑ i, ∑ a ∈ Finset.range (n + 1), ∑ j,
        let E : Matrix ι κ ℝ := Matrix.single i j 1
        Matrix.trace (R ^ (n - a + 1) * (E * Gᵀ + G * Eᵀ) * R ^ (a + 1) *
          (E * Gᵀ + G * Eᵀ))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = (∑ a ∈ Finset.range (n + 1), ∑ i, ∑ j,
        let E : Matrix ι κ ℝ := Matrix.single i j 1
        Matrix.trace (R ^ (n - a + 1) * (E * Gᵀ + G * Eᵀ) * R ^ (a + 1) *
          (E * Gᵀ + G * Eᵀ))) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have hX : (R ^ (n - a + 1))ᵀ = R ^ (n - a + 1) :=
        (Matrix.isHermitian_iff_isSymm.mp (hR.pow _).isHermitian).eq
      have hY : (R ^ (a + 1))ᵀ = R ^ (a + 1) :=
        (Matrix.isHermitian_iff_isSymm.mp (hR.pow _).isHermitian).eq
      rw [sum_trace_mul_gram_direction_mul_gram_direction _ _ hX hY G, ← pow_add]
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [show n - a + 1 + (a + 1) = n + 2 by omega]

/-- The exact finite resolvent Gram Laplacian in trace-power form. This
identity exposes the cancellations needed for the sharper limiting
Laplacian bound. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (helper). -/
theorem gramSoftMinLaplacian_eq (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let R := (regularizedGram ε G)⁻¹
    let T := Matrix.trace (R ^ n)
    gramSoftMinLaplacian n ε G =
      2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) +
      4 * ((n : ℝ) + 1) * T ^ (-(n : ℝ)⁻¹ - 2) * Matrix.trace (R ^ (2 * n + 2) * (G * Gᵀ)) -
      T ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ a ∈ Finset.range (n + 1),
          (2 * Matrix.trace (R ^ (n + 2) * (G * Gᵀ)) +
            Matrix.trace (R ^ (n - a + 1)) * Matrix.trace (R ^ (a + 1) * (G * Gᵀ)) +
            Matrix.trace (R ^ (a + 1)) * Matrix.trace (R ^ (n - a + 1) * (G * Gᵀ))) := by
  dsimp only
  let R := (regularizedGram ε G)⁻¹
  have hR : R.PosSemidef := hpd.inv.posSemidef
  have hX : (R ^ (n + 1))ᵀ = R ^ (n + 1) :=
    (Matrix.isHermitian_iff_isSymm.mp (hR.pow _).isHermitian).eq
  have hsq := sum_trace_mul_gram_direction_sq (R ^ (n + 1)) hX G
  rw [← pow_mul, show (n + 1) * 2 = 2 * n + 2 by omega] at hsq
  have hk := sum_inversePowerHessianKernel_gram_direction_eq R hR G n
  dsimp only [R] at hsq hk
  have hfirst : (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᵀ))) =
      2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) := by
    simp only [inversePowerSoftMinFirst_eq_trace_weight_mul, Matrix.transpose_single,
      Matrix.single_mul_single_same, one_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Matrix.trace_mul_single, op_smul_eq_smul, one_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.trace, Matrix.diag]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  unfold gramSoftMinLaplacian gramSoftMinSecond
  simp only [Finset.sum_add_distrib]
  rw [hfirst]
  unfold inversePowerSoftMinSecond
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsq, hk]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end NLAlib
