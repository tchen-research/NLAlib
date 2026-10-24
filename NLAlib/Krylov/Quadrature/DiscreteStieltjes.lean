import NLAlib.Krylov.Quadrature.CanonicalLanczos
import NLAlib.Krylov.Quadrature.DiscreteCanonical

/-! # Stieltjes iteration on a finite weighted node set

The normalized Stieltjes procedure is implemented directly on its values at the nodes.
Its weighted three-term step is conjugate, by multiplication by square-root weights, to
the actual native Lanczos step on the diagonal node matrix. Thus the computed coefficients
agree procedurally, including termination. The monic beta convention is recorded separately:
beta zero is total mass, whereas normalized Lanczos has zero boundary coupling.

Source: Gautschi (2004), §§2.2.3.1–2.2.3.2.
Atlas: `discrete-measure-jacobi-matrix`.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private def weightVector (w p : n → ℝ) : n → ℝ := fun r => Real.sqrt (w r) * p r

private def weightedRayleigh (t w p : n → ℝ) : ℝ :=
  ∑ r, w r * p r * (t r * p r)

private def weightedNorm (w p : n → ℝ) : ℝ := Real.sqrt (∑ r, w r * p r ^ 2)

private def weightState (w : n → ℝ) (s : LanczosState n) : LanczosState n :=
  ⟨weightVector w s.prev, weightVector w s.cur, s.beta⟩

/-- Initial normalized Stieltjes state: the previous values are zero, current values are
the reciprocal square-root total mass, and the boundary coupling is zero.
The shared three-term state stores values at the nodes instead of Euclidean Lanczos vectors.
Source: Gautschi (2004), §2.2.3.1. -/
def discreteStieltjesInit (w : n → ℝ) : LanczosState n :=
  ⟨0, fun _ => (Real.sqrt (∑ r, w r))⁻¹, 0⟩

/-- The literal normalized Stieltjes step on weighted node values: compute the weighted
Rayleigh diagonal, subtract the previous two terms, and normalize the weighted residual.
All square roots and inverses are total; nonnegative weights give the intended norm.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
def discreteStieltjesStep (t w : n → ℝ) (s : LanczosState n) : LanczosState n :=
  let v := fun r => t r * s.cur r - weightedRayleigh t w s.cur * s.cur r - s.beta * s.prev r
  let β := weightedNorm w v
  ⟨s.cur, β⁻¹ • v, β⟩

/-- The state produced by iterating the actual weighted Stieltjes procedure.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
def discreteStieltjesState (t w : n → ℝ) (j : ℕ) : LanczosState n :=
  (discreteStieltjesStep t w)^[j] (discreteStieltjesInit w)

omit [DecidableEq n] in
/-- Each actual Stieltjes state is obtained by applying its weighted three-term step.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteStieltjesState_succ (t w : n → ℝ) (j : ℕ) :
    discreteStieltjesState t w (j + 1) = discreteStieltjesStep t w (discreteStieltjesState t w j) :=
  Function.iterate_succ_apply' _ _ _

/-- Actual normalized polynomial values computed at the nodes by Stieltjes iteration. -/
def discreteStieltjesValues (t w : n → ℝ) (j : ℕ) : n → ℝ :=
  (discreteStieltjesState t w j).cur

/-- The diagonal coefficient computed by the weighted Stieltjes procedure. -/
def discreteStieltjesAlpha (t w : n → ℝ) (j : ℕ) : ℝ :=
  weightedRayleigh t w (discreteStieltjesValues t w j)

/-- The normalized nonnegative coupling computed by the weighted Stieltjes procedure. -/
def discreteStieltjesBeta (t w : n → ℝ) (j : ℕ) : ℝ :=
  (discreteStieltjesState t w j).beta

/-- Monic Stieltjes beta uses total mass at index zero and the square of the normalized
coupling at positive indices. The mass is not a Jacobi boundary coupling.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
def discreteStieltjesMonicBeta (t w : n → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then ∑ r, w r else discreteStieltjesBeta t w j ^ 2

private theorem weightedRayleigh_eq_dotProduct (t w p : n → ℝ) (hw : ∀ r, 0 ≤ w r) :
    weightedRayleigh t w p = weightVector w p ⬝ᵥ (diagonal t *ᵥ weightVector w p) := by
  simp only [weightedRayleigh, Matrix.mulVec_diagonal, dotProduct, weightVector]
  apply Finset.sum_congr rfl
  intro r _
  calc
    w r * p r * (t r * p r) = Real.sqrt (w r) ^ 2 * p r * (t r * p r) := by
      rw [Real.sq_sqrt (hw r)]
    _ = _ := by ring

omit [DecidableEq n] in
private theorem weightedNorm_eq_norm (w p : n → ℝ) (hw : ∀ r, 0 ≤ w r) :
    weightedNorm w p = ‖WithLp.toLp 2 (weightVector w p)‖ := by
  have hsq : ‖WithLp.toLp 2 (weightVector w p)‖ ^ 2 = ∑ r, w r * p r ^ 2 := by
    rw [norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct, weightVector]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = Real.sqrt (w r) ^ 2 * p r ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hw r)]
  unfold weightedNorm
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

omit [Fintype n] [DecidableEq n] in
private theorem weightVector_smul (w p : n → ℝ) (a : ℝ) :
    weightVector w (a • p) = a • weightVector w p := by
  ext r
  simp only [weightVector, Pi.smul_apply, smul_eq_mul]
  ring

private theorem weightState_step (t w : n → ℝ) (hw : ∀ r, 0 ≤ w r) (s : LanczosState n) :
    weightState w (discreteStieltjesStep t w s) =
      lanczosStep (diagonal t) (weightState w s) := by
  let v := fun r => t r * s.cur r - weightedRayleigh t w s.cur * s.cur r - s.beta * s.prev r
  have hv : diagonal t *ᵥ weightVector w s.cur -
      (weightVector w s.cur ⬝ᵥ (diagonal t *ᵥ weightVector w s.cur)) • weightVector w s.cur -
      s.beta • weightVector w s.prev = weightVector w v := by
    rw [← weightedRayleigh_eq_dotProduct t w s.cur hw]
    ext r
    simp only [v, weightVector, Matrix.mulVec_diagonal, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  change LanczosState.mk (weightVector w s.cur) (weightVector w ((weightedNorm w v)⁻¹ • v))
      (weightedNorm w v) =
    LanczosState.mk (weightVector w s.cur)
      (‖WithLp.toLp 2 (diagonal t *ᵥ weightVector w s.cur -
          (weightVector w s.cur ⬝ᵥ (diagonal t *ᵥ weightVector w s.cur)) • weightVector w s.cur -
          s.beta • weightVector w s.prev)‖⁻¹ •
        (diagonal t *ᵥ weightVector w s.cur -
          (weightVector w s.cur ⬝ᵥ (diagonal t *ᵥ weightVector w s.cur)) • weightVector w s.cur -
          s.beta • weightVector w s.prev))
      ‖WithLp.toLp 2 (diagonal t *ᵥ weightVector w s.cur -
          (weightVector w s.cur ⬝ᵥ (diagonal t *ᵥ weightVector w s.cur)) • weightVector w s.cur -
          s.beta • weightVector w s.prev)‖
  rw [hv, weightedNorm_eq_norm w v hw, weightVector_smul]

omit [DecidableEq n] in
private theorem weightState_init (w : n → ℝ) (hw : ∀ r, 0 ≤ w r) :
    weightState w (discreteStieltjesInit w) = lanczosInit (fun r => Real.sqrt (w r)) := by
  have hnorm : Real.sqrt (∑ r, w r) = ‖WithLp.toLp 2 (fun r => Real.sqrt (w r))‖ := by
    have hvec : weightVector w (fun _ => 1) = fun r => Real.sqrt (w r) := by
      ext r
      simp only [weightVector, mul_one]
    have hn := weightedNorm_eq_norm w (fun _ => 1) hw
    rw [hvec] at hn
    simpa only [weightedNorm, one_pow, mul_one] using hn
  unfold weightState discreteStieltjesInit lanczosInit
  congr 1
  · ext r
    simp [weightVector]
  · ext r
    simp only [weightVector, hnorm, Pi.smul_apply, smul_eq_mul]
    ring

/-- Every actual weighted Stieltjes state is conjugate to the actual diagonal Lanczos state.
The proof iterates the literal step identity, so it also covers breakdown and later zero states.
Source: Gautschi (2004), §§2.2.3.1–2.2.3.2. -/
private theorem weightState_discreteStieltjesState (t w : n → ℝ) (hw : ∀ r, 0 ≤ w r) (j : ℕ) :
    weightState w (discreteStieltjesState t w j) =
      lanczosState (diagonal t) (fun r => Real.sqrt (w r)) j := by
  induction j with
  | zero => exact weightState_init w hw
  | succ j ih =>
    rw [discreteStieltjesState_succ, weightState_step t w hw, ih, lanczosState_succ]

/-- The actual Stieltjes values and actual Lanczos vectors satisfy the weighted evaluation
identity `qⱼ(r) = sqrt(wᵣ) pⱼ(tᵣ)` at every step, including termination.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem lanczosRecurrence_diagonal_sqrt_eq_mul_discreteStieltjesValues
    (t w : n → ℝ) (hw : ∀ r, 0 ≤ w r) (j : ℕ) (r : n) :
    lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j r =
      Real.sqrt (w r) * discreteStieltjesValues t w j r := by
  exact congrFun (congrArg LanczosState.cur (weightState_discreteStieltjesState t w hw j)).symm r

/-- The literal weighted Stieltjes diagonal coefficient equals the coefficient computed by
the actual diagonal Lanczos algorithm. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteStieltjesAlpha_eq_lanczosAlpha (t w : n → ℝ) (hw : ∀ r, 0 ≤ w r) (j : ℕ) :
    discreteStieltjesAlpha t w j = lanczosAlpha (diagonal t) (fun r => Real.sqrt (w r)) j := by
  unfold discreteStieltjesAlpha lanczosAlpha
  rw [weightedRayleigh_eq_dotProduct t w _ hw]
  have hcur := congrArg LanczosState.cur (weightState_discreteStieltjesState t w hw j)
  change weightVector w (discreteStieltjesValues t w j) =
    lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j at hcur
  rw [hcur]

/-- The normalized Stieltjes coupling equals the actual Lanczos coupling at every step.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteStieltjesBeta_eq_lanczosBeta (t w : n → ℝ) (hw : ∀ r, 0 ≤ w r) (j : ℕ) :
    discreteStieltjesBeta t w j = lanczosBeta (diagonal t) (fun r => Real.sqrt (w r)) j := by
  have h := congrArg LanczosState.beta (weightState_discreteStieltjesState t w hw j)
  exact h

omit [DecidableEq n] in
/-- Normalized Stieltjes has zero boundary coupling, before any residual is formed.
atlas: discrete-measure-jacobi-matrix (partial) -/
@[simp] theorem discreteStieltjesBeta_zero (t w : n → ℝ) :
    discreteStieltjesBeta t w 0 = 0 := rfl

omit [DecidableEq n] in
/-- The monic beta-zero convention is the total atomic mass, independently of the normalized
zero Jacobi boundary coupling. Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
@[simp] theorem discreteStieltjesMonicBeta_zero (t w : n → ℝ) :
    discreteStieltjesMonicBeta t w 0 = ∑ r, w r := by
  simp [discreteStieltjesMonicBeta]

end NLAlib
