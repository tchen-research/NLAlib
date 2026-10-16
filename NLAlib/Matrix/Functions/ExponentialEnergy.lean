import NLAlib.Matrix.Functions.ExpLog
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Matrix exponential bounds from an energy inequality

An integrating factor applied to each Euclidean orbit proves the sharp
semigroup estimate associated with a bound on the Hermitian part.
Higham, Functions of Matrices; toolkit derivations, Section `eq-lognorm`.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each Euclidean orbit of a matrix exponential solves the associated
constant-coefficient differential equation. -/
theorem hasDerivAt_matrixExp_orbit (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (matrixExp (s • A)).toEuclideanLin x)
      (A.toEuclideanLin ((matrixExp (t • A)).toEuclideanLin x)) t := by
  let L : Matrix n n ℂ →ₗ[ℝ] EuclideanSpace ℂ n :=
    ((LinearMap.applyₗ x).comp Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  convert! h using 1
  change WithLp.toLp 2 (A *ᵥ ((NormedSpace.exp (t • A)) *ᵥ x.ofLp)) =
    WithLp.toLp 2 ((A * NormedSpace.exp (t • A)) *ᵥ x.ofLp)
  rw [Matrix.mulVec_mulVec]

/-- The exponential inherits every uniform upper bound on the real
quadratic form of its generator. The constant may be negative. -/
theorem specNorm_matrixExp_smul_le_of_energy_bound (A : Matrix n n ℂ) (c : ℝ)
    (hA : ∀ x : EuclideanSpace ℂ n,
      inner ℝ x (A.toEuclideanLin x) ≤ c * ‖x‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) : specNorm (matrixExp (t • A)) ≤ Real.exp (t * c) := by
  have horbit (x : EuclideanSpace ℂ n) :
      ‖(NormedSpace.exp (t • A) : Matrix n n ℂ).toEuclideanLin x‖ ≤
        Real.exp (t * c) * ‖x‖ := by
    let L : Matrix n n ℂ →ₗ[ℝ] EuclideanSpace ℂ n :=
      ((LinearMap.applyₗ x).comp Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ
    let z (s : ℝ) := L (NormedSpace.exp (s • A))
    have hz (s : ℝ) : HasDerivAt z (A.toEuclideanLin (z s)) s := by
      exact hasDerivAt_matrixExp_orbit A x s
    let F (s : ℝ) := Real.exp (-2 * c * s) * ‖z s‖ ^ 2
    let D (s : ℝ) := Real.exp (-2 * c * s) *
      (2 * inner ℝ (z s) (A.toEuclideanLin (z s)) - 2 * c * ‖z s‖ ^ 2)
    have hF (s : ℝ) : HasDerivAt F (D s) s := by
      have h := (((hasDerivAt_id s).const_mul (-2 * c)).exp).mul (hz s).norm_sq
      convert! h using 1
      dsimp [D]
      ring
    have hanti : Antitone F := antitone_of_hasDerivAt_nonpos hF (fun s => by
      dsimp [D]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by nlinarith [hA (z s)]))
    have he := hanti ht
    have hz0 : z 0 = x := by
      change (NormedSpace.exp ((0 : ℝ) • A) : Matrix n n ℂ).toEuclideanLin x = x
      simp [Matrix.toEuclideanLin]
    change Real.exp (-2 * c * t) * ‖z t‖ ^ 2 ≤ Real.exp (-2 * c * 0) * ‖z 0‖ ^ 2 at he
    rw [hz0] at he
    simp only [mul_zero, Real.exp_zero, one_mul] at he
    have hex : Real.exp (-2 * c * t) * (Real.exp (t * c) * ‖x‖) ^ 2 = ‖x‖ ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      have heq : -2 * c * t + 2 * (t * c) = 0 := by ring
      rw [heq, Real.exp_zero, one_mul]
    have hsq : ‖z t‖ ^ 2 ≤ (Real.exp (t * c) * ‖x‖) ^ 2 :=
      (mul_le_mul_iff_right₀ (Real.exp_pos (-2 * c * t))).mp (he.trans_eq hex.symm)
    have hn : 0 ≤ Real.exp (t * c) * ‖x‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) hn).mp hsq
  rw [specNorm_eq_norm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro x
  exact horbit x

end NLAlib
