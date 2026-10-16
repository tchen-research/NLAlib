import NLAlib.Matrix.Functions.LyapunovIntegral
import Mathlib.Tactic.Module

/-! # The actual low-rank continuous Lyapunov ADI iteration

The residual factor is propagated by each Cayley transform. All finite
identities are exact; convergence is proved separately for a fixed shift.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {K n s : Type*} [RCLike K] [Fintype n] [Fintype s] [DecidableEq n]

/-- One low-rank ADI solve, with a positive real shift. -/
def lyapunovADISolve (A : Matrix n n K) (p : ℝ) (W : Matrix n s K) : Matrix n s K :=
  (A - (p : K) • 1)⁻¹ * W

/-- The actual residual-factor and solution pair after `j` solves. -/
def lyapunovADI (A : Matrix n n K) (B : Matrix n s K) (p : ℕ → ℝ) :
    ℕ → Matrix n s K × Matrix n n K
  | 0 => (B, 0)
  | j + 1 =>
    let (W, X) := lyapunovADI A B p j
    let V := lyapunovADISolve A (p j) W
    (W + (2 * p j : K) • V, X + (2 * p j : K) • (V * Vᴴ))

/-- Product of the actual ADI Cayley factors, in iteration order. -/
def lyapunovADIPropagator (A : Matrix n n K) (p : ℕ → ℝ) : ℕ → Matrix n n K
  | 0 => 1
  | j + 1 => cayleyTransform A (p j) * lyapunovADIPropagator A p j

omit [Fintype s] in
private theorem lyapunovADISolve_equation (A : Matrix n n K) (p : ℝ)
    (W : Matrix n s K) (hP : IsUnit (A - (p : K) • 1).det) :
    A * lyapunovADISolve A p W = W + (p : K) • lyapunovADISolve A p W := by
  have h := congrArg (fun M : Matrix n n K => M * W) (Matrix.mul_nonsing_inv _ hP)
  rw [Matrix.mul_assoc, Matrix.one_mul] at h
  simpa only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_iff_eq_add, lyapunovADISolve] using h

omit [Fintype s] in
private theorem lyapunovADI_factor_step (A : Matrix n n K) (p : ℝ)
    (W : Matrix n s K) (hP : IsUnit (A - (p : K) • 1).det) :
    W + (2 * p : K) • lyapunovADISolve A p W = cayleyTransform A p * W := by
  rw [cayleyTransform_eq_one_add A p hP]
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, lyapunovADISolve]

/-- The computed residual factor is exactly the propagated original factor. -/
theorem lyapunovADI_fst (A : Matrix n n K) (B : Matrix n s K) (p : ℕ → ℝ)
    (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (j : ℕ) :
    (lyapunovADI A B p j).1 = lyapunovADIPropagator A p j * B := by
  induction j with
  | zero => simp [lyapunovADI, lyapunovADIPropagator]
  | succ j hj =>
    change (lyapunovADI A B p j).1 + (2 * p j : K) •
      lyapunovADISolve A (p j) (lyapunovADI A B p j).1 = _
    rw [lyapunovADI_factor_step A (p j) _ (hP j), hj, lyapunovADIPropagator, Matrix.mul_assoc]

/-- The exact residual of the actual iterate is its computed factor Gram.
Source: user derivations, equation (G8).
atlas: lyapunov-adi-residual-factor (partial) -/
theorem lyapunovADI_residual (A : Matrix n n K) (B : Matrix n s K) (p : ℕ → ℝ)
    (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (j : ℕ) :
    A * (lyapunovADI A B p j).2 + (lyapunovADI A B p j).2 * Aᴴ + B * Bᴴ =
      (lyapunovADI A B p j).1 * (lyapunovADI A B p j).1ᴴ := by
  induction j with
  | zero => simp [lyapunovADI]
  | succ j hj =>
    let X := (lyapunovADI A B p j).2
    let W := (lyapunovADI A B p j).1
    let V := lyapunovADISolve A (p j) W
    have hAV : A * V = W + (p j : K) • V := lyapunovADISolve_equation A (p j) W (hP j)
    have hVA : Vᴴ * Aᴴ = Wᴴ + (p j : K) • Vᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        RCLike.star_def, RCLike.conj_ofReal] using congrArg Matrix.conjTranspose hAV
    change A * (X + (2 * p j : K) • (V * Vᴴ)) +
      (X + (2 * p j : K) • (V * Vᴴ)) * Aᴴ + B * Bᴴ =
      (W + (2 * p j : K) • V) * (W + (2 * p j : K) • V)ᴴ
    change A * X + X * Aᴴ + B * Bᴴ = W * Wᴴ at hj
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_mul, star_ofNat,
      RCLike.star_def, RCLike.conj_ofReal]
    rw [← Matrix.mul_assoc A V Vᴴ, hAV, Matrix.mul_assoc V Vᴴ Aᴴ, hVA]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    have hAX : A * X = W * Wᴴ - X * Aᴴ - B * Bᴴ := by rw [← hj]; abel
    rw [hAX]
    module

/-- Each actual ADI increment is positive semidefinite. -/
theorem posSemidef_lyapunovADI_increment (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hp : ∀ j, 0 < p j) (j : ℕ) :
    ((lyapunovADI A B p (j + 1)).2 - (lyapunovADI A B p j).2).PosSemidef := by
  change ((lyapunovADI A B p j).2 + (2 * p j : K) • _ - (lyapunovADI A B p j).2).PosSemidef
  rw [add_sub_cancel_left]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by exact_mod_cast mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hp j).le)

/-- The actual solution iterates are Loewner monotone from zero. -/
theorem monotone_lyapunovADI_snd (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hp : ∀ j, 0 < p j) : Monotone (fun j => (lyapunovADI A B p j).2) := by
  apply monotone_nat_of_le_succ
  intro j
  exact Matrix.le_iff.mpr (posSemidef_lyapunovADI_increment A B p hp j)

private theorem mul_cayleyTransform (A : Matrix n n K) (p : ℝ)
    (hP : IsUnit (A - (p : K) • 1).det) :
    (A - (p : K) • 1) * cayleyTransform A p = A + (p : K) • 1 := by
  rw [cayleyTransform_eq_one_add A p hP]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hP]
  module

private theorem cayley_congruence_identity (A E : Matrix n n K) (p : ℝ)
    (hP : IsUnit (A - (p : K) • 1).det) :
    (A - (p : K) • 1) * (E - cayleyTransform A p * E * (cayleyTransform A p)ᴴ) *
      (A - (p : K) • 1)ᴴ = -(2 * p : K) • (A * E + E * Aᴴ) := by
  have hT := mul_cayleyTransform A p hP
  have hstar : (cayleyTransform A p)ᴴ * (A - (p : K) • 1)ᴴ = (A + (p : K) • 1)ᴴ := by
    rw [← Matrix.conjTranspose_mul, hT]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  have hterm : (A - (p : K) • 1) * (cayleyTransform A p * E * (cayleyTransform A p)ᴴ) *
      (A - (p : K) • 1)ᴴ = (A + (p : K) • 1) * E * (A + (p : K) • 1)ᴴ := by
    simp only [← Matrix.mul_assoc] at *
    rw [hT]
    rw [Matrix.mul_assoc _ (cayleyTransform A p)ᴴ (A - (p : K) • 1)ᴴ, hstar]
  rw [hterm]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, RCLike.star_def, RCLike.conj_ofReal,
    Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  module

private theorem lyapunovADI_error_step (A E : Matrix n n K) (W : Matrix n s K)
    (p : ℝ) (hP : IsUnit (A - (p : K) • 1).det)
    (hE : A * E + E * Aᴴ + W * Wᴴ = 0) :
    E - (2 * p : K) • (lyapunovADISolve A p W * (lyapunovADISolve A p W)ᴴ) =
      cayleyTransform A p * E * (cayleyTransform A p)ᴴ := by
  let P := A - (p : K) • (1 : Matrix n n K)
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det _).mpr hP
  apply hPu.mul_left_cancel
  apply hPu.star.mul_right_cancel
  have hc := cayley_congruence_identity A E p hP
  have hR : A * E + E * Aᴴ = -(W * Wᴴ) := eq_neg_of_add_eq_zero_left hE
  rw [hR, smul_neg, neg_smul, neg_neg] at hc
  have hV : P * lyapunovADISolve A p W = W := by
    simp only [P, lyapunovADISolve, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul]
  have hGram : P * (lyapunovADISolve A p W * (lyapunovADISolve A p W)ᴴ) * Pᴴ = W * Wᴴ := by
    rw [← Matrix.mul_assoc, hV, Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hV]
  change P * (E - (2 * p : K) • _) * Pᴴ = P * (_ * E * _) * Pᴴ
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hGram]
  rw [Matrix.mul_sub, Matrix.sub_mul] at hc
  change P * E * Pᴴ - P * (cayleyTransform A p * E * (cayleyTransform A p)ᴴ) * Pᴴ =
    (2 * p : K) • (W * Wᴴ) at hc
  apply sub_eq_iff_eq_add.mpr
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp hc

/-- The exact error is propagated by the actual ordered Cayley product.
Source: user derivations, equation (G9).
atlas: lyapunov-adi-residual-factor (partial) -/
theorem sub_lyapunovADI_snd (A X : Matrix n n K) (B : Matrix n s K) (p : ℕ → ℝ)
    (hP : ∀ j, IsUnit (A - (p j : K) • 1).det)
    (hX : A * X + X * Aᴴ + B * Bᴴ = 0) (j : ℕ) :
    X - (lyapunovADI A B p j).2 =
      lyapunovADIPropagator A p j * X * (lyapunovADIPropagator A p j)ᴴ := by
  induction j with
  | zero => simp [lyapunovADI, lyapunovADIPropagator]
  | succ j hj =>
    have hR := lyapunovADI_residual A B p hP j
    have hE : A * (X - (lyapunovADI A B p j).2) +
        (X - (lyapunovADI A B p j).2) * Aᴴ +
        (lyapunovADI A B p j).1 * (lyapunovADI A B p j).1ᴴ = 0 := by
      rw [← hR, Matrix.mul_sub, Matrix.sub_mul]
      have he : A * (X - (lyapunovADI A B p j).2) =
        A * X - A * (lyapunovADI A B p j).2 := Matrix.mul_sub _ _ _
      convert hX using 1; abel
    change X - ((lyapunovADI A B p j).2 + (2 * p j : K) • _) = _
    rw [← sub_sub, lyapunovADI_error_step A _ _ (p j) (hP j) hE, hj,
      lyapunovADIPropagator, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-- The computed iterate lies between zero and every PSD solution. -/
theorem lyapunovADI_snd_nonneg_le_solution (A X : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hp : ∀ j, 0 < p j)
    (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (hX : X.PosSemidef)
    (hEq : A * X + X * Aᴴ + B * Bᴴ = 0) (j : ℕ) :
    0 ≤ (lyapunovADI A B p j).2 ∧ (lyapunovADI A B p j).2 ≤ X := by
  refine ⟨?_, Matrix.le_iff.mpr ?_⟩
  · simpa only [lyapunovADI] using monotone_lyapunovADI_snd A B p hp (Nat.zero_le j)
  · rw [sub_lyapunovADI_snd A X B p hP hEq]
    exact hX.mul_mul_conjTranspose_same _

end NLAlib
