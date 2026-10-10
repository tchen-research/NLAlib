import NLAlib.Matrix.InverseCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Weighted spectral inequalities for inverse trace powers

The Hessian kernel of an inverse trace power dominates its diagonal part.
A weighted Cauchy--Schwarz inequality controls the square of its first
derivative. Together these are the algebraic basis for the concavity of
the resolvent approximation to the smallest eigenvalue.

Source: operator re-derivation of the smallest Wishart eigenvalue bound.
Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Trace is invariant under unitary conjugation. Source: matrix trace
cyclicity; atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_conjStarAlgAut (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    Matrix.trace (Unitary.conjStarAlgAut ℝ _ U A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

/-- A symmetric matrix quadratic trace in a diagonal basis is a weighted
sum of squares. Source: ported from SparseFockFormal,
`TracePowerConvexity.trace_mul_diagonal_pow_mul_mul_diagonal_pow`;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_mul_diagonal_pow_mul_mul_diagonal_pow (B : Matrix ι ι ℝ)
    (hB : Bᵀ = B) (ev : ι → ℝ) (a c : ℕ) :
    Matrix.trace (B * (Matrix.diagonal ev) ^ a * B * (Matrix.diagonal ev) ^ c) =
      ∑ i, ∑ j, B i j ^ 2 * ev j ^ a * ev i ^ c := by
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow,
    Matrix.mul_assoc B (Matrix.diagonal (ev ^ a)) B]
  have hentry (i : ι) : (B * (Matrix.diagonal (ev ^ a) * B)) i i =
      ∑ j, B i j * (ev j ^ a * B j i) := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diagonal_mul]
    rfl
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  simp_rw [hentry]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrFun (congrFun hB j) i
  simp only [Matrix.transpose_apply] at hs
  rw [hs]
  simp only [Pi.pow_apply]
  ring

/-- The quadratic kernel arising as the second derivative of an inverse
trace power. Source: finite noncommutative power rule; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
def inversePowerHessianKernel (R B : Matrix ι ι ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Matrix.trace (R ^ (n - i + 1) * B * R ^ (i + 1) * B)

/-- The inverse-power Hessian kernel dominates the square of the first
trace derivative by weighted Cauchy--Schwarz. Source: resolvent operator
proof; atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem mul_trace_pow_mul_sq_le_trace_pow_mul_inversePowerHessianKernel
    {R B : Matrix ι ι ℝ} (hR : R.PosSemidef) (hB : B.IsHermitian) (n : ℕ) :
    ((n : ℝ) + 1) * Matrix.trace (R ^ (n + 1) * B) ^ 2 ≤
      Matrix.trace (R ^ n) * inversePowerHessianKernel R B n := by
  let U := star hR.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  let C := φ B
  let ev := hR.isHermitian.eigenvalues
  have hdiag : φ R = Matrix.diagonal ev := by
    dsimp only [φ, U, ev]
    simpa using hR.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hC : Cᵀ = C := by
    have hh : C.IsHermitian := hB.isSelfAdjoint.map φ |>.isHermitian
    exact (Matrix.isHermitian_iff_isSymm.mp hh).eq
  have hev : ∀ i, 0 ≤ ev i := hR.eigenvalues_nonneg
  have hT : Matrix.trace (R ^ n) = ∑ i, ev i ^ n := by
    calc _ = Matrix.trace (φ (R ^ n)) := (trace_conjStarAlgAut U _).symm
      _ = _ := by simp only [map_pow, hdiag, Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]
  have hL : Matrix.trace (R ^ (n + 1) * B) = ∑ i, ev i ^ (n + 1) * C i i := by
    calc _ = Matrix.trace (φ (R ^ (n + 1) * B)) := (trace_conjStarAlgAut U _).symm
      _ = _ := by simp only [map_mul, map_pow, hdiag, Matrix.diagonal_pow,
        Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Pi.pow_apply]; rfl
  have hterm (a : ℕ) : Matrix.trace (R ^ (n - a + 1) * B * R ^ (a + 1) * B) =
      ∑ i, ∑ j, C i j ^ 2 * ev j ^ (n - a + 1) * ev i ^ (a + 1) := by
    calc _ = Matrix.trace (φ (R ^ (n - a + 1) * B * R ^ (a + 1) * B)) :=
          (trace_conjStarAlgAut U _).symm
      _ = Matrix.trace ((Matrix.diagonal ev) ^ (n - a + 1) * C *
            (Matrix.diagonal ev) ^ (a + 1) * C) := by simp only [map_mul, map_pow, hdiag]; rfl
      _ = Matrix.trace (C * (Matrix.diagonal ev) ^ (n - a + 1) * C *
            (Matrix.diagonal ev) ^ (a + 1)) := by
          rw [Matrix.trace_mul_cycle]
          simp only [Matrix.mul_assoc]
      _ = _ := trace_mul_diagonal_pow_mul_mul_diagonal_pow C hC ev _ _
  let D : ℝ := ∑ i, ev i ^ (n + 2) * C i i ^ 2
  have hkernel : ((n : ℝ) + 1) * D ≤ inversePowerHessianKernel R B n := by
    calc _ = ∑ _a ∈ Finset.range (n + 1), D := by simp
      _ ≤ inversePowerHessianKernel R B n := by
        apply Finset.sum_le_sum
        intro a ha
        rw [hterm]
        apply Finset.sum_le_sum
        intro i _
        have hai : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hdiagterm : ev i ^ (n + 2) * C i i ^ 2 =
            C i i ^ 2 * ev i ^ (n - a + 1) * ev i ^ (a + 1) := by
          rw [mul_assoc, ← pow_add, show n - a + 1 + (a + 1) = n + 2 by omega]
          ring
        rw [hdiagterm]
        exact Finset.single_le_sum (f := fun j =>
          C i j ^ 2 * ev j ^ (n - a + 1) * ev i ^ (a + 1))
          (fun j _ => mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (hev j) _))
            (pow_nonneg (hev i) _)) (Finset.mem_univ i)
  have hCS : Matrix.trace (R ^ (n + 1) * B) ^ 2 ≤ Matrix.trace (R ^ n) * D := by
    rw [hT, hL]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro i _; exact pow_nonneg (hev i) _
    · intro i _; exact mul_nonneg (pow_nonneg (hev i) _) (sq_nonneg _)
    · intro i _
      have hpow : (ev i ^ (n + 1)) ^ 2 = ev i ^ n * ev i ^ (n + 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [mul_pow, hpow]
      ring_nf
      exact le_refl _
  have hTnn : 0 ≤ Matrix.trace (R ^ n) := by rw [hT]; exact Finset.sum_nonneg fun i _ => pow_nonneg (hev i) _
  calc ((n : ℝ) + 1) * Matrix.trace (R ^ (n + 1) * B) ^ 2
      ≤ ((n : ℝ) + 1) * (Matrix.trace (R ^ n) * D) := by gcongr
    _ = Matrix.trace (R ^ n) * (((n : ℝ) + 1) * D) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hTnn

/-- Every natural trace power of a positive definite real matrix has
positive trace in nonzero dimension. Source: spectral theorem; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_pow_pos_of_posDef [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (n : ℕ) : 0 < Matrix.trace (R ^ n) := by
  rw [hR.isHermitian.spectral_theorem, ← map_pow, trace_conjStarAlgAut,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  change 0 < ∑ i, hR.isHermitian.eigenvalues i ^ n
  exact Finset.sum_pos (fun i _ => pow_pos (hR.eigenvalues_pos i) n) Finset.univ_nonempty

/-- Resolvent approximation to the smallest eigenvalue: the negative
`n`th root of the inverse-power trace. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
def inversePowerSoftMin (n : ℕ) (A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹)

/-- First directional derivative of the resolvent approximation. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (operator calculus helper). -/
def inversePowerSoftMinFirst (n : ℕ) (A B : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) * Matrix.trace (A⁻¹ ^ (n + 1) * B)

/-- Positive semidefinite gradient weight for the resolvent approximation.
Source: operator tail proof; atlas `wishart-lambda-min-tail` (operator
calculus helper). -/
def inversePowerSoftMinWeight (n : ℕ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) • A⁻¹ ^ (n + 1)

/-- The first directional derivative is the trace pairing with the
resolvent gradient weight. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem inversePowerSoftMinFirst_eq_trace_weight_mul (n : ℕ)
    (A B : Matrix ι ι ℝ) :
    inversePowerSoftMinFirst n A B = Matrix.trace (inversePowerSoftMinWeight n A * B) := by
  simp only [inversePowerSoftMinFirst, inversePowerSoftMinWeight, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul]

/-- The resolvent gradient weight is positive semidefinite at a positive
semidefinite matrix. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem inversePowerSoftMinWeight_posSemidef (n : ℕ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (inversePowerSoftMinWeight n A).PosSemidef := by
  exact (hA.inv.pow (n + 1)).smul (Real.rpow_nonneg
    (hA.inv.pow n).trace_nonneg _)

/-- The resolvent gradient weight has trace at most one, the key bound
for the Gram-chain Laplacian estimate. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_inversePowerSoftMinWeight_le_one [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {A : Matrix ι ι ℝ} (hA : A.PosDef) : Matrix.trace (inversePowerSoftMinWeight n A) ≤ 1 := by
  set R := A⁻¹
  set T := Matrix.trace (R ^ n) with hTdef
  have hR : R.PosDef := hA.inv
  have hT : 0 < T := trace_pow_pos_of_posDef hR n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let ev := hR.isHermitian.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := fun i => (hR.eigenvalues_pos i).le
  have htrace (m : ℕ) : Matrix.trace (R ^ m) = ∑ i, ev i ^ m := by
    rw [hR.isHermitian.spectral_theorem, ← map_pow, trace_conjStarAlgAut,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have hroot (i : ι) : ev i ≤ T ^ (n : ℝ)⁻¹ := by
    have hsingle : ev i ^ n ≤ T := by
      rw [hTdef, htrace]
      exact Finset.single_le_sum (fun j _ => pow_nonneg (hev j) n) (Finset.mem_univ i)
    have h := Real.rpow_le_rpow (pow_nonneg (hev i) n) hsingle
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    rw [← Real.rpow_natCast (ev i) n, Real.rpow_rpow_inv (hev i) hn0] at h
    exact h
  have hnext : Matrix.trace (R ^ (n + 1)) ≤ T * T ^ (n : ℝ)⁻¹ := by
    rw [htrace, hTdef, htrace, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [pow_succ]
    simpa only [hTdef, htrace] using
      mul_le_mul_of_nonneg_left (hroot i) (pow_nonneg (hev i) n)
  have heq : T ^ (-(n : ℝ)⁻¹ - 1) * (T * T ^ (n : ℝ)⁻¹) = 1 := by
    nth_rw 2 [← Real.rpow_one T]
    rw [← mul_assoc, ← Real.rpow_add hT, ← Real.rpow_add hT,
      show (-(n : ℝ)⁻¹ - 1) + 1 + (n : ℝ)⁻¹ = 0 by ring, Real.rpow_zero]
  unfold inversePowerSoftMinWeight
  rw [Matrix.trace_smul, smul_eq_mul]
  change T ^ (-(n : ℝ)⁻¹ - 1) * Matrix.trace (R ^ (n + 1)) ≤ 1
  exact (mul_le_mul_of_nonneg_left hnext (Real.rpow_nonneg hT.le _)).trans_eq heq

/-- Second directional derivative of the resolvent approximation. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (operator calculus helper). -/
def inversePowerSoftMinSecond (n : ℕ) (A B : Matrix ι ι ℝ) : ℝ :=
  ((n : ℝ) + 1) * Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) *
      Matrix.trace (A⁻¹ ^ (n + 1) * B) ^ 2 -
    Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) * inversePowerHessianKernel A⁻¹ B n

/-- The resolvent approximation has its explicit first derivative along
any differentiable invertible matrix curve with positive inverse-power trace. Source:
operator tail proof; atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_inversePowerSoftMin_curve (n : ℕ) (hn : 0 < n)
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t))
    (hT : 0 < Matrix.trace ((A t)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMin n (A x))
      (inversePowerSoftMinFirst n (A t) A') t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := (hasDerivAt_matrix_trace_inv_pow hA hunit n).rpow_const
    (p := -(n : ℝ)⁻¹) (Or.inl hT.ne')
  convert! h using 1
  · unfold inversePowerSoftMinFirst
    field_simp

/-- The resolvent approximation has its explicit first derivative along
an affine matrix line. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_inversePowerSoftMin (n : ℕ) (hn : 0 < n)
    (A B : Matrix ι ι ℝ) (t : ℝ) (hunit : IsUnit (A + t • B))
    (hT : 0 < Matrix.trace ((A + t • B)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMin n (A + x • B))
      (inversePowerSoftMinFirst n (A + t • B) B) t := by
  have hline : HasDerivAt (fun x : ℝ => A + x • B) B t := by
    simpa using ((hasDerivAt_id t).smul_const B).const_add A
  exact hasDerivAt_inversePowerSoftMin_curve n hn hline hunit hT

/-- Along a twice differentiable matrix curve, the derivative of the
resolvent first derivative is its directional Hessian plus the trace
pairing with the second curve derivative. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_inversePowerSoftMinFirst_curve (n : ℕ) (hn : 0 < n)
    {A D : ℝ → Matrix ι ι ℝ} {D' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A (D t) t) (hD : HasDerivAt D D' t)
    (hunit : IsUnit (A t)) (hT : 0 < Matrix.trace ((A t)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMinFirst n (A x) (D x))
      (inversePowerSoftMinSecond n (A t) (D t) +
        inversePowerSoftMinFirst n (A t) D') t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpower := (hasDerivAt_matrix_trace_inv_pow hA hunit n).rpow_const
    (p := -(n : ℝ)⁻¹ - 1) (Or.inl hT.ne')
  have hmul := hpower.mul (hasDerivAt_matrix_trace_inv_pow_mul hA hD hunit n)
  convert! hmul using 1
  · unfold inversePowerSoftMinSecond inversePowerSoftMinFirst inversePowerHessianKernel
    have he : -(n : ℝ)⁻¹ - 1 - 1 = -(n : ℝ)⁻¹ - 2 := by ring
    rw [he]
    field_simp
    ring

/-- The derivative of the resolvent approximation's first directional
derivative is its explicit Hessian. Source: operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_inversePowerSoftMinFirst (n : ℕ) (hn : 0 < n)
    (A B : Matrix ι ι ℝ) (t : ℝ) (hunit : IsUnit (A + t • B))
    (hT : 0 < Matrix.trace ((A + t • B)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMinFirst n (A + x • B) B)
      (inversePowerSoftMinSecond n (A + t • B) B) t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hline : HasDerivAt (fun x : ℝ => A + x • B) B t := by
    simpa using ((hasDerivAt_id t).smul_const B).const_add A
  have hpower := (hasDerivAt_matrix_trace_inv_pow hline hunit n).rpow_const
    (p := -(n : ℝ)⁻¹ - 1) (Or.inl hT.ne')
  have hmul := hpower.mul (hasDerivAt_matrix_trace_inv_pow_mul_const A B n t hunit)
  convert! hmul using 1
  · unfold inversePowerSoftMinSecond inversePowerHessianKernel
    have he : -(n : ℝ)⁻¹ - 1 - 1 = -(n : ℝ)⁻¹ - 2 := by ring
    rw [he]
    field_simp
    ring

/-- The resolvent approximation's directional Hessian is nonpositive
at positive definite matrices in symmetric directions. Source: weighted
spectral Cauchy--Schwarz in the operator tail proof; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem inversePowerSoftMinSecond_nonpos [Nonempty ι] (n : ℕ)
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.IsHermitian) :
    inversePowerSoftMinSecond n A B ≤ 0 := by
  have hT := trace_pow_pos_of_posDef hA.inv n
  have hCS := mul_trace_pow_mul_sq_le_trace_pow_mul_inversePowerHessianKernel
    hA.inv.posSemidef hB n
  have he : -(n : ℝ)⁻¹ - 1 = (-(n : ℝ)⁻¹ - 2) + 1 := by ring
  unfold inversePowerSoftMinSecond
  rw [he, Real.rpow_add hT, Real.rpow_one]
  have hpos : 0 ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) := Real.rpow_nonneg hT.le _
  nlinarith [mul_le_mul_of_nonneg_left hCS hpos]

end NLAlib
