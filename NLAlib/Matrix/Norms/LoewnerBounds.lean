import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Spectral.SpectralBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-! # Spectral norm bounds from the Loewner order

The positive Gram matrix translates finite matrix order bounds to named
spectral norms. Largest-eigenvalue bounds do not require positivity of the
matrix whose quadratic form is being bounded.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A PSD matrix has spectral norm at most a nonnegative scalar precisely
when it lies below that scalar times the identity. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_iff {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {r : ℝ} (hr : 0 ≤ r) :
    specNorm A ≤ r ↔ A ≤ r • (1 : Matrix n n ℂ) := by
  simpa only [specNorm_eq_norm, Algebra.algebraMap_eq_smul_one] using
    CStarAlgebra.norm_le_iff_le_algebraMap A hr hA.nonneg

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian matrix lies below its spectral norm times the identity. -/
theorem _root_.Matrix.IsHermitian.le_specNorm_smul_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : A ≤ specNorm A • (1 : Matrix n n ℂ) := by
  simpa only [specNorm_eq_norm, Algebra.algebraMap_eq_smul_one] using
    hA.isSelfAdjoint.le_algebraMap_norm_self

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian matrix lies below its largest eigenvalue times the identity.
The largest eigenvalue is used, rather than the largest absolute eigenvalue. -/
theorem _root_.Matrix.IsHermitian.le_lambdaMax_smul_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : A ≤ lambdaMax A • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  apply le_algebraMap_of_spectrum_le (a := A)
  intro x hx
  exact le_csSup (by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).bddAbove) hx

/-- A rectangular Gram domination bounds the squared spectral norm, including
empty index sets and a zero upper bound. -/
theorem specNorm_sq_le_of_conjTranspose_mul_self_le (A : Matrix m n ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hA : Aᴴ * A ≤ r • (1 : Matrix n n ℂ)) :
    specNorm A ^ 2 ≤ r := by
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).specNorm_le_iff hr |>.mpr hA

variable {ι : Type*} [Fintype ι]

open scoped Matrix.Norms.L2Operator in
/-- The sum of squared differences of two Hermitian arrays has spectral
norm at most twice the sum of the two individual square-mass norms.
The finite matrix and array index types may be empty. -/
theorem specNorm_sum_sub_sq_le (U V : ι → Matrix n n ℂ)
    (hU : ∀ i, (U i).IsHermitian) (hV : ∀ i, (V i).IsHermitian) :
    specNorm (∑ i, (U i - V i) ^ 2) ≤
      2 * (specNorm (∑ i, U i ^ 2) + specNorm (∑ i, V i ^ 2)) := by
  classical
  have hsq (A : Matrix n n ℂ) (hA : A.IsHermitian) : 0 ≤ A ^ 2 := by
    simpa only [hA.eq, pow_two] using (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hle : (∑ i, (U i - V i) ^ 2) ≤
      (2 : ℝ) • ((∑ i, U i ^ 2) + ∑ i, V i ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← sub_nonneg]
    convert hsq (U i + V i) ((hU i).add (hV i)) using 1
    simp only [pow_two, two_smul]
    noncomm_ring
  have hn := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (Finset.sum_nonneg (fun i _ => hsq _ ((hU i).sub (hV i)))) hle
  calc
    _ ≤ ‖(2 : ℝ) • ((∑ i, U i ^ 2) + ∑ i, V i ^ 2)‖ := hn
    _ = 2 * ‖(∑ i, U i ^ 2) + ∑ i, V i ^ 2‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ _ := by
      simpa only [specNorm_eq_norm] using
        mul_le_mul_of_nonneg_left
          (norm_add_le (∑ i, U i ^ 2) (∑ i, V i ^ 2)) (by norm_num : (0 : ℝ) ≤ 2)

end NLAlib
