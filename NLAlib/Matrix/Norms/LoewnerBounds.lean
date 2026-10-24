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
variable {𝕜 : Type*} [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian matrix has spectral norm at most a nonnegative scalar exactly when it lies
between the negative and positive scalar identity matrices. This finite spectral statement
works over either real or complex scalars and includes empty dimensions. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_iff_sandwich {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    specNorm A ≤ r ↔ -(r • (1 : Matrix n n 𝕜)) ≤ A ∧ A ≤ r • (1 : Matrix n n 𝕜) := by
  have hHi : cfc (fun x : ℝ => r - x) A = r • (1 : Matrix n n 𝕜) - A := by
    calc
      cfc (fun x : ℝ => r - x) A = cfc (fun _ : ℝ => r) A - cfc (fun x : ℝ => x) A :=
        cfc_sub _ _ A continuousOn_const continuousOn_id
      _ = algebraMap ℝ (Matrix n n 𝕜) r - A :=
        congrArg₂ (fun X Y : Matrix n n 𝕜 => X - Y) (cfc_const r A hA) (cfc_id' ℝ A hA)
      _ = r • (1 : Matrix n n 𝕜) - A := by rw [Algebra.algebraMap_eq_smul_one]
  have hLo : cfc (fun x : ℝ => x + r) A = A + r • (1 : Matrix n n 𝕜) := by
    calc
      cfc (fun x : ℝ => x + r) A =
          cfc (fun x : ℝ => x) A + algebraMap ℝ (Matrix n n 𝕜) r :=
        cfc_add_const r _ A continuousOn_id hA
      _ = A + algebraMap ℝ (Matrix n n 𝕜) r :=
        congrArg (fun X : Matrix n n 𝕜 => X + algebraMap ℝ (Matrix n n 𝕜) r) (cfc_id' ℝ A hA)
      _ = A + r • (1 : Matrix n n 𝕜) := by rw [Algebra.algebraMap_eq_smul_one]
  have hUpper : A ≤ r • (1 : Matrix n n 𝕜) ↔ ∀ i, hA.eigenvalues i ≤ r := by
    constructor
    · intro hb i
      have hp : 0 ≤ cfc (fun x : ℝ => r - x) A := by
        rw [hHi]
        exact sub_nonneg.mpr hb
      exact sub_nonneg.mp ((cfc_nonneg_iff (fun x : ℝ => r - x) A (by fun_prop)
        hA).mp hp _ (hA.eigenvalues_mem_spectrum_real i))
    · intro hb
      have hp : 0 ≤ cfc (fun x : ℝ => r - x) A := by
        apply (cfc_nonneg_iff (fun x : ℝ => r - x) A (by fun_prop) hA).mpr
        intro x hx
        rw [hA.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact sub_nonneg.mpr (hb i)
      rw [hHi] at hp
      exact sub_nonneg.mp hp
  have hLower : -(r • (1 : Matrix n n 𝕜)) ≤ A ↔ ∀ i, -r ≤ hA.eigenvalues i := by
    constructor
    · intro hb i
      have hp : 0 ≤ cfc (fun x : ℝ => x + r) A := by
        rw [hLo]
        exact neg_le_iff_add_nonneg.mp hb
      have hi := (cfc_nonneg_iff (fun x : ℝ => x + r) A (by fun_prop)
        hA).mp hp _ (hA.eigenvalues_mem_spectrum_real i)
      linarith
    · intro hb
      have hp : 0 ≤ cfc (fun x : ℝ => x + r) A := by
        apply (cfc_nonneg_iff (fun x : ℝ => x + r) A (by fun_prop) hA).mpr
        intro x hx
        rw [hA.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        linarith [hb i]
      rw [hLo] at hp
      exact neg_le_iff_add_nonneg.mpr hp
  rw [hA.specNorm_eq_norm_eigenvalues, hLower, hUpper]
  simp only [pi_norm_le_iff_of_nonneg hr, Real.norm_eq_abs, abs_le, forall_and]

open scoped Matrix.Norms.L2Operator in
/-- A PSD matrix has spectral norm at most a nonnegative scalar precisely
when it lies below that scalar times the identity. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_iff {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {r : ℝ} (hr : 0 ≤ r) :
    specNorm A ≤ r ↔ A ≤ r • (1 : Matrix n n 𝕜) := by
  have hD : cfc (fun x : ℝ => r - x) A = r • (1 : Matrix n n 𝕜) - A := by
    calc
      cfc (fun x : ℝ => r - x) A = cfc (fun _ : ℝ => r) A - cfc (fun x : ℝ => x) A :=
        cfc_sub _ _ A continuousOn_const continuousOn_id
      _ = algebraMap ℝ (Matrix n n 𝕜) r - A :=
        congrArg₂ (fun X Y : Matrix n n 𝕜 => X - Y)
          (cfc_const r A hA.isHermitian) (cfc_id' ℝ A hA.isHermitian)
      _ = r • (1 : Matrix n n 𝕜) - A := by rw [Algebra.algebraMap_eq_smul_one]
  rw [hA.isHermitian.specNorm_eq_norm_eigenvalues]
  constructor
  · intro hnorm
    apply Matrix.le_iff.mpr
    rw [← hD]
    apply Matrix.nonneg_iff_posSemidef.mp
    apply (cfc_nonneg_iff _ _ (continuousOn_const.sub continuousOn_id) hA.isHermitian).mpr
    intro x hx
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact sub_nonneg.mpr
      (((Real.le_norm_self _).trans (norm_le_pi_norm hA.isHermitian.eigenvalues i)).trans hnorm)
  · intro horder
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
    have hp : 0 ≤ cfc (fun x : ℝ => r - x) A := by
      rw [hD]
      exact sub_nonneg.mpr horder
    have hs := (cfc_nonneg_iff _ _ (continuousOn_const.sub continuousOn_id)
      hA.isHermitian).mp hp
    exact sub_nonneg.mp (hs _ (hA.isHermitian.eigenvalues_mem_spectrum_real i))

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

omit [DecidableEq m] in
/-- A rectangular Gram domination bounds the squared spectral norm, including
empty index sets and a zero upper bound. -/
theorem specNorm_sq_le_of_conjTranspose_mul_self_le (A : Matrix m n 𝕜)
    {r : ℝ} (hr : 0 ≤ r) (hA : Aᴴ * A ≤ r • (1 : Matrix n n 𝕜)) :
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
