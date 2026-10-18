import NLAlib.Matrix.Norms.SchattenNormalization
import NLAlib.Matrix.Functions.FunctionalCalculusEigenvalues
import NLAlib.Matrix.Functions.CFCTrace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Schatten norms of positive real powers and matrix moduli

The real functional-calculus power of a positive matrix raises every
singular value to that power. This gives the exact Schatten norm identity
for `|A|^(1/r)` used in the multivariate ALT and Golden--Thompson formulas.
Zero singular values and empty dimensions are included.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, equation (35).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A nonnegative real functional-calculus power raises each positive-matrix
singular value to that power, with the usual scalar zero-power convention. -/
theorem singularValues_rpow_of_posSemidef {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) (i : Fin (Fintype.card n)) :
    singularValues (CFC.rpow A s) (i : ℕ) = singularValues A i ^ s := by
  change singularValues (A ^ s) (i : ℕ) = _
  rw [CFC.rpow_eq_cfc_real hA.nonneg]
  have hEig (j : Fin (Fintype.card n)) : 0 ≤ hA.isHermitian.eigenvalues₀ j := by
    rw [← singularValues_eq_eigenvalues₀_of_posSemidef hA j]
    exact singularValues_nonneg A j
  have hc : (cfc (fun x : ℝ => x ^ s) A).PosSemidef :=
    posSemidef_cfc_of_nonneg_eigenvalues hA.isHermitian
      (fun j => Real.rpow_nonneg (hA.eigenvalues_nonneg j) s)
  rw [singularValues_eq_eigenvalues₀_of_posSemidef hc,
    eigenvalues₀_cfc_of_antitone (fun x : ℝ => x ^ s) hA.isHermitian
      (fun j k hjk => Real.rpow_le_rpow (hEig k) (hA.isHermitian.eigenvalues₀_antitone hjk) hs),
    singularValues_eq_eigenvalues₀_of_posSemidef hA]

open scoped Matrix.Norms.L2Operator in
/-- A positive matrix's real power has exactly the corresponding Schatten
norm power, with no invertibility or nonempty-dimension assumptions. -/
theorem schattenNormReal_rpow_of_posSemidef {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    schattenNormReal (CFC.rpow A s) p = schattenNormReal A (p * s) ^ s := by
  have hsum : (∑ i ∈ Finset.range (Fintype.card n), singularValues (CFC.rpow A s) i ^ p) =
      ∑ i ∈ Finset.range (Fintype.card n), singularValues A i ^ (p * s) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [singularValues_rpow_of_posSemidef hA hs.le ⟨i, Finset.mem_range.mp hi⟩,
      ← Real.rpow_mul (singularValues_nonneg A i), mul_comm s p]
  simp only [schattenNormReal, min_self]
  rw [hsum, ← Real.rpow_mul
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) (p * s))]
  congr 1
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- The native CFC modulus has exactly the original singular values, for
an arbitrary real or complex matrix. -/
theorem singularValues_cfcAbs (A : Matrix n n 𝕜) :
    singularValues (CFC.abs A) = singularValues A := by
  have hAbs : (CFC.abs A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)
  apply funext
  intro i
  apply singularValues_eq_of_gram_eq
  rw [hAbs.isHermitian.eq, CFC.abs_mul_abs]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- Taking the native CFC modulus preserves every finite Schatten power
formula, even at exponents outside the norm range. -/
theorem schattenNormReal_cfcAbs (A : Matrix n n 𝕜) (p : ℝ) :
    schattenNormReal (CFC.abs A) p = schattenNormReal A p := by
  simp only [schattenNormReal, singularValues_cfcAbs]

open scoped Matrix.Norms.L2Operator in
/-- Exact Schatten/CFC identity for the ALT modulus-power expression. -/
theorem schattenNormReal_rpow_abs (A : Matrix n n 𝕜) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) :
    schattenNormReal (CFC.rpow (CFC.abs A) (1 / r)) p =
      schattenNormReal A (p / r) ^ (1 / r) := by
  rw [schattenNormReal_rpow_of_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)) hp (one_div_pos.mpr hr),
    schattenNormReal_cfcAbs, ← div_eq_mul_one_div]

end NLAlib
