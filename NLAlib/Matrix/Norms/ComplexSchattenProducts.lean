import NLAlib.Matrix.Norms.Realification
import NLAlib.Matrix.Norms.SchattenProducts

/-!
# Complex Schatten product Hölder

Realification transfers the checked real Schatten product inequality without
changing its constant: the dimension-doubling factors cancel by the Hölder
reciprocal-exponent identity.
-/

noncomputable section
namespace NLAlib

/-- Complex square-matrix Schatten product Hölder with sharp constant one,
for every positive finite Hölder triple, including empty dimensions. -/
theorem schattenNormReal_mul_le_mul_complex {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) {p s r : ℝ} (hpsr : Real.HolderTriple p s r) :
    schattenNormReal (A*B) r ≤ schattenNormReal A p * schattenNormReal B s := by
  have h := schattenNormReal_mul_le_mul (matrixRealification A) (matrixRealification B) hpsr
  rw [←matrixRealification_mul,schattenNormReal_matrixRealification,
    schattenNormReal_matrixRealification,schattenNormReal_matrixRealification] at h
  have heq : (2 : ℝ)^(1/r) = 2^(1/p) * 2^(1/s) := by
    rw [←Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    simpa only [one_div] using hpsr.inv_add_inv_eq_inv.symm
  rw [heq] at h
  have hpos : 0 < (2 : ℝ)^(1/p) * 2^(1/s) := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith [h]

end NLAlib
