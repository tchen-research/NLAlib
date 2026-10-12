import NLAlib.Matrix.Inequalities.BlockOrderConsequences
/-!
# Kantorovich's inequality from spectral endpoints

A scalar endpoint inequality gives the matrix inequality
`A + ab A⁻¹ ≤ (a+b)I`, and the two quadratic moments yield the exact
Kantorovich constant. Source: Horn--Johnson (2013), Section 7.4.12;
atlas `kantorovich-inequality`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite matrix between positive scalar endpoints satisfies
the sharp reciprocal linear inequality. Horn--Johnson (2013), Section 7.4.12;
helper for Kantorovich's inequality. -/
theorem add_smul_inv_le_smul_one_of_sandwich {A : Matrix n n ℝ}
    (hA : A.PosDef) {a b : ℝ} (ha : 0 < a)
    (hlo : a • (1 : Matrix n n ℝ) ≤ A) (hhi : A ≤ b • (1 : Matrix n n ℝ)) :
    A + (a * b) • A⁻¹ ≤ (a + b) • (1 : Matrix n n ℝ) := by
  have hs : ∀ t ∈ spectrum ℝ A, a ≤ t ∧ t ≤ b := by
    have h := (loewner_sandwich_iff_relative_spectrum_subset Matrix.PosDef.one hA.isHermitian a b).mp
      ⟨hlo, hhi⟩
    simpa only [inv_one, Matrix.one_mul, Set.subset_def, Set.mem_Icc] using h
  have hf : ∀ t ∈ spectrum ℝ A, t + a * b * t⁻¹ ≤ a + b := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le (hs t ht).1
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hs t ht).1)
      (sub_nonpos.mpr (hs t ht).2)
    calc
      t + a * b * t⁻¹ = (t ^ 2 + a * b) / t := by field_simp
      _ ≤ a + b := (div_le_iff₀ ht0).mpr (by nlinarith)
  have hinv : cfc (fun t : ℝ => t⁻¹) A = A⁻¹ := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      cfc_ringInverse_id (R := ℝ) (p := IsSelfAdjoint) (a := A) hA.isUnit hA.isHermitian
  have hfc : cfc (fun t : ℝ => t + a * b * t⁻¹) A = A + (a * b) • A⁻¹ := by
    rw [cfc_add (p := IsSelfAdjoint) A (fun t : ℝ => t) (fun t : ℝ => a * b * t⁻¹)
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_id' (p := IsSelfAdjoint) ℝ A hA.isHermitian,
      cfc_const_mul (p := IsSelfAdjoint) (a * b) (fun t : ℝ => t⁻¹) A (A.finite_real_spectrum.continuousOn _), hinv]
  have h := (cfc_le_algebraMap_iff (p := IsSelfAdjoint) (fun t : ℝ => t + a * b * t⁻¹) (a + b) A
    (A.finite_real_spectrum.continuousOn _) hA.isHermitian).mpr hf
  rw [hfc, Algebra.algebraMap_eq_smul_one] at h
  exact h

/-- Kantorovich's quadratic-form inequality with arbitrary positive spectral
endpoints. The squared Euclidean length is `x ⬝ᵥ x`, so the final factor is
the fourth power of the Euclidean norm. Empty dimensions and the zero vector
are included. Horn--Johnson (2013), Section 7.4.12.
atlas: kantorovich-inequality (partial) -/
theorem quadForm_mul_quadForm_inv_le_of_sandwich {A : Matrix n n ℝ}
    (hA : A.PosDef) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlo : a • (1 : Matrix n n ℝ) ≤ A) (hhi : A ≤ b • (1 : Matrix n n ℝ))
    (x : n → ℝ) :
    quadForm A x * quadForm A⁻¹ x ≤ ((a + b) ^ 2 / (4 * a * b)) * (x ⬝ᵥ x) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hM := Matrix.le_iff.mp (add_smul_inv_le_smul_one_of_sandwich hA ha hlo hhi)
  have hm := hM.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hm
  have hs : 0 ≤ quadForm A x := by simpa only [quadForm, star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg x
  have ht : 0 ≤ quadForm A⁻¹ x := by simpa only [quadForm, star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg x
  change 0 ≤ (a + b) * (x ⬝ᵥ x) - (quadForm A x + a * b * quadForm A⁻¹ x) at hm
  have hsum : 0 ≤ quadForm A x + a * b * quadForm A⁻¹ x := by positivity
  have hsq := mul_self_le_mul_self hsum (sub_nonneg.mp hm)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 4 * a * b by positivity)).mpr
  nlinarith [sq_nonneg (quadForm A x - a * b * quadForm A⁻¹ x)]

end NLAlib
