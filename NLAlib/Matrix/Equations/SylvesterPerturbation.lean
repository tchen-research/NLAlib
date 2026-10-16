import NLAlib.Matrix.Equations.SylvesterSeparation

/-! # Perturbations of the actual Sylvester operator -/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Coefficient perturbations change the Frobenius operator by at most the
sum of their spectral norms. -/
theorem frobNorm_sylvester_perturbation_le (dA : Matrix m m K) (dB : Matrix n n K)
    (X : Matrix m n K) :
    frobNorm (dA * X - X * dB) ≤ (specNorm dA + specNorm dB) * frobNorm X := by
  calc
    _ ≤ frobNorm (dA * X) + frobNorm (X * dB) := frobNorm_sub_le _ _
    _ ≤ specNorm dA * frobNorm X + frobNorm X * specNorm dB :=
      add_le_add (frobNorm_mul_le_specNorm_mul_frobNorm _ _) (frobNorm_mul_le_frobNorm_mul_specNorm _ _)
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- The genuine perturbed operator retains the lower expansion margin. -/
theorem sub_norms_mul_frobNorm_le_sylvester_perturbed (A dA : Matrix m m K)
    (B dB : Matrix n n K) (X : Matrix m n K) :
    (sylvesterSep A B - (specNorm dA + specNorm dB)) * frobNorm X ≤
      frobNorm ((A + dA) * X - X * (B + dB)) := by
  have h0 := sylvesterSep_mul_frobNorm_le A B X
  have hpert := frobNorm_sylvester_perturbation_le dA dB X
  have he : A * X - X * B = ((A + dA) * X - X * (B + dB)) - (dA * X - X * dB) := by
    simp only [Matrix.add_mul, Matrix.mul_add]; abel
  have htri := frobNorm_sub_le ((A + dA) * X - X * (B + dB)) (dA * X - X * dB)
  rw [← he] at htri
  nlinarith

open scoped Matrix.Norms.L2Operator in
/-- Separation decreases by at most the coefficient perturbation budget. -/
theorem sylvesterSep_perturbed_ge [Nonempty m] [Nonempty n] (A dA : Matrix m m K)
    (B dB : Matrix n n K) :
    sylvesterSep A B - (specNorm dA + specNorm dB) ≤ sylvesterSep (A + dA) (B + dB) := by
  obtain ⟨X, hX, hS⟩ := exists_frobNorm_one_sylvester_eq_sep (A + dA) (B + dB)
  simpa only [hX, mul_one, hS] using sub_norms_mul_frobNorm_le_sylvester_perturbed A dA B dB X

open scoped Matrix.Norms.L2Operator in
/-- A strictly positive separation margin proves existence and uniqueness
for every perturbed right-hand side, without a spectral or normality surrogate. -/
theorem existsUnique_sylvester_of_perturbation_margin [Nonempty m] [Nonempty n]
    (A dA : Matrix m m K) (B dB : Matrix n n K) (C : Matrix m n K)
    (hmargin : specNorm dA + specNorm dB < sylvesterSep A B) :
    ∃! X : Matrix m n K, (A + dA) * X - X * (B + dB) = C := by
  have hsep : 0 < sylvesterSep (A + dA) (B + dB) :=
    lt_of_lt_of_le (sub_pos.mpr hmargin) (sylvesterSep_perturbed_ge A dA B dB)
  have hinj := (sylvesterSep_pos_iff_injective (A + dA) (B + dB)).mp hsep
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hinj) C
  exact ⟨X, hX, fun Y hY => hinj (hY.trans hX.symm)⟩

open scoped Matrix.Norms.L2Operator in
/-- The full coefficient/right-hand-side perturbation estimate with the exact
separation denominator. Source: user derivations, Sylvester perturbation bound.
atlas: sylvester-separation-residual-conditioning (partial) -/
theorem frobNorm_sylvester_solution_perturbation_le (A dA : Matrix m m K)
    (B dB : Matrix n n K) (C dC X Xnew : Matrix m n K)
    (hmargin : specNorm dA + specNorm dB < sylvesterSep A B)
    (hX : A * X - X * B = C)
    (hXnew : (A + dA) * Xnew - Xnew * (B + dB) = C + dC) :
    frobNorm (Xnew - X) ≤
      (frobNorm dC + (specNorm dA + specNorm dB) * frobNorm X) /
        (sylvesterSep A B - (specNorm dA + specNorm dB)) := by
  apply (le_div_iff₀ (sub_pos.mpr hmargin)).mpr
  rw [mul_comm]
  have hlow := sub_norms_mul_frobNorm_le_sylvester_perturbed A dA B dB (Xnew - X)
  have he : (A + dA) * (Xnew - X) - (Xnew - X) * (B + dB) = dC - (dA * X - X * dB) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    have hnew : (A + dA) * X = C + X * B + dA * X := by
      rw [Matrix.add_mul, ← hX]; abel
    rw [hnew, Matrix.mul_add]
    have hfirst : (A + dA) * Xnew = C + dC + Xnew * (B + dB) :=
      sub_eq_iff_eq_add.mp hXnew
    rw [hfirst]
    simp only [Matrix.mul_add]
    abel
  rw [he] at hlow
  exact hlow.trans ((frobNorm_sub_le _ _).trans
    (add_le_add le_rfl (frobNorm_sylvester_perturbation_le dA dB X)))

end NLAlib
