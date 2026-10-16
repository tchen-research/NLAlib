import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Spectral.SVD

/-!
# A complex contraction is the average of two unitaries

The construction uses the actual indexed SVD and the scalar circle points
`s ± i sqrt(1-s²)`. Tropp (2022), Proposition 12.24.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

private theorem circlePoint_mul_star (s : ℝ) (hs : |s| ≤ 1) :
    ((s : ℂ) + Complex.I * Real.sqrt (1 - s ^ 2)) *
      star ((s : ℂ) + Complex.I * Real.sqrt (1 - s ^ 2)) = 1 := by
  have ht : (Real.sqrt (1 - s ^ 2)) ^ 2 = 1 - s ^ 2 :=
    Real.sq_sqrt (by
      have hs' := abs_le.mp hs
      nlinarith [mul_nonneg (sub_nonneg.mpr hs'.2) (by linarith : 0 ≤ 1 + s)])
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Every square complex contraction is an average of two unitary matrices,
with no invertibility assumption. Tropp (2022), Proposition 12.24. -/
theorem exists_unitary_average_of_specNorm_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : specNorm A ≤ 1) :
    ∃ U V : unitary (Matrix (Fin n) (Fin n) ℂ),
      A = (2 : ℂ)⁻¹ • ((U : Matrix (Fin n) (Fin n) ℂ) + V) := by
  obtain ⟨L, R, h⟩ := exists_isSVD A
  let s (i : Fin n) : ℝ := singularValues A i
  let z (i : Fin n) : ℂ := (s i : ℂ) + Complex.I * Real.sqrt (1 - s i ^ 2)
  have hz (i : Fin n) : z i * star (z i) = 1 := circlePoint_mul_star (s i) (by
    rw [abs_of_nonneg (singularValues_nonneg A i)]
    exact (singularValues_le_specNorm A i).trans hA)
  have hd : diagonal z ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    constructor <;> ext i j <;> by_cases hij : i = j
    all_goals first
    | subst j
      simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, mul_comm] using hz i
    | simp [Matrix.star_eq_conjTranspose, hij]
  let Lu : unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨L, ⟨h.conjTranspose_mul_left, h.mul_conjTranspose_left⟩⟩
  let Ru : unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨R, ⟨h.conjTranspose_mul_right, h.mul_conjTranspose_right⟩⟩
  let Du : unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨diagonal z, hd⟩
  let U := Lu * Du * star Ru
  let V := Lu * star Du * star Ru
  refine ⟨U, V, ?_⟩
  change A = (2 : ℂ)⁻¹ • (L * diagonal z * R.conjTranspose +
    L * (diagonal z).conjTranspose * R.conjTranspose)
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  have heq : (2 : ℂ)⁻¹ • (L * (diagonal z + (diagonal z).conjTranspose) * R.conjTranspose) =
      L * ((2 : ℂ)⁻¹ • (diagonal z + (diagonal z).conjTranspose)) * R.conjTranspose := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [heq]
  rw [h.eq]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rectDiag_apply_ofReal, z]
    ring
  · simp [rectDiag_apply_ofReal, hij, Fin.val_injective.ne hij]

end NLAlib
