import NLAlib.Matrix.Functions.SteinConvergence
import NLAlib.Matrix.Spectral.Complexification

/-! # Real Stein stability and actual Gramian transport -/
noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complexification commutes with the actual convergent real Stein series. -/
theorem realMatrixComplexification_steinGramian (A Q : Matrix n n ℝ)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (realMatrixComplexification (steinGramian A Q) : Matrix n n ℂ) =
      steinGramian (realMatrixComplexification A) (realMatrixComplexification Q) := by
  let F := (realMatrixComplexification (n := n) (𝕜 := ℂ)).toLinearMap.toContinuousLinearMap
  have h := F.map_tsum hs
  change realMatrixComplexification (steinGramian A Q) = _ at h
  rw [h]
  congr 1
  funext j
  change realMatrixComplexification (A ^ j * Q * (Aᴴ) ^ j) = _
  simp only [map_mul, map_pow]
  have hstar : (realMatrixComplexification Aᴴ : Matrix n n ℂ) =
      (realMatrixComplexification A)ᴴ := map_star realMatrixComplexification A
  rw [hstar]

/-- Discrete stability of a real matrix is equivalent to a strict real
positive definite Stein certificate, using its genuine complexified spectrum.
Source: user derivations, Stein stability equivalence.
atlas: stein-gramian-smith-doubling -/
theorem complex_spectralRadius_lt_one_iff_exists_real_posDef_stein (A : Matrix n n ℝ) :
    spectralRadius ℂ (A.map Complex.ofReal) < 1 ↔
      ∃ X : Matrix n n ℝ, X.PosDef ∧ (X - A * X * Aᴴ).PosDef := by
  constructor
  · intro hA
    have hs := summable_real_stein_of_complex_spectralRadius_lt_one A 1 hA
    refine ⟨steinGramian A 1, posDef_steinGramian A 1 Matrix.PosDef.one hs, ?_⟩
    rw [steinGramian_sub_mul_mul_conjTranspose A 1 hs]
    exact Matrix.PosDef.one
  · rintro ⟨X, hX, hR⟩
    apply (spectralRadius_lt_one_iff_exists_posDef_stein (A.map Complex.ofReal)).mpr
    refine ⟨realMatrixComplexification X, posDef_realMatrixComplexification hX, ?_⟩
    have hc := posDef_realMatrixComplexification (𝕜 := ℂ) hR
    have hstar : (realMatrixComplexification Aᴴ : Matrix n n ℂ) =
        (realMatrixComplexification A)ᴴ := map_star realMatrixComplexification A
    simp only [map_sub, map_mul, hstar] at hc
    exact hc

end NLAlib
