import NLAlib.Matrix.Structured.RadauCornerFormula
import NLAlib.Matrix.Structured.LobattoSchurBorder

/-! # Monic resolvent formulas for the actual Lobatto border

The positive Schur definition equals the classical last-coordinate characteristic
ratios. Nonsingular endpoint shifts are explicit, so no endpoint division is hidden.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix

namespace NLAlib

/-- The actual Lobatto coupling and common corner have the classical monic
characteristic-ratio formulas, with `r(z)=χ_leading(z)/χ(z)`.
Source: operator derivations (AQ8); focused reroutes, Section 3 (BL8).
atlas: gauss-radau-lobatto (partial) -/
theorem lobattoCouplingSq_and_corner_single_last_eq_charpoly_ratio {q : ℕ}
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (a c : ℝ)
    (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef) :
    let e : Fin (q + 1) → ℝ := Pi.single (Fin.last q) 1
    let r := fun z => (J.submatrix Fin.castSucc Fin.castSucc).charpoly.eval z / J.charpoly.eval z
    lobattoCouplingSq J e a c = (c - a) / (r c - r a) ∧
      lobattoCorner J e a c = a - lobattoCouplingSq J e a c * r a ∧
      lobattoCorner J e a c = c - lobattoCouplingSq J e a c * r c := by
  dsimp only
  let e : Fin (q + 1) → ℝ := Pi.single (Fin.last q) 1
  let r := fun z => (J.submatrix Fin.castSucc Fin.castSucc).charpoly.eval z / J.charpoly.eval z
  have hunit : IsUnit (a • 1 - J) := by
    rw [← neg_sub J (a • 1)]
    exact hJa.isUnit.neg
  have hqa : quadForm (J - a • 1)⁻¹ e = -r a := by
    have h := leftRadauCorner_single_last_eq_charpoly_ratio J 1 a hunit
    simp only [leftRadauCorner, one_pow, one_mul] at h
    dsimp only [e, r]
    linarith
  have hqc : quadForm (c • 1 - J)⁻¹ e = r c := by
    rw [quadForm_single, one_pow, one_mul, resolvent_last_last_eq_charpoly_leading_div_charpoly]
  have he : e ≠ 0 := by intro hz; have h := congrFun hz (Fin.last q); simp [e] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [lobattoCouplingSq, hqa, hqc]
    congr 1
    ring
  · rw [lobattoCorner, hqa]
    ring
  · rw [lobattoCorner_eq_right hJa hJc he, hqc]

end NLAlib
