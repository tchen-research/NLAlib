import NLAlib.Matrix.Structured.RadauSchurBorders

/-! # The actual Lobatto border from its two endpoint Schur complements

Positive definite left and right endpoint shifts determine a strictly positive coupling
square and a common corner. Both shifted actual borders have zero Schur complement,
so the two endpoints are eigenvalues and the entire matrix lies between them.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Lobatto coupling square, using the two positive endpoint resolvent forms.
It is total; positivity is established under the explicit endpoint hypotheses. -/
def lobattoCouplingSq (J : Matrix n n ℝ) (e : n → ℝ) (a c : ℝ) : ℝ :=
  (c - a) / (quadForm (J - a • 1)⁻¹ e + quadForm (c • 1 - J)⁻¹ e)

/-- The common Lobatto scalar corner determined by the left endpoint equation. -/
def lobattoCorner (J : Matrix n n ℝ) (e : n → ℝ) (a c : ℝ) : ℝ :=
  a + lobattoCouplingSq J e a c * quadForm (J - a • 1)⁻¹ e

/-- The actual two-endpoint Lobatto border with positive square-root coupling. -/
def lobattoSchurBorder (J : Matrix n n ℝ) (e : n → ℝ) (a c : ℝ) :
    Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℝ :=
  symmetricBorder J (Real.sqrt (lobattoCouplingSq J e a c) • e) (lobattoCorner J e a c)

/-- Both endpoint inverse forms are strictly positive for a nonzero border vector. -/
theorem endpoint_inverse_quadForm_pos {J : Matrix n n ℝ} {e : n → ℝ} {a c : ℝ}
    (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef) (he : e ≠ 0) :
    0 < quadForm (J - a • 1)⁻¹ e ∧ 0 < quadForm (c • 1 - J)⁻¹ e :=
  ⟨hJa.inv.quadForm_pos he, hJc.inv.quadForm_pos he⟩

/-- The actual Lobatto coupling square is positive under the exact strict endpoint
hypotheses. Source: focused mathematical reroutes, Section 3 (BL7)–(BL8).
atlas: gauss-radau-lobatto (partial) -/
theorem lobattoCouplingSq_pos {J : Matrix n n ℝ} {e : n → ℝ} {a c : ℝ}
    (hac : a < c) (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef) (he : e ≠ 0) :
    0 < lobattoCouplingSq J e a c := by
  obtain ⟨ha, hc⟩ := endpoint_inverse_quadForm_pos hJa hJc he
  exact div_pos (sub_pos.mpr hac) (add_pos ha hc)

/-- The computed Lobatto corner also satisfies the right endpoint equation.
Source: focused mathematical reroutes, Section 3 (BL8).
atlas: gauss-radau-lobatto (partial) -/
theorem lobattoCorner_eq_right {J : Matrix n n ℝ} {e : n → ℝ} {a c : ℝ}
    (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef) (he : e ≠ 0) :
    lobattoCorner J e a c = c - lobattoCouplingSq J e a c * quadForm (c • 1 - J)⁻¹ e := by
  obtain ⟨ha, hc⟩ := endpoint_inverse_quadForm_pos hJa hJc he
  have hsum : quadForm (J - a • 1)⁻¹ e + quadForm (c • 1 - J)⁻¹ e ≠ 0 := (add_pos ha hc).ne'
  dsimp only [lobattoCorner, lobattoCouplingSq]
  field_simp
  ring

/-- The actual Lobatto border has both endpoint eigenvalues and its whole spectrum
lies between the endpoints, expressed by the matrix order inequalities.
Source: focused mathematical reroutes, Section 3 (BL9).
atlas: gauss-radau-lobatto (partial) -/
theorem lobattoSchurBorder_bounds_and_endpoints {J : Matrix n n ℝ} {e : n → ℝ} {a c : ℝ}
    (hac : a < c) (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef) (he : e ≠ 0) :
    a • 1 ≤ lobattoSchurBorder J e a c ∧ lobattoSchurBorder J e a c ≤ c • 1 ∧
      a ∈ spectrum ℝ (lobattoSchurBorder J e a c) ∧
      c ∈ spectrum ℝ (lobattoSchurBorder J e a c) := by
  let v := Real.sqrt (lobattoCouplingSq J e a c) • e
  have hγ := lobattoCouplingSq_pos hac hJa hJc he
  have hqa : quadForm (J - a • 1)⁻¹ v =
      lobattoCouplingSq J e a c * quadForm (J - a • 1)⁻¹ e := by
    dsimp only [v]
    rw [quadForm_smul, star_trivial, ← pow_two, Real.sq_sqrt hγ.le]
  have hqc : quadForm (c • 1 - J)⁻¹ v =
      lobattoCouplingSq J e a c * quadForm (c • 1 - J)⁻¹ e := by
    dsimp only [v]
    rw [quadForm_smul, star_trivial, ← pow_two, Real.sq_sqrt hγ.le]
  have ha : lobattoSchurBorder J e a c = symmetricBorder J v (leftRadauCorner J v a) := by
    simp only [lobattoSchurBorder, leftRadauCorner, hqa, lobattoCorner, v]
  have hc : lobattoSchurBorder J e a c = symmetricBorder J v (rightRadauCorner J v c) := by
    rw [lobattoSchurBorder, lobattoCorner_eq_right hJa hJc he]
    simp only [rightRadauCorner, hqc, v]
  obtain ⟨hpa, hsa⟩ := leftRadauBorder_posSemidef_shift_and_mem_spectrum J v a hJa
  obtain ⟨hpc, hsc⟩ := rightRadauBorder_posSemidef_shift_and_mem_spectrum J v c hJc
  exact ⟨ha ▸ (Matrix.le_iff).mpr hpa, hc ▸ (Matrix.le_iff).mpr hpc, ha ▸ hsa, hc ▸ hsc⟩

end NLAlib
