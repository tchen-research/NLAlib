import NLAlib.Matrix.Structured.JacobiBorderPowers
import NLAlib.Matrix.Structured.LobattoSchurBorder
import NLAlib.Matrix.Functions.CFCQuadratic

/-! # Interval location of actual scalar Jacobi borders

The Schur matrix order bounds survive the explicit contiguous finite reindexing.
Rayleigh values of normalized eigenvectors turn those order bounds into interval
location for every actual node, with the designated endpoint eigenvalues retained.
-/

noncomputable section
open Matrix Set
open scoped Matrix MatrixOrder

namespace NLAlib

/-- Matrix interval order bounds contain every eigenvalue of a real Hermitian matrix. -/
theorem _root_.Matrix.IsHermitian.eigenvalues_mem_Icc_of_order
    {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι ℝ} (hJ : J.IsHermitian)
    {a c : ℝ} (ha : a • 1 ≤ J) (hc : J ≤ c • 1) (i : ι) : hJ.eigenvalues i ∈ Icc a c := by
  let v : ι → ℝ := hJ.eigenvectorBasis i
  have hv : J *ᵥ v = hJ.eigenvalues i • v := hJ.mulVec_eigenvectorBasis i
  have hn : v ⬝ᵥ v = 1 := eigenvectorBasis_dotProduct_eigenvectorBasis hJ i i |>.trans (by simp)
  have hlo := ((Matrix.le_iff).mp ha).dotProduct_mulVec_nonneg v
  have hhi := ((Matrix.le_iff).mp hc).dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, star_trivial,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hn, mul_one, mul_one] at hlo
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, star_trivial,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hn, mul_one, mul_one] at hhi
  exact ⟨by linarith, by linarith⟩

/-- The actual finite indexed Lobatto Schur border lies in the endpoint interval and
has both designated endpoint eigenvalues. Source: focused reroutes, Section 3 (BL9).
atlas: gauss-radau-lobatto (partial) -/
theorem finLobattoSchurBorder_bounds_and_endpoints {q : ℕ}
    {J : Matrix (Fin q) (Fin q) ℝ} {e : Fin q → ℝ} {a c : ℝ}
    (hac : a < c) (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef) (he : e ≠ 0) :
    let B := finSymmetricBorder J (Real.sqrt (lobattoCouplingSq J e a c) • e) (lobattoCorner J e a c)
    a • 1 ≤ B ∧ B ≤ c • 1 ∧ a ∈ spectrum ℝ B ∧ c ∈ spectrum ℝ B := by
  dsimp only
  obtain ⟨ha, hc, hsa, hsc⟩ := lobattoSchurBorder_bounds_and_endpoints hac hJa hJc he
  have hla := reindex_le_reindex finSumFinEquiv ha
  have hlc := reindex_le_reindex finSumFinEquiv hc
  rw [reindex_smul_one] at hla hlc
  refine ⟨hla, hlc, ?_, ?_⟩
  · simpa only [finSymmetricBorder, lobattoSchurBorder, spectrum_reindex] using hsa
  · simpa only [finSymmetricBorder, lobattoSchurBorder, spectrum_reindex] using hsc

/-- The actual finite indexed Radau matrices retain the endpoint spectrum and
bracket the original finite border in matrix order. Source: focused reroutes (BL4).
atlas: gauss-radau-lobatto (partial) -/
theorem finRadauSchurBorders_bounds_and_endpoints {q : ℕ}
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d a c : ℝ)
    (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef)
    (hMa : (symmetricBorder J v d - a • 1).PosSemidef)
    (hMc : (c • 1 - symmetricBorder J v d).PosSemidef) :
    let Ra := finSymmetricBorder J v (leftRadauCorner J v a)
    let Rc := finSymmetricBorder J v (rightRadauCorner J v c)
    a • 1 ≤ Ra ∧ Ra ≤ finSymmetricBorder J v d ∧
      finSymmetricBorder J v d ≤ Rc ∧ Rc ≤ c • 1 ∧
      a ∈ spectrum ℝ Ra ∧ c ∈ spectrum ℝ Rc := by
  dsimp only
  obtain ⟨ha, haM, hMc', hc⟩ := leftRadauBorder_le_original_le_rightRadauBorder J v d a c hJa hJc hMa hMc
  have hla := reindex_le_reindex finSumFinEquiv ha
  have hlc := reindex_le_reindex finSumFinEquiv hc
  rw [reindex_smul_one] at hla hlc
  refine ⟨hla, reindex_le_reindex finSumFinEquiv haM,
    reindex_le_reindex finSumFinEquiv hMc', hlc, ?_, ?_⟩
  · have h := (leftRadauBorder_posSemidef_shift_and_mem_spectrum J v a hJa).2
    simpa only [finSymmetricBorder, spectrum_reindex] using h
  · have h := (rightRadauBorder_posSemidef_shift_and_mem_spectrum J v c hJc).2
    simpa only [finSymmetricBorder, spectrum_reindex] using h

end NLAlib
