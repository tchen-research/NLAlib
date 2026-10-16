import NLAlib.Matrix.Functions.PositiveMapSpectral

/-!
# Inverse Jensen inequality for positive unital maps

The same spectral block construction as Kadison's inequality, with scalar
coefficients `sqrt λ` and `1/sqrt λ`, proves Choi's inverse inequality.
Strict positivity of the image follows from an actual positive scalar gap.
Tropp (2022), Theorem 12.19. Atlas: `positive-map-inverse-jensen`.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [Fintype m] in
/-- A positive unital map preserves positive definiteness in finite dimensions. -/
theorem posDef_map_of_positive_unital
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (hΦ : Φ 1 = 1)
    {A : Matrix n n ℂ} (hA : A.PosDef) : (Φ A).PosDef := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hA1 : A = 1 := Subsingleton.elim _ _
    rw [hA1, hΦ]
    exact Matrix.PosDef.one
  | inr hn =>
    obtain ⟨c, hc, hcA⟩ :=
      (CFC.exists_pos_algebraMap_le_iff hA.isHermitian.isSelfAdjoint).mpr
        (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
    have hgap := Φ.monotone hcA
    have hmap : Φ (algebraMap ℝ (Matrix n n ℂ) c) =
        c • (1 : Matrix m m ℂ) := by
      simp only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, hΦ]
    change Φ (algebraMap ℝ (Matrix n n ℂ) c) ≤ Φ A at hgap
    rw [hmap] at hgap
    have hp := (Matrix.PosDef.one.smul hc).add_posSemidef (Matrix.le_iff.mp hgap)
    simpa only [add_sub_cancel] using hp

/-- Positive scalar reciprocal blocks are positive after tensoring by a PSD matrix. -/
theorem posSemidef_reciprocal_fromBlocks {B : Matrix m m ℂ}
    (hB : B.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (fromBlocks ((t : ℂ) • B) B B ((t : ℂ)⁻¹ • B)).PosSemidef := by
  let a : ℂ := Real.sqrt t
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have haa : a * a = (t : ℂ) := by
    dsimp [a]
    exact_mod_cast Real.mul_self_sqrt ht.le
  have hstar : star a = a := by simp [a]
  have hstari : star (a⁻¹) = a⁻¹ := by simp [a]
  have hi : a⁻¹ * a⁻¹ = (t : ℂ)⁻¹ := by rw [← _root_.mul_inv_rev, haa]
  simpa only [hstar, hstari, haa, hi, mul_inv_cancel₀ ha,
    inv_mul_cancel₀ ha, one_smul] using posSemidef_scalar_gram_fromBlocks hB a a⁻¹

/-- A Hermitian invertible matrix has the reciprocal spectral expansion. -/
theorem inv_eq_sum_inv_eigenvalue_smul_unitarySpectralProjector
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hu : IsUnit A) :
    A⁻¹ = ∑ i, (hA.eigenvalues i : ℂ)⁻¹ •
      unitarySpectralProjector hA.eigenvectorUnitary i := by
  calc
    A⁻¹ = Ring.inverse A := Matrix.nonsing_inv_eq_ringInverse A
    _ = cfc (fun x : ℝ => x⁻¹) A :=
      (cfc_ringInverse_id (R := ℝ) A hu hA).symm
    _ = _ := by
      rw [cfc_eq_sum_smul_unitarySpectralProjector hA]
      simp only [Complex.ofReal_inv]

/-- Positive unital complex-linear maps preserve positive definiteness and
satisfy the inverse Jensen inequality. Tropp (2022), Theorem 12.19.
atlas: positive-map-inverse-jensen -/
theorem posDef_map_and_inv_le_map_inv
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (hΦ : Φ 1 = 1)
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    (Φ A).PosDef ∧ (Φ A)⁻¹ ≤ Φ A⁻¹ := by
  have hΦA := posDef_map_of_positive_unital Φ hΦ hA
  refine ⟨hΦA, ?_⟩
  let P := unitarySpectralProjector hA.isHermitian.eigenvectorUnitary
  let B : n → Matrix m m ℂ := fun i => Φ (P i)
  let ev : n → ℝ := hA.isHermitian.eigenvalues
  have hB (i : n) : (B i).PosSemidef := posSemidef_map_unitarySpectralProjector Φ _ i
  have hsum : ∑ i, B i = 1 := by
    dsimp [B, P]
    rw [← map_sum, sum_unitarySpectralProjector, hΦ]
  have hfirst : ∑ i, (ev i : ℂ) • B i = Φ A := by
    rw [sum_eigenvalue_smul_unitarySpectralProjector hA.isHermitian, map_sum]
    simp only [map_smul]
    rfl
  have hsecond : ∑ i, (ev i : ℂ)⁻¹ • B i = Φ A⁻¹ := by
    rw [inv_eq_sum_inv_eigenvalue_smul_unitarySpectralProjector hA.isHermitian hA.isUnit,
      map_sum]
    simp only [map_smul]
    rfl
  have hblocks (i : n) :
      (fromBlocks ((ev i : ℂ) • B i) (B i) (B i) ((ev i : ℂ)⁻¹ • B i)).PosSemidef :=
    posSemidef_reciprocal_fromBlocks (hB i) (hA.eigenvalues_pos i)
  have hH := Matrix.posSemidef_sum Finset.univ (fun i _ => hblocks i)
  have heq : (∑ i, fromBlocks ((ev i : ℂ) • B i) (B i) (B i)
      ((ev i : ℂ)⁻¹ • B i)) =
      fromBlocks (∑ i, (ev i : ℂ) • B i) (∑ i, B i) (∑ i, B i)
        (∑ i, (ev i : ℂ)⁻¹ • B i) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.sum_apply, fromBlocks]
  rw [heq, hsum, hfirst, hsecond] at hH
  let : Invertible (Φ A) := hΦA.isUnit.invertible
  have h := (Matrix.PosDef.fromBlocks₁₁ (1 : Matrix m m ℂ) (Φ A⁻¹) hΦA).mp
    (by simpa only [Matrix.conjTranspose_one] using hH)
  exact Matrix.le_iff.mpr (by simpa only [Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one] using h)

end NLAlib
