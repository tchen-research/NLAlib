import NLAlib.Matrix.Spectral.DefiniteCongruence
import NLAlib.Matrix.Spectral.CourantFischer
import NLAlib.Matrix.OperatorTheory.LoewnerHeinz
/-!
# Relative spectrum and Loewner order

Whitening a definite pair identifies Loewner sandwiches with intervals
containing the actual relative spectrum. Source: Horn--Johnson (2013),
Theorem 7.7.3 and Corollary 7.7.4; atlas `loewner-relative-spectrum`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Invertible congruence preserves and reflects real matrix Loewner order.
Horn--Johnson (2013), Section 7.7; helper for relative-spectrum bounds. -/
theorem congruence_le_congruence_iff {A B S : Matrix n n ℝ} (hS : IsUnit S) :
    S * A * Sᵀ ≤ S * B * Sᵀ ↔ A ≤ B := by
  rw [Matrix.le_iff, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.le_iff]
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hS.posSemidef_star_right_conjugate_iff (x := B - A)

/-- The lower relative Loewner bound is exactly a lower bound on each
relative eigenvalue. Horn--Johnson (2013), Theorem 7.7.3.
atlas: loewner-relative-spectrum (partial) -/
theorem smul_le_iff_relative_spectrum_lower {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) (a : ℝ) :
    a • A ≤ B ↔ ∀ z ∈ spectrum ℝ (A⁻¹ * B), a ≤ z := by
  obtain ⟨S, d, hS, hAA, hBB, -⟩ := exists_definite_pair_congruence_diagonal hA hB
  have hsc : a • A = S * (a • (1 : Matrix n n ℝ)) * Sᵀ := by
    simp only [hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB, hsc, hBB,
    congruence_le_congruence_iff hS, Matrix.le_iff, Matrix.smul_one_eq_diagonal,
    Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  simp only [sub_nonneg, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- The upper relative Loewner bound is exactly an upper bound on each
relative eigenvalue. Horn--Johnson (2013), Theorem 7.7.3.
atlas: loewner-relative-spectrum (partial) -/
theorem le_smul_iff_relative_spectrum_upper {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) (b : ℝ) :
    B ≤ b • A ↔ ∀ z ∈ spectrum ℝ (A⁻¹ * B), z ≤ b := by
  obtain ⟨S, d, hS, hAA, hBB, -⟩ := exists_definite_pair_congruence_diagonal hA hB
  have hsc : b • A = S * (b • (1 : Matrix n n ℝ)) * Sᵀ := by
    simp only [hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB, hsc, hBB,
    congruence_le_congruence_iff hS, Matrix.le_iff, Matrix.smul_one_eq_diagonal,
    Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  simp only [sub_nonneg, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- A Loewner sandwich is equivalent to containment of the relative spectrum
in the same real interval. Endpoints are arbitrary and empty dimensions are
included. Horn--Johnson (2013), Theorem 7.7.3.
atlas: loewner-relative-spectrum (partial) -/
theorem loewner_sandwich_iff_relative_spectrum_subset {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) (a b : ℝ) :
    (a • A ≤ B ∧ B ≤ b • A) ↔ spectrum ℝ (A⁻¹ * B) ⊆ Set.Icc a b := by
  rw [smul_le_iff_relative_spectrum_lower hA hB, le_smul_iff_relative_spectrum_upper hA hB]
  simp only [Set.subset_def, Set.mem_Icc]
  aesop

/-- Under PSD comparison with a positive definite first matrix, the relative
spectral radius is at most one exactly when the smaller matrix is below the
first matrix in Loewner order. The radius is Mathlib's actual supremum of
the absolute real spectrum, including empty dimensions.
Horn--Johnson (2013), Corollary 7.7.4.
atlas: loewner-relative-spectrum (partial) -/
theorem le_iff_relative_spectralRadius_le_one {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    B ≤ A ↔ spectralRadius ℝ (A⁻¹ * B) ≤ 1 := by
  have hn := spectrum_inverse_mul_subset_nonneg_of_posDef hA hB
  have h := le_smul_iff_relative_spectrum_upper hA hB.isHermitian 1
  rw [one_smul] at h
  rw [h, spectralRadius, iSup₂_le_iff]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  have hz0 : 0 ≤ z := hn hz
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) from rfl, ENNReal.coe_le_coe]
  simp only [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs,
    abs_of_nonneg hz0]

/-- A positive definite matrix dominates `B` exactly when `B` is its square
root congruence of a PSD contraction. Horn--Johnson (2013), Corollary 7.7.4.
atlas: loewner-relative-spectrum (partial) -/
theorem le_iff_exists_sqrt_congruence_contraction {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    B ≤ A ↔ ∃ X : Matrix n n ℝ, 0 ≤ X ∧ X ≤ 1 ∧
      B = CFC.sqrt A * X * CFC.sqrt A := by
  let R := CFC.sqrt A
  have hR : IsUnit R := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hRit : R⁻¹ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRt]
  have hRd := (Matrix.isUnit_iff_isUnit_det R).mp hR
  have hRRi := Matrix.mul_nonsing_inv R hRd
  have hRiR := Matrix.nonsing_inv_mul R hRd
  have hSq : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hBX : R * (R⁻¹ * B * R⁻¹) * R = B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R⁻¹, hRRi, Matrix.one_mul, hRiR, Matrix.mul_one]
  constructor
  · intro hBA
    refine ⟨R⁻¹ * B * R⁻¹, ?_, ?_, hBX.symm⟩
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hRit] using
        (hB.mul_mul_conjTranspose_same R⁻¹).nonneg
    · apply (congruence_le_congruence_iff hR).mp
      simpa only [hRt, hBX, Matrix.mul_one, hSq] using hBA
  · rintro ⟨X, -, hX, hXB⟩
    have h := (congruence_le_congruence_iff hR).mpr hX
    change B = R * X * R at hXB
    simpa only [hRt, ← hXB, Matrix.mul_one, hSq] using h

omit [DecidableEq n] in
/-- Matrix trace is monotone in Loewner order, with equality only for equal
matrices. Horn--Johnson (2013), Corollary 7.7.4.
atlas: loewner-relative-spectrum (partial) -/
theorem trace_le_and_eq_iff_of_le {A B : Matrix n n ℝ} (hAB : A ≤ B) :
    A.trace ≤ B.trace ∧ (A.trace = B.trace ↔ A = B) := by
  have h := Matrix.le_iff.mp hAB
  constructor
  · simpa only [Matrix.trace_sub, sub_nonneg] using h.trace_nonneg
  · have hz := h.trace_eq_zero_iff
    simpa only [Matrix.trace_sub, sub_eq_zero, eq_comm] using hz

/-- Determinant is monotone on the PSD cone. Horn--Johnson (2013),
Corollary 7.7.4; arbitrary finite indices and singular matrices are included.
atlas: loewner-relative-spectrum (partial) -/
theorem det_le_det_of_posSemidef_le {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hAB : A ≤ B) : A.det ≤ B.det := by
  have hB := (hA.nonneg.trans hAB).posSemidef
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hB.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_le_prod
  · intro i _; exact hA.eigenvalues_nonneg i
  · intro i _
    exact eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub hA.isHermitian hB.isHermitian
      (Matrix.le_iff.mp hAB) _

/-- For a real PSD matrix, being bounded above by identity is equivalent to
operator norm at most one. Empty dimensions are included. Horn--Johnson
(2013), Section 7.7; helper for relative spectra and PSD blocks. -/
theorem le_one_iff_specNorm_le_one_of_posSemidef {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : A ≤ 1 ↔ specNorm A ≤ 1 := by
  let U : Matrix n n ℝ := hA.isHermitian.eigenvectorUnitary
  have hUt : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA.isHermitian
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hUt
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_left_inverse hUt)
  have hAU : A = U * diagonal hA.isHermitian.eigenvalues * Uᵀ :=
    eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA.isHermitian
  have hnorm : specNorm A = ‖hA.isHermitian.eigenvalues‖ := by
    calc
      specNorm A = specNorm (U * diagonal hA.isHermitian.eigenvalues * Uᵀ) := congrArg specNorm hAU
      _ = ‖hA.isHermitian.eigenvalues‖ := by
        rw [specNorm_mul_transpose_right_of_hasOrthonormalCols hUt,
          specNorm_mul_left_of_hasOrthonormalCols hUt, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  have hord : A ≤ 1 ↔ diagonal hA.isHermitian.eigenvalues ≤ 1 := by
    calc
      A ≤ 1 ↔ U * diagonal hA.isHermitian.eigenvalues * Uᵀ ≤ U * 1 * Uᵀ := by
        rw [Matrix.mul_one, hUU, ← hAU]
      _ ↔ diagonal hA.isHermitian.eigenvalues ≤ 1 := congruence_le_congruence_iff hUu
  rw [hord, hnorm, Matrix.le_iff, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.posSemidef_diagonal_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [sub_nonneg, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg _)]

/-- A real row Gram matrix is bounded by identity exactly when its matrix
is a contraction in spectral norm. Horn--Johnson (2013), Lemma 7.7.6;
helper for relative spectra and PSD blocks. -/
theorem mul_transpose_le_one_iff_specNorm_le_one {m : Type*} [Fintype m]
    [DecidableEq m] (M : Matrix n m ℝ) :
    M * Mᵀ ≤ 1 ↔ specNorm M ≤ 1 := by
  have hM : (M * Mᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose M
  rw [le_one_iff_specNorm_le_one_of_posSemidef hM,
    ← Matrix.conjTranspose_eq_transpose_of_trivial M, specNorm_mul_conjTranspose_self]
  exact sq_le_one_iff₀ (specNorm_nonneg M)

/-- A square comparison of symmetric matrices is equivalent to a relative
operator norm bound. The second matrix need not be PSD.
Horn--Johnson (2013), Corollary 7.7.4.
atlas: loewner-relative-spectrum (partial) -/
theorem sq_le_sq_iff_relative_specNorm_le_one {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    B ^ 2 ≤ A ^ 2 ↔ specNorm (A⁻¹ * B) ≤ 1 := by
  have hAt : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hBt : Bᵀ = B := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.eq
  have hAit : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hAt]
  have hAd := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAAi := Matrix.mul_nonsing_inv A hAd
  have hAiA := Matrix.nonsing_inv_mul A hAd
  have hGram : A * ((A⁻¹ * B) * (A⁻¹ * B)ᵀ) * Aᵀ = B * B := by
    rw [Matrix.transpose_mul, hBt, hAit, hAt]
    calc
      A * (A⁻¹ * B * (B * A⁻¹)) * A = (A * A⁻¹) * (B * B) * (A⁻¹ * A) := by
        simp only [Matrix.mul_assoc]
      _ = B * B := by rw [hAAi, hAiA, Matrix.one_mul, Matrix.mul_one]
  rw [← mul_transpose_le_one_iff_specNorm_le_one]
  calc
    B ^ 2 ≤ A ^ 2 ↔
        A * ((A⁻¹ * B) * (A⁻¹ * B)ᵀ) * Aᵀ ≤ A * 1 * Aᵀ := by
      rw [hGram, Matrix.mul_one, hAt, sq, sq]
    _ ↔ _ := congruence_le_congruence_iff hA.isUnit

/-- Real matrix complexification preserves the positive square root.
Uniqueness proves the bridge without a complex norm assumption.
Horn--Johnson (2013), Section 7.2; helper for relative-spectrum monotonicity. -/
theorem realMatrixComplexification_sqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    realMatrixComplexification (CFC.sqrt A) = CFC.sqrt (realMatrixComplexification A) := by
  symm
  apply CFC.sqrt_unique _
    ((posSemidef_realMatrixComplexification_iff _).mpr (CFC.sqrt_nonneg A).posSemidef).nonneg
  rw [← map_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]

/-- Square roots preserve Loewner order for real PSD matrices, including
singular matrices. Horn--Johnson (2013), Corollary 7.7.4.
atlas: loewner-relative-spectrum (partial) -/
theorem sqrt_le_sqrt_of_posSemidef_le {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hAB : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  have hB := (hA.nonneg.trans hAB).posSemidef
  apply (realMatrixComplexification_le_iff _ _).mp
  rw [realMatrixComplexification_sqrt hA, realMatrixComplexification_sqrt hB]
  exact CFC.sqrt_le_sqrt _ _ ((realMatrixComplexification_le_iff _ _).mpr hAB)

/-- Under PSD comparison with a positive definite larger matrix, determinant
equality forces equality of the matrices. The positive-definite requirement
on the larger matrix is essential. Horn--Johnson (2013), Corollary 7.7.4.
atlas: loewner-relative-spectrum (partial) -/
theorem det_eq_iff_eq_of_posSemidef_le_posDef {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) (hBA : B ≤ A) :
    B.det = A.det ↔ B = A := by
  constructor
  · intro hdet
    obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_definite_pair_congruence_diagonal hA hB.isHermitian
    have hs : S.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero
    have hp : ∏ i, d i = 1 := by
      apply mul_left_cancel₀ hs
      apply mul_right_cancel₀ hs
      simpa only [hAA, hBB, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
        mul_one] using hdet
    have hd1 : ∀ i, d i ≤ 1 := by
      have hupper := (le_smul_iff_relative_spectrum_upper hA hB.isHermitian 1).mp
        (by simpa using hBA)
      rw [spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB] at hupper
      exact fun i => hupper (d i) ⟨i, rfl⟩
    let e : n → NNReal := fun i => ⟨d i, hd hB i⟩
    have he : ∏ i, e i = 1 := by
      apply Subtype.ext
      change ((∏ i, e i : NNReal) : ℝ) = (1 : ℝ)
      rw [NNReal.coe_prod]
      exact hp
    have he1 : ∀ i, e i = 1 := by
      simpa only [Finset.mem_univ, forall_true_left] using
        (Finset.prod_eq_one_iff_of_le_one' (fun i _ => show e i ≤ 1 from hd1 i)).mp he
    have hd' : d = fun _ => 1 := by
      funext i
      exact congrArg Subtype.val (he1 i)
    rw [hBB, hd', Matrix.diagonal_one, Matrix.mul_one, ← hAA]
  · rintro rfl; rfl

/-- Complete relative-spectrum and monotonicity contract for a positive
definite real first matrix and PSD second matrix, with arbitrary interval
endpoints. Includes square comparison, trace and determinant equality,
all sorted eigenvalues, square roots, and inverse order when the smaller
matrix is positive definite. Horn--Johnson (2013), Theorem 7.7.3 and
Corollary 7.7.4; the indefinite sandwich variant is the separate theorem
`loewner_sandwich_iff_relative_spectrum_subset`.
atlas: loewner-relative-spectrum -/
theorem relative_spectrum_characterizations {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) (a b : ℝ) :
    ((a • A ≤ B ∧ B ≤ b • A) ↔ spectrum ℝ (A⁻¹ * B) ⊆ Set.Icc a b) ∧
    (B ≤ A ↔ spectralRadius ℝ (A⁻¹ * B) ≤ 1) ∧
    (B ≤ A ↔ ∃ X : Matrix n n ℝ, 0 ≤ X ∧ X ≤ 1 ∧
      B = CFC.sqrt A * X * CFC.sqrt A) ∧
    (B ^ 2 ≤ A ^ 2 ↔ specNorm (A⁻¹ * B) ≤ 1) ∧
    (B ≤ A → B.det ≤ A.det ∧ (B.det = A.det ↔ B = A) ∧
      B.trace ≤ A.trace ∧ (B.trace = A.trace ↔ B = A) ∧
      (∀ k, hB.isHermitian.eigenvalues₀ k ≤ hA.isHermitian.eigenvalues₀ k) ∧
      CFC.sqrt B ≤ CFC.sqrt A ∧ (B.PosDef → A⁻¹ ≤ B⁻¹)) := by
  refine ⟨loewner_sandwich_iff_relative_spectrum_subset hA hB.isHermitian a b,
    le_iff_relative_spectralRadius_le_one hA hB,
    le_iff_exists_sqrt_congruence_contraction hA hB,
    sq_le_sq_iff_relative_specNorm_le_one hA hB.isHermitian, fun hBA => ?_⟩
  have ht := trace_le_and_eq_iff_of_le hBA
  exact ⟨det_le_det_of_posSemidef_le hB hBA, det_eq_iff_eq_of_posSemidef_le_posDef hA hB hBA,
    ht.1, ht.2, eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub hB.isHermitian hA.isHermitian
      (Matrix.le_iff.mp hBA), sqrt_le_sqrt_of_posSemidef_le hB hBA,
    fun hBPD => inv_le_inv_of_posDef hBPD hBA⟩

end NLAlib
