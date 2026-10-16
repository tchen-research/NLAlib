import NLAlib.Matrix.Nonnegative.MMatrixSpectral
import NLAlib.Matrix.Nonnegative.MMatrixPrincipal
import NLAlib.Matrix.Spectral.PrincipalMinorPSD
import Mathlib.Topology.Order.IntermediateValue

/-! # Positive principal minors characterize nonsingular M-matrices

A positive-vector homotopy to the identity keeps the determinant nonzero,
so its sign is positive. Conversely, positive principal minors give
nonnegative degree-dependent signed characteristic coefficients. These
exclude every negative real root, including the shifted Perron eigenvalue;
the positive full determinant excludes zero.
Source: Berman–Plemmons, Nonnegative Matrices, Chapter 6.
-/

noncomputable section
open Matrix Finset
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonsingular M-matrix has strictly positive determinant. The proof
includes dimension zero, where the determinant is one.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsNonsingularMMatrix.det_pos {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix) :
    0 < A.det := by
  obtain ⟨x, hx, hAx⟩ := hA.exists_positive_certificate
  let T : ℝ → Matrix ι ι ℝ := fun t => (1 - t) • 1 + t • A
  have hTunit (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsUnit (T t) := by
    have hTZ : (T t).IsZMatrix := by
      intro i j hij
      simpa only [T, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij, if_false,
        smul_eq_mul, mul_zero, zero_add] using mul_nonpos_of_nonneg_of_nonpos ht.1 (hA.1 i j hij)
    apply (hTZ.isNonsingularMMatrix_of_positive_certificate hx (fun i => ?_)).2.1
    have he : (T t *ᵥ x) i = (1 - t) * x i + t * (A *ᵥ x) i := by
      change (((1 - t) • (1 : Matrix ι ι ℝ) + t • A) *ᵥ x) i = _
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rfl
    rw [he]
    by_cases ht0 : t = 0
    · simp only [ht0, sub_zero, one_mul, zero_mul, add_zero]
      exact hx i
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hx i).le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (hAx i))
  have hdet (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (T t).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (hTunit t ht)).ne_zero
  have hc : Continuous (fun t => (T t).det) := by fun_prop
  by_contra! hle
  have hzero : (0 : ℝ) ∈ Set.Icc ((T 1).det) ((T 0).det) := by
    change (T 1).det ≤ 0 ∧ 0 ≤ (T 0).det
    simpa only [T, sub_self, zero_smul, one_smul, zero_add, sub_zero, add_zero,
      Matrix.det_one] using And.intro hle zero_le_one
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' zero_le_one hc.continuousOn hzero
  exact hdet t ht hz

/-- Every principal minor of a nonsingular M-matrix is strictly positive,
including the empty principal minor, whose value is one.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsNonsingularMMatrix.principal_minor_pos {A : Matrix ι ι ℝ}
    (hA : A.IsNonsingularMMatrix) (S : Finset ι) :
    0 < (A.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).det :=
  (hA.submatrix _ Subtype.val_injective).det_pos

variable [Nonempty ι]

/-- Strict positivity of all principal minors characterizes a nonsingular
M-matrix among Z-matrices. Quantifying the empty minor is harmless: it equals one.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem isNonsingularMMatrix_iff_principal_minors_pos {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) :
    A.IsNonsingularMMatrix ↔ ∀ S : Finset ι,
      0 < (A.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).det := by
  refine ⟨fun hM => hM.principal_minor_pos, fun hminor => ?_⟩
  have hdet : 0 < A.det := by
    let e : (Finset.univ : Finset ι) ≃ ι := Equiv.subtypeUnivEquiv (fun _ => mem_univ _)
    have h := hminor Finset.univ
    change 0 < (A.submatrix e e).det at h
    simpa only [Matrix.det_submatrix_equiv_self] using h
  have hcoeff (k : ℕ) (hk : k ≤ Fintype.card ι) :
      0 ≤ (-1 : ℝ) ^ k * A.charpoly.coeff (Fintype.card ι - k) := by
    rw [NLAlib.signed_charpoly_coeff_eq_sum_principal_minors A k hk]
    exact Finset.sum_nonneg fun S _ => (hminor S).le
  obtain ⟨s, B, _, hB, hAB⟩ := hA.exists_positive_shift_nonnegative
  obtain ⟨p, _, hs, he⟩ := exists_nonnegative_perron_eigenvector hB
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hs
  let aRoot := s - (spectralRadius ℂ (B.map Complex.ofReal)).toReal
  have hAp : A *ᵥ p = aRoot • p := by
    rw [hAB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, sub_smul]
  have hroot : A.charpoly.eval aRoot = 0 :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mp (mem_spectrum_of_mulVec_eq_smul hpne hAp)).eq_zero
  have hrootpos : 0 < aRoot := by
    by_contra! hle
    by_cases hz : aRoot = 0
    · have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet.ne')
      have hzero : A *ᵥ p = 0 := by rw [hAp, hz, zero_smul]
      exact hpne (Matrix.mulVec_injective_of_isUnit hunit (hzero.trans (Matrix.mulVec_zero _).symm))
    · have hneg : aRoot < 0 := lt_of_le_of_ne hle hz
      have hc (j : ℕ) (hj : j ≤ Fintype.card ι) :
          0 ≤ (-1 : ℝ) ^ (Fintype.card ι - j) * A.charpoly.coeff j := by
        simpa only [Nat.sub_sub_self hj] using hcoeff (Fintype.card ι - j) (Nat.sub_le _ _)
      have hpos := NLAlib.mul_eval_neg_pos_of_signed_coeff_nonneg A.charpoly_natDegree_eq_dim
        A.charpoly_monic hc (neg_pos.mpr hneg)
      simp only [neg_neg, hroot, mul_zero, lt_self_iff_false] at hpos
  exact (isNonsingularMMatrix_iff_exists_shift_above_spectralRadius hA).mpr
    ⟨s, B, hB, hAB, sub_pos.mp hrootpos⟩

end Matrix
