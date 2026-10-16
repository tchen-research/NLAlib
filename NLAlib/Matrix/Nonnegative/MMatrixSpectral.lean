import NLAlib.Matrix.Nonnegative.MMatrixBasic
import NLAlib.Matrix.Nonnegative.CollatzWielandt

/-! # Spectral characterizations of nonsingular M-matrices

A Z-matrix is inverse-positive precisely when it is a shift of a nonnegative
matrix by a scalar above the Perron root, and precisely when all its complex
eigenvalues lie in the open right half-plane. Positive strict Collatz vectors
construct the converse directly. Source: Berman–Plemmons, Chapter 6.
-/

noncomputable section
open Matrix Finset
open scoped Matrix ENNReal
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
private theorem dotProduct_pos_of_nonnegative_sum_one {q x : ι → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) (hx : ∀ i, 0 < x i) : 0 < q ⬝ᵥ x := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < q j := by
    by_contra! h
    have hle := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => h j)
    rw [hs] at hle
    norm_num at hle
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hq i) (hx i).le)
    ⟨j, mem_univ j, mul_pos hj (hx j)⟩

omit [Nonempty ι] in
/-- Every Z-matrix can be written as `s I - B`, with `s > 0` and `B ≥ 0`.
The scalar is explicitly chosen above all diagonal entries. -/
theorem IsZMatrix.exists_positive_shift_nonnegative {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) :
    ∃ (s : ℝ) (B : Matrix ι ι ℝ), 0 < s ∧ (∀ i j, 0 ≤ B i j) ∧ A = s • 1 - B := by
  let s : ℝ := 1 + ∑ i, max (A i i) 0
  have hs : 0 < s := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => le_max_right _ _)
  have hsdiag (i : ι) : A i i ≤ s := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => le_max_right (A j j) 0)
      (mem_univ i)
    have hi := le_max_left (A i i) 0
    dsimp [s]
    linarith
  let B := s • (1 : Matrix ι ι ℝ) - A
  refine ⟨s, B, hs, fun i j => ?_, ?_⟩
  · by_cases hij : i = j
    · subst j
      simpa only [B, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one] using sub_nonneg.mpr (hsdiag i)
    · simpa only [B, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij, if_false,
        smul_eq_mul, mul_zero, zero_sub] using neg_nonneg.mpr (hA i j hij)
  · dsimp [B]
    abel

/-- The shift-above-Perron-root characterization of nonsingular M-matrices.
The spectral radius is explicitly that of the complexification.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem isNonsingularMMatrix_iff_exists_shift_above_spectralRadius
    {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) : A.IsNonsingularMMatrix ↔
      ∃ (s : ℝ) (B : Matrix ι ι ℝ), (∀ i j, 0 ≤ B i j) ∧
        A = s • 1 - B ∧ (spectralRadius ℂ (B.map Complex.ofReal)).toReal < s := by
  constructor
  · intro hM
    obtain ⟨s, B, _, hB, hAB⟩ := hA.exists_positive_shift_nonnegative
    obtain ⟨x, hx, hAx⟩ := hM.exists_positive_certificate
    obtain ⟨_, q, _, hq, _, hqs, _, hqB⟩ := exists_nonnegative_perron_pair hB
    have hqx := dotProduct_pos_of_nonnegative_sum_one hq hqs hx
    have hqAx := dotProduct_pos_of_nonnegative_sum_one hq hqs hAx
    have heq : q ⬝ᵥ (A *ᵥ x) =
        (s - (spectralRadius ℂ (B.map Complex.ofReal)).toReal) * (q ⬝ᵥ x) := by
      rw [hAB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, hqB, smul_dotProduct]
      dsimp only [smul_eq_mul]
      ring
    refine ⟨s, B, hB, hAB, ?_⟩
    rw [heq] at hqAx
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hqx).mp hqAx)
  · rintro ⟨s, B, hB, hAB, hρ⟩
    obtain ⟨x, hx, hBx⟩ := exists_positive_strict_subsolution_of_spectralRadius_lt hB hρ
    apply hA.isNonsingularMMatrix_of_positive_certificate hx
    intro i
    rw [hAB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact sub_pos.mpr (hBx i)

omit [Nonempty ι] in
private theorem norm_le_spectralRadius_toReal {B : Matrix ι ι ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ B) : ‖μ‖ ≤ (spectralRadius ℂ B).toReal := by
  have hnorm : (‖μ‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ B :=
    le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)
  simpa only [ENNReal.coe_toReal, coe_nnnorm] using
    ENNReal.toReal_mono (NLAlib.matrix_spectralRadius_ne_top B) hnorm

/-- A nonsingular M-matrix has every complex eigenvalue in the open right half-plane.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsNonsingularMMatrix.re_pos_of_mem_spectrum {A : Matrix ι ι ℝ}
    (hA : A.IsNonsingularMMatrix) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A.map Complex.ofReal)) :
    0 < μ.re := by
  obtain ⟨s, B, _, hAB, hρ⟩ :=
    (isNonsingularMMatrix_iff_exists_shift_above_spectralRadius hA.1).mp hA
  obtain ⟨z, hz, hAz⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
  have hAc : A.map Complex.ofReal = (s : ℂ) • 1 - B.map Complex.ofReal := by
    rw [hAB]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hBc : B.map Complex.ofReal = (s : ℂ) • 1 - A.map Complex.ofReal := by rw [hAc]; abel
  have hBz : B.map Complex.ofReal *ᵥ z = ((s : ℂ) - μ) • z := by
    rw [hBc, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAz, sub_smul]
  have hnorm := norm_le_spectralRadius_toReal (mem_spectrum_of_mulVec_eq_smul hz hBz)
  have hre := Complex.re_le_norm ((s : ℂ) - μ)
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- For a Z-matrix, open-right-half-plane spectrum is equivalent to being a
nonsingular M-matrix. The converse tests the real Perron root of a nonnegative shift.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem isNonsingularMMatrix_iff_spectrum_re_pos {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) :
    A.IsNonsingularMMatrix ↔ ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), 0 < μ.re := by
  refine ⟨fun hM μ hμ => hM.re_pos_of_mem_spectrum hμ, fun hspec => ?_⟩
  obtain ⟨s, B, _, hB, hAB⟩ := hA.exists_positive_shift_nonnegative
  obtain ⟨p, _, hs, he⟩ := exists_nonnegative_perron_eigenvector hB
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hs
  have hAp : A *ᵥ p = (s - (spectralRadius ℂ (B.map Complex.ofReal)).toReal) • p := by
    rw [hAB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, sub_smul]
  have hmem := mem_spectrum_complexification_of_real_eigenpair hpne hAp
  have hpos := hspec _ hmem
  simp only [Complex.ofReal_re] at hpos
  exact (isNonsingularMMatrix_iff_exists_shift_above_spectralRadius hA).mpr
    ⟨s, B, hB, hAB, sub_pos.mp hpos⟩

end Matrix
