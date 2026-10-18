import NLAlib.Matrix.Norms.SchattenDuality
import NLAlib.Matrix.Norms.ComplexSchattenProducts
import NLAlib.Matrix.Norms.TraceNuclear

/-!
# Complex trace Hölder and attained Schatten duality

The full complex trace pairing, rather than only its real part, attains
Schatten duality. Shared singular-power coefficients supply finite conjugate
pairs. The leading singular direction and the unit singular coefficients
supply the two infinity endpoints. Zero and empty matrices are included.
Source: Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
-/

noncomputable section
open scoped Matrix ENNReal

namespace NLAlib

/-- Sharp complex trace Hölder for every finite conjugate pair. -/
theorem norm_trace_conjTranspose_mul_le_schattenNormReal_mul_complex
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) :
    ‖(Aᴴ * B).trace‖ ≤ schattenNormReal A p * schattenNormReal B q := by
  calc
    _ ≤ schattenNormReal (Aᴴ * B) 1 := by
      simpa only [schattenNormReal_one] using norm_trace_le_nuclearNorm (Aᴴ * B)
    _ ≤ _ := by
      simpa only [schattenNormReal_conjTranspose] using
        schattenNormReal_mul_le_mul_complex Aᴴ B hpq

/-- Sharp complex trace Hölder, including both infinity endpoints. -/
theorem norm_trace_conjTranspose_mul_le_schattenNorm_mul_complex
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    ‖(Aᴴ * B).trace‖ ≤ schattenNorm A p * schattenNorm B q := by
  by_cases hp : p = ∞
  · subst p
    have hq : q = 1 := (ENNReal.HolderTriple.unique ∞ q 1 q).symm
    subst q
    simp only [schattenNorm_top, schattenNorm_one]
    apply (norm_trace_le_nuclearNorm (Aᴴ * B)).trans
    simpa only [schattenNormReal_one, specNorm_conjTranspose] using
      schattenNormReal_mul_le_specNorm_mul Aᴴ B (by norm_num : (0 : ℝ) < 1)
  · by_cases hq : q = ∞
    · subst q
      have hp' : p = 1 := (ENNReal.HolderTriple.unique p ∞ 1 p).symm
      subst p
      simp only [schattenNorm_top, schattenNorm_one]
      apply (norm_trace_le_nuclearNorm (Aᴴ * B)).trans
      have h := schattenNormReal_mul_le_mul_specNorm Aᴴ B (by norm_num : (0 : ℝ) < 1)
      rw [schattenNormReal_conjTranspose] at h
      simpa only [schattenNormReal_one] using h
    · rw [schattenNorm_eq_of_ne_top _ hp, schattenNorm_eq_of_ne_top _ hq]
      exact norm_trace_conjTranspose_mul_le_schattenNormReal_mul_complex A B
        (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)

/-- Sharp finite complex trace Hölder in the direct product orientation. -/
theorem norm_trace_mul_le_schattenNormReal_mul_complex
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) :
    ‖(A * B).trace‖ ≤ schattenNormReal A p * schattenNormReal B q := by
  simpa only [Matrix.conjTranspose_conjTranspose, schattenNormReal_conjTranspose] using
    norm_trace_conjTranspose_mul_le_schattenNormReal_mul_complex Aᴴ B hpq

/-- Sharp extended complex trace Hölder in the direct product orientation. -/
theorem norm_trace_mul_le_schattenNorm_mul_complex
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    ‖(A * B).trace‖ ≤ schattenNorm A p * schattenNorm B q := by
  simpa only [Matrix.conjTranspose_conjTranspose, schattenNorm_conjTranspose] using
    norm_trace_conjTranspose_mul_le_schattenNorm_mul_complex Aᴴ B (p := p) (q := q)

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem exists_schattenNormReal_le_one_trace_conjTranspose_mul_eq_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) {p q : ℝ} (hpq : Real.HolderConjugate p q) :
    ∃ B : Matrix (Fin m) (Fin n) 𝕜,
      schattenNormReal B q ≤ 1 ∧ (Aᴴ * B).trace = (schattenNormReal A p : 𝕜) := by
  by_cases hA : A = 0
  · subst A
    refine ⟨0, ?_, ?_⟩
    · rw [schattenNormReal_zero hpq.symm.pos]; norm_num
    · simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
        schattenNormReal_zero hpq.pos, RCLike.ofReal_zero]
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    refine ⟨U * (rectDiag (schattenDualCoefficients A p) : Matrix (Fin m) (Fin n) 𝕜) * Vᴴ,
      (h.schattenDualCoefficients_attain hpq hA).1.le, ?_⟩
    rw [h.trace_conjTranspose_mul_mul_rectDiag_mul_conjTranspose,
      sum_singularValues_mul_schattenDualCoefficients_eq A hpq hA]

private theorem exists_nuclearNorm_le_one_trace_conjTranspose_mul_eq_specNorm_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) :
    ∃ B : Matrix (Fin m) (Fin n) 𝕜,
      nuclearNorm B ≤ 1 ∧ (Aᴴ * B).trace = (specNorm A : 𝕜) := by
  by_cases hA : A = 0
  · subst A
    refine ⟨0, ?_, ?_⟩
    · rw [← schattenNormReal_one, schattenNormReal_zero (by norm_num : (0 : ℝ) < 1)]
      norm_num
    · simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
        specNorm_zero, RCLike.ofReal_zero]
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    refine ⟨U * (rectDiag leadingSingularCoefficients : Matrix (Fin m) (Fin n) 𝕜) * Vᴴ,
      (h.leadingSingularCoefficients_attain hA).1.le, ?_⟩
    have hpair := (h.leadingSingularCoefficients_attain hA).2
    rw [h.frobInner_mul_rectDiag_mul_conjTranspose] at hpair
    rw [h.trace_conjTranspose_mul_mul_rectDiag_mul_conjTranspose, hpair]

open scoped Matrix.Norms.L2Operator in
private theorem exists_specNorm_le_one_trace_conjTranspose_mul_eq_nuclearNorm_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) :
    ∃ B : Matrix (Fin m) (Fin n) 𝕜,
      specNorm B ≤ 1 ∧ (Aᴴ * B).trace = (nuclearNorm A : 𝕜) := by
  by_cases hA : A = 0
  · subst A
    refine ⟨0, ?_, ?_⟩
    · simp [specNorm]
    · simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero]
      rw [← schattenNormReal_one, schattenNormReal_zero (by norm_num : (0 : ℝ) < 1),
        RCLike.ofReal_zero]
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    have hN : 0 < min m n := by
      by_contra hn
      have hs := singularValues_eq_zero_of_min_le A
        (show min (Fintype.card (Fin m)) (Fintype.card (Fin n)) ≤ 0 by
          simpa only [Fintype.card_fin] using not_lt.mp hn)
      rw [singularValues_zero_eq_specNorm] at hs
      exact hA (norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hs))
    let B : Matrix (Fin m) (Fin n) 𝕜 :=
      U * (rectDiag (fun _ => 1) : Matrix (Fin m) (Fin n) 𝕜) * Vᴴ
    refine ⟨B, ?_, ?_⟩
    · have hs : singularValues B 0 = 1 := singularValues_eq_of_eq_mul_rectDiag_mul
        h.conjTranspose_mul_left h.conjTranspose_mul_right (fun _ => zero_le_one)
        (fun _ _ _ => le_rfl) rfl hN
      rw [singularValues_zero_eq_specNorm] at hs
      exact hs.le
    · change (Aᴴ * (U * (rectDiag (fun _ => 1) : Matrix (Fin m) (Fin n) 𝕜) * Vᴴ)).trace = _
      rw [h.trace_conjTranspose_mul_mul_rectDiag_mul_conjTranspose]
      simp only [mul_one]
      congr 1
      simp only [nuclearNorm_eq_sum_range, Fintype.card_fin]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Finite Schatten duality is attained in the full trace pairing over both
real and complex scalars, on every finite rectangular matrix space. -/
theorem exists_schattenNormReal_le_one_trace_conjTranspose_mul_eq (A : Matrix m n 𝕜)
    {p q : ℝ} (hpq : Real.HolderConjugate p q) :
    ∃ B : Matrix m n 𝕜,
      schattenNormReal B q ≤ 1 ∧ (Aᴴ * B).trace = (schattenNormReal A p : 𝕜) := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  obtain ⟨Bf, hBn, hBpair⟩ :=
    exists_schattenNormReal_le_one_trace_conjTranspose_mul_eq_fin (A.reindex em en) hpq
  let B := Bf.reindex em.symm en.symm
  have hBr : B.reindex em en = Bf := by ext i j; simp [B, Matrix.reindex_apply]
  refine ⟨B, ?_, ?_⟩
  · simpa only [B, schattenNormReal_reindex] using hBn
  · have h := trace_conjTranspose_mul_reindex A B em en
    rw [hBr, hBpair, schattenNormReal_reindex] at h
    exact h.symm

/-- Every extended conjugate Schatten pair has an actual full-trace
attainer, including the nuclear/spectral endpoints, zero, and empty shapes. -/
theorem exists_schattenNorm_le_one_trace_conjTranspose_mul_eq (A : Matrix m n 𝕜)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    ∃ B : Matrix m n 𝕜,
      schattenNorm B q ≤ 1 ∧ (Aᴴ * B).trace = (schattenNorm A p : 𝕜) := by
  by_cases hp : p = ∞
  · subst p
    have hq : q = 1 := (ENNReal.HolderTriple.unique ∞ q 1 q).symm
    subst q
    simp only [schattenNorm_top, schattenNorm_one]
    let em := Fintype.equivFin m
    let en := Fintype.equivFin n
    obtain ⟨Bf, hBn, hBpair⟩ :=
      exists_nuclearNorm_le_one_trace_conjTranspose_mul_eq_specNorm_fin (A.reindex em en)
    let B := Bf.reindex em.symm en.symm
    have hBr : B.reindex em en = Bf := by ext i j; simp [B, Matrix.reindex_apply]
    refine ⟨B, ?_, ?_⟩
    · rw [← schattenNormReal_one] at hBn ⊢
      simpa only [B, schattenNormReal_reindex] using hBn
    · have h := trace_conjTranspose_mul_reindex A B em en
      rw [hBr, hBpair, specNorm_reindex] at h
      exact h.symm
  · by_cases hq : q = ∞
    · subst q
      have hp' : p = 1 := (ENNReal.HolderTriple.unique p ∞ 1 p).symm
      subst p
      simp only [schattenNorm_top, schattenNorm_one]
      let em := Fintype.equivFin m
      let en := Fintype.equivFin n
      obtain ⟨Bf, hBn, hBpair⟩ :=
        exists_specNorm_le_one_trace_conjTranspose_mul_eq_nuclearNorm_fin (A.reindex em en)
      let B := Bf.reindex em.symm en.symm
      have hBr : B.reindex em en = Bf := by ext i j; simp [B, Matrix.reindex_apply]
      refine ⟨B, ?_, ?_⟩
      · simpa only [B, specNorm_reindex] using hBn
      · have h := trace_conjTranspose_mul_reindex A B em en
        rw [hBr, hBpair, ← schattenNormReal_one, schattenNormReal_reindex,
          schattenNormReal_one] at h
        exact h.symm
    · simp only [schattenNorm_eq_of_ne_top _ hp, schattenNorm_eq_of_ne_top _ hq]
      exact exists_schattenNormReal_le_one_trace_conjTranspose_mul_eq A
        (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)

/-- Finite Schatten duality in the left-test orientation used by analytic
matrix interpolation. -/
theorem exists_schattenNormReal_le_one_trace_mul_eq (A : Matrix m n 𝕜)
    {p q : ℝ} (hpq : Real.HolderConjugate p q) :
    ∃ T : Matrix n m 𝕜,
      schattenNormReal T q ≤ 1 ∧ (T * A).trace = (schattenNormReal A p : 𝕜) := by
  obtain ⟨B, hBn, hpair⟩ := exists_schattenNormReal_le_one_trace_conjTranspose_mul_eq A hpq
  refine ⟨Bᴴ, ?_, ?_⟩
  · simpa only [schattenNormReal_conjTranspose] using hBn
  · have h := congrArg star hpair
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, RCLike.star_def, RCLike.conj_ofReal] at h
    exact h

/-- Schatten duality in the left-test orientation used by analytic matrix
interpolation. The tester is an actual matrix with conjugate unit norm bound. -/
theorem exists_schattenNorm_le_one_trace_mul_eq (A : Matrix m n 𝕜)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    ∃ T : Matrix n m 𝕜, schattenNorm T q ≤ 1 ∧ (T * A).trace = (schattenNorm A p : 𝕜) := by
  obtain ⟨B, hBn, hpair⟩ := exists_schattenNorm_le_one_trace_conjTranspose_mul_eq A (p := p) (q := q)
  refine ⟨Bᴴ, ?_, ?_⟩
  · simpa only [schattenNorm_conjTranspose] using hBn
  · have h := congrArg star hpair
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, RCLike.star_def, RCLike.conj_ofReal] at h
    exact h

end NLAlib
