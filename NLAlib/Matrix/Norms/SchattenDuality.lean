import NLAlib.Matrix.Norms.SchattenSingularCoefficients
/-!
# Attained Schatten duality

Finite conjugates use the normalized powers of the original singular values.
The endpoint witnesses are the top-singular-frame partial isometry
(`exists_specNorm_le_one_frobInner_eq_nuclearNorm`) and a leading rank-one
singular-vector outer product. Zero matrices use zero, including empty shapes.
Source: Bhatia (1997), §IV.2; matrix toolkit derivations, (10).
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace NLAlib

/-- The explicit normalized power coefficients in the finite Schatten dual
attainer. At a nonzero matrix and `1 < p`, these are
`σᵢ^(p-1) / ‖A‖_(S_p)^(p-1)`.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
def schattenDualCoefficients {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (p : ℝ) (i : ℕ) : ℝ :=
  singularValues A i ^ (p - 1) / schattenNorm A p ^ (p - 1)

/-- A nonzero matrix's normalized singular power coefficients have conjugate
power sum one, with the exact source scaling.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem sum_schattenDualCoefficients_rpow_eq_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {p q : ℝ} (hpq : Real.HolderConjugate p q) (hA : A ≠ 0) :
    (∑ i ∈ Finset.range (min m n), schattenDualCoefficients A p i ^ q) = 1 := by
  have hN : 0 < schattenNorm A p := lt_of_le_of_ne (schattenNorm_nonneg A p)
    (Ne.symm (fun h => hA ((schattenNorm_eq_zero_iff A hpq.pos).mp h)))
  have hS : 0 ≤ ∑ i ∈ Finset.range (min m n), singularValues A i ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) p)
  have hpow : schattenNorm A p ^ p = ∑ i ∈ Finset.range (min m n), singularValues A i ^ p := by
    simp only [schattenNorm, Fintype.card_fin]
    change ((∑ i ∈ Finset.range (min m n), singularValues A i ^ p) ^ (1 / p)) ^ p = _
    rw [one_div, Real.rpow_inv_rpow hS hpq.ne_zero]
  have hden : (schattenNorm A p ^ (p - 1)) ^ q = schattenNorm A p ^ p := by
    rw [← Real.rpow_mul hN.le, hpq.sub_one_mul_conj]
  simp only [schattenDualCoefficients]
  change (∑ i ∈ Finset.range (min m n),
    (singularValues A i ^ (p - 1) / schattenNorm A p ^ (p - 1)) ^ q) = 1
  simp_rw [Real.div_rpow (Real.rpow_nonneg (singularValues_nonneg A _) _) (Real.rpow_nonneg hN.le _),
    ← Real.rpow_mul (singularValues_nonneg A _), hpq.sub_one_mul_conj, hden]
  rw [← Finset.sum_div, ← hpow, div_self (Real.rpow_pos_of_pos hN p).ne']

/-- Pairing with the normalized singular power coefficients is exactly the
original Schatten norm. Zero singular values contribute zero.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem sum_singularValues_mul_schattenDualCoefficients_eq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {p q : ℝ} (hpq : Real.HolderConjugate p q) (hA : A ≠ 0) :
    (∑ i ∈ Finset.range (min m n), singularValues A i * schattenDualCoefficients A p i) =
      schattenNorm A p := by
  have hN : 0 < schattenNorm A p := lt_of_le_of_ne (schattenNorm_nonneg A p)
    (Ne.symm (fun h => hA ((schattenNorm_eq_zero_iff A hpq.pos).mp h)))
  have hS : 0 ≤ ∑ i ∈ Finset.range (min m n), singularValues A i ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) p)
  have hpow : schattenNorm A p ^ p = ∑ i ∈ Finset.range (min m n), singularValues A i ^ p := by
    simp only [schattenNorm, Fintype.card_fin]
    change ((∑ i ∈ Finset.range (min m n), singularValues A i ^ p) ^ (1 / p)) ^ p = _
    rw [one_div, Real.rpow_inv_rpow hS hpq.ne_zero]
  have hterm (i : ℕ) : singularValues A i * schattenDualCoefficients A p i =
      singularValues A i ^ p / schattenNorm A p ^ (p - 1) := by
    change singularValues A i * (singularValues A i ^ (p - 1) / _) = _
    have hprod : singularValues A i * singularValues A i ^ (p - 1) = singularValues A i ^ p := by
      calc
        _ = singularValues A i ^ (1 : ℝ) * singularValues A i ^ (p - 1) := by rw [Real.rpow_one]
        _ = singularValues A i ^ (1 + (p - 1)) :=
          (Real.rpow_add_of_nonneg (singularValues_nonneg A i) (by norm_num : (0 : ℝ) ≤ 1)
            hpq.sub_one_pos.le).symm
        _ = _ := by congr 1; ring
    rw [← mul_div_assoc, hprod]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← hpow, Real.rpow_sub hN, Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos hN p).ne']

/-- In fixed SVD frames, the normalized power coefficients give a unit
conjugate Schatten norm and attain the source matrix norm.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem IsSVD.schattenDualCoefficients_attain {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U V) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) (hA : A ≠ 0) :
    schattenNorm (U * (rectDiag (schattenDualCoefficients A p) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) q = 1 ∧
    frobInner A (U * (rectDiag (schattenDualCoefficients A p) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) =
      schattenNorm A p := by
  have hb0 : ∀ i, 0 ≤ schattenDualCoefficients A p i := fun i =>
    div_nonneg (Real.rpow_nonneg (singularValues_nonneg A i) _)
      (Real.rpow_nonneg (schattenNorm_nonneg A p) _)
  have hb : Antitone (schattenDualCoefficients A p) := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (singularValues_nonneg A j) (singularValues_antitone A hij) hpq.sub_one_pos.le)
      (Real.rpow_nonneg (schattenNorm_nonneg A p) _)
  constructor
  · rw [schattenNorm_mul_rectDiag_mul_transpose h.conjTranspose_mul_left h.conjTranspose_mul_right
      _ hb0 hb, sum_schattenDualCoefficients_rpow_eq_one A hpq hA, Real.one_rpow]
  · rw [h.frobInner_mul_rectDiag_mul_transpose,
      sum_singularValues_mul_schattenDualCoefficients_eq A hpq hA]

/-- `Fin` step of `exists_schattenNorm_le_one_frobInner_eq`. -/
private theorem exists_schattenNorm_le_one_frobInner_eq_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {p q : ℝ} (hpq : Real.HolderConjugate p q) :
    ∃ B : Matrix (Fin m) (Fin n) ℝ, schattenNorm B q ≤ 1 ∧ frobInner A B = schattenNorm A p := by
  by_cases hA : A = 0
  · subst A
    refine ⟨0, ?_, ?_⟩
    · rw [schattenNorm_zero hpq.symm.pos]; norm_num
    · rw [frobInner_zero_left, schattenNorm_zero hpq.pos]
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    have hb := h.schattenDualCoefficients_attain hpq hA
    exact ⟨_, hb.1.le, hb.2⟩

/-- The leading singular-vector coefficient list, giving a rank-one outer
product in SVD frames whenever the matrix shape has a nonempty diagonal.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
def leadingSingularCoefficients (i : ℕ) : ℝ := if i = 0 then 1 else 0

/-- The polar singular coefficients are one exactly on the positive
singular-value prefix of length equal to the matrix rank.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
def polarSingularCoefficients (r i : ℕ) : ℝ := if i < r then 1 else 0

/-- Polar singular coefficients are nonnegative.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem polarSingularCoefficients_nonneg (r i : ℕ) : 0 ≤ polarSingularCoefficients r i := by
  simp only [polarSingularCoefficients]
  split_ifs <;> norm_num

/-- Polar singular coefficients decrease with their index.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem polarSingularCoefficients_antitone (r : ℕ) : Antitone (polarSingularCoefficients r) := by
  intro i j hij
  by_cases hj : j < r
  · have hi : i < r := lt_of_le_of_lt hij hj
    simp [polarSingularCoefficients, hi, hj]
  · simp only [polarSingularCoefficients, if_neg hj]
    split_ifs <;> norm_num

/-- A singular-frame partial isometry with `r` supported coefficients has
rank exactly `r`, including zero and full thin rank.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem rank_mul_rectDiag_polarSingularCoefficients_mul_transpose {m n r : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (hr : r ≤ min m n) :
    (U * (rectDiag (polarSingularCoefficients r) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ).rank = r := by
  rw [rank_eq_card_singularValues_ne_zero, Fintype.card_fin, Fintype.card_fin]
  have hfilter : ((Finset.range (min m n)).filter fun i =>
      singularValues (U * (rectDiag (polarSingularCoefficients r) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) i ≠ 0) =
      Finset.range r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hne⟩
      rw [singularValues_eq_of_eq_mul_rectDiag_mul
        (A := U * (rectDiag (polarSingularCoefficients r) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ)
        (show Uᵀ * U = 1 from hU) (show Vᵀ * V = 1 from hV) (polarSingularCoefficients_nonneg r)
        (polarSingularCoefficients_antitone r) rfl hi] at hne
      by_contra hir
      simp [polarSingularCoefficients, hir] at hne
    · intro hi
      have him : i < min m n := hi.trans_le hr
      refine ⟨him, ?_⟩
      rw [singularValues_eq_of_eq_mul_rectDiag_mul
        (A := U * (rectDiag (polarSingularCoefficients r) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ)
        (show Uᵀ * U = 1 from hU) (show Vᵀ * V = 1 from hV) (polarSingularCoefficients_nonneg r)
        (polarSingularCoefficients_antitone r) rfl him]
      simp [polarSingularCoefficients, hi]
  rw [hfilter, Finset.card_range]

/-- The leading singular-frame outer product has rank exactly one whenever
the thin matrix shape is nonempty.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem rank_mul_rectDiag_leadingSingularCoefficients_mul_transpose {m n : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (hN : 0 < min m n) :
    (U * (rectDiag leadingSingularCoefficients : Matrix (Fin m) (Fin n) ℝ) * Vᵀ).rank = 1 := by
  have heq : leadingSingularCoefficients = polarSingularCoefficients 1 := by
    funext i
    simp [leadingSingularCoefficients, polarSingularCoefficients]
  rw [heq]
  exact rank_mul_rectDiag_polarSingularCoefficients_mul_transpose hU hV hN

/-- The leading singular-vector outer product has nuclear norm one and
attains the spectral pairing for every nonzero matrix.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem IsSVD.leadingSingularCoefficients_attain {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U V) (hA : A ≠ 0) :
    nuclearNorm (U * (rectDiag leadingSingularCoefficients : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) = 1 ∧
    frobInner A (U * (rectDiag leadingSingularCoefficients : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) = specNorm A := by
  have hfirst : singularValues A 0 = specNorm A := by
    simpa only [kyFanNorm, Finset.sum_range_one, singularValues] using kyFanNorm_one_eq_specNorm A
  have hN : 0 < min m n := by
    by_contra hn
    have hs : singularValues A 0 = 0 :=
      singularValues_eq_zero_of_min_le A (by simp only [Fintype.card_fin]; omega)
    have hzero : specNorm A = 0 := hfirst.symm.trans hs
    exact hA (norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hzero))
  have hb0 : ∀ i, 0 ≤ leadingSingularCoefficients i := by
    intro i
    simp only [leadingSingularCoefficients]
    split_ifs <;> norm_num
  have hb : Antitone leadingSingularCoefficients := by
    intro i j hij
    by_cases hj : j = 0
    · subst j
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      simp [hi]
    · simp only [leadingSingularCoefficients, if_neg hj]
      split_ifs <;> norm_num
  constructor
  · rw [← schattenNorm_one, schattenNorm_mul_rectDiag_mul_transpose
      h.conjTranspose_mul_left h.conjTranspose_mul_right _ hb0 hb]
    simp [leadingSingularCoefficients, hN]
  · rw [h.frobInner_mul_rectDiag_mul_transpose]
    simpa [leadingSingularCoefficients, hN] using hfirst

/-- `Fin` step of `exists_nuclearNorm_le_one_frobInner_eq_specNorm`. -/
private theorem exists_nuclearNorm_le_one_frobInner_eq_specNorm_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : Matrix (Fin m) (Fin n) ℝ, nuclearNorm B ≤ 1 ∧ frobInner A B = specNorm A := by
  by_cases hA : A = 0
  · subst A
    refine ⟨0, ?_, ?_⟩
    · rw [nuclearNorm, kyFanNorm_zero_matrix]; norm_num
    · simp [specNorm]
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    have hb := h.leadingSingularCoefficients_attain hA
    exact ⟨_, hb.1.le, hb.2⟩

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Finite-conjugate Schatten duality is attained on arbitrary finite matrix indices:
the witness is the explicit singular-power formula in SVD frames (transported from `Fin`),
and the zero matrix uses the zero witness, covering empty shapes.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem exists_schattenNorm_le_one_frobInner_eq (A : Matrix m n ℝ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) :
    ∃ B : Matrix m n ℝ, schattenNorm B q ≤ 1 ∧ frobInner A B = schattenNorm A p := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  obtain ⟨Bf, hBn, hBpair⟩ := exists_schattenNorm_le_one_frobInner_eq_fin (A.reindex em en) hpq
  let B := Bf.reindex em.symm en.symm
  have hBr : B.reindex em en = Bf := by ext i j; simp [B, Matrix.reindex_apply]
  refine ⟨B, ?_, ?_⟩
  · change schattenNorm (Bf.reindex em.symm en.symm) q ≤ 1
    rwa [schattenNorm_reindex]
  · have h := frobInner_reindex A B em en
    rw [hBr, hBpair, schattenNorm_reindex] at h
    exact h.symm

/-- Spectral–nuclear duality is attained on arbitrary finite indices by the leading
singular-vector rank-one outer product (transported from `Fin`); the zero matrix uses
zero, including empty shapes. Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem exists_nuclearNorm_le_one_frobInner_eq_specNorm (A : Matrix m n ℝ) :
    ∃ B : Matrix m n ℝ, nuclearNorm B ≤ 1 ∧ frobInner A B = specNorm A := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  obtain ⟨Bf, hBn, hBpair⟩ := exists_nuclearNorm_le_one_frobInner_eq_specNorm_fin (A.reindex em en)
  let B := Bf.reindex em.symm en.symm
  have hBr : B.reindex em en = Bf := by ext i j; simp [B, Matrix.reindex_apply]
  refine ⟨B, ?_, ?_⟩
  · change nuclearNorm (Bf.reindex em.symm en.symm) ≤ 1
    rwa [nuclearNorm_reindex]
  · have h := frobInner_reindex A B em en
    rw [hBr, hBpair, specNorm_reindex] at h
    exact h.symm

/-- Extended Schatten norms are nonnegative, including exponent infinity.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem schattenNormExtended_nonneg (A : Matrix m n ℝ) (p : ℝ≥0∞) :
    0 ≤ schattenNormExtended A p := by
  by_cases hp : p = ∞
  · subst p
    exact specNorm_nonneg A
  · rw [schattenNormExtended_eq_of_ne_top _ hp]
    exact schattenNorm_nonneg A _

/-- Every conjugate pair of extended Schatten exponents has an actual
unit-ball attainer, including `(1,∞)`, `(∞,1)`, rank zero and empty shapes.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem exists_schattenNormExtended_le_one_frobInner_eq (A : Matrix m n ℝ)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    ∃ B : Matrix m n ℝ, schattenNormExtended B q ≤ 1 ∧ frobInner A B = schattenNormExtended A p := by
  by_cases hpTop : p = ∞
  · subst p
    have hq : q = 1 := (ENNReal.HolderTriple.unique ∞ q 1 q).symm
    subst q
    simp only [schattenNormExtended_top]
    simp only [schattenNormExtended_eq_of_ne_top _ (show (1 : ℝ≥0∞) ≠ ∞ by simp),
      ENNReal.toReal_one, schattenNorm_one]
    exact exists_nuclearNorm_le_one_frobInner_eq_specNorm A
  · by_cases hqTop : q = ∞
    · subst q
      have hp : p = 1 := (ENNReal.HolderTriple.unique p ∞ 1 p).symm
      subst p
      simp only [schattenNormExtended_top]
      simp only [schattenNormExtended_eq_of_ne_top _ (show (1 : ℝ≥0∞) ≠ ∞ by simp),
        ENNReal.toReal_one, schattenNorm_one]
      exact exists_specNorm_le_one_frobInner_eq_nuclearNorm A
    · simp only [schattenNormExtended_eq_of_ne_top _ hpTop,
        schattenNormExtended_eq_of_ne_top _ hqTop]
      exact exists_schattenNorm_le_one_frobInner_eq A
        (ENNReal.HolderConjugate.toReal_of_ne_top hpTop hqTop)

/-- Schatten duality as a greatest value on the genuine conjugate unit ball.
The upper bound is trace Hölder and membership is the explicit SVD attainer.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem isGreatest_schattenNormExtended_frobInner (A : Matrix m n ℝ)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    IsGreatest {z : ℝ | ∃ B : Matrix m n ℝ, schattenNormExtended B q ≤ 1 ∧ frobInner A B = z}
      (schattenNormExtended A p) := by
  refine ⟨exists_schattenNormExtended_le_one_frobInner_eq A, ?_⟩
  rintro z ⟨B, hB, rfl⟩
  calc
    frobInner A B ≤ |frobInner A B| := le_abs_self _
    _ ≤ schattenNormExtended A p * schattenNormExtended B q :=
      abs_frobInner_le_schattenNormExtended_mul A B
    _ ≤ schattenNormExtended A p * 1 :=
      mul_le_mul_of_nonneg_left hB (schattenNormExtended_nonneg A p)
    _ = _ := mul_one _

/-- The unit-ball supremum in Schatten duality equals the norm and is attained,
for every extended conjugate pair and every finite matrix shape.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12).
atlas: schatten-norms-def (partial) -/
theorem sSup_frobInner_schattenNormExtended_unitBall (A : Matrix m n ℝ)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] :
    sSup {z : ℝ | ∃ B : Matrix m n ℝ, schattenNormExtended B q ≤ 1 ∧ frobInner A B = z} =
      schattenNormExtended A p := by
  have h := isGreatest_schattenNormExtended_frobInner A (p := p) (q := q)
  exact h.isLUB.csSup_eq ⟨_, h.1⟩

end NLAlib
