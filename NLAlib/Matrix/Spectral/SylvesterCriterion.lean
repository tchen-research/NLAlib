import NLAlib.Matrix.Spectral.Inertia
import NLAlib.Matrix.Basic.SchurComplement
/-!
# Positive definiteness from leading and trailing minors

Sylvester's criterion follows by induction through the first pivot Schur
complement. Reversing the finite coordinate order gives the trailing-minor
criterion. Source: Horn--Johnson (2013), Theorem 7.2.5 and Corollary 7.2.4.
Atlas: `sylvester-criterion`.
-/

noncomputable section
open Matrix

namespace NLAlib

/-- The trailing principal minor is the leading principal minor after
reversing coordinate order; simultaneous reversal of rows and columns
does not change the determinant of the selected block.
Horn--Johnson (2013), Theorem 7.2.5; supports `sylvester-criterion`. -/
def trailingMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  leadingMinor (A.submatrix Fin.rev Fin.rev) k

/-- A first-pivot Schur step factors every larger leading minor by the
first pivot. Horn--Johnson (2013), Theorem 7.2.5;
helper for `sylvester-criterion`. -/
theorem leadingMinor_eq_pivot_mul_leadingMinor_pivotSchur {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ha : A 0 0 ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    leadingMinor A (k + 1) = A 0 0 * leadingMinor (pivotSchur A) k := by
  have hsucc : k + 1 ≤ n + 1 := Nat.succ_le_succ hk
  have hRestr : pivotSchur (A.submatrix (Fin.castLE hsucc) (Fin.castLE hsucc)) =
      (pivotSchur A).submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext i j
    rfl
  simp only [leadingMinor, dif_pos hsucc, dif_pos hk]
  rw [det_eq_mul_det_pivotSchur _ (by exact ha), hRestr]
  rfl

/-- Positive definite matrices have positive leading principal minors.
Horn--Johnson (2013), Theorem 7.2.5.
atlas: sylvester-criterion (partial) -/
theorem leadingMinor_pos_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (k : ℕ) (hk : k ≤ n) : 0 < leadingMinor A k := by
  rw [leadingMinor, dif_pos hk]
  exact (hA.submatrix (Fin.castLE_injective hk)).det_pos

/-- A real symmetric matrix with positive leading principal minors is
positive definite, including the empty-dimensional case.
Horn--Johnson (2013), Theorem 7.2.5.
atlas: sylvester-criterion (partial) -/
theorem posDef_of_leadingMinor_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian)
    (hminor : ∀ k, 1 ≤ k → k ≤ n → 0 < leadingMinor A k) : A.PosDef := by
  induction n with
  | zero =>
    apply PosDef.of_dotProduct_mulVec_pos hA
    intro x hx
    exact False.elim (hx (Subsingleton.elim x 0))
  | succ n ih =>
    have ha : 0 < A 0 0 := by
      have h := hminor 1 (by rfl) (by omega)
      simpa [leadingMinor] using h
    apply (posDef_iff_pivotSchur (Matrix.isHermitian_iff_isSymm.mp hA)).mpr
    refine ⟨ha, ih (Matrix.isHermitian_iff_isSymm.mpr
      (isSymm_pivotSchur (Matrix.isHermitian_iff_isSymm.mp hA))) ?_⟩
    intro k hk₁ hkn
    have h := hminor (k + 1) (by omega) (by omega)
    rw [leadingMinor_eq_pivot_mul_leadingMinor_pivotSchur A ha.ne' k hkn] at h
    by_contra hb
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hb))) h

/-- Sylvester's leading-principal-minor criterion for a real symmetric
matrix. Horn--Johnson (2013), Theorem 7.2.5.
atlas: sylvester-criterion -/
theorem posDef_iff_leadingMinor_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < leadingMinor A k :=
  ⟨fun h k _ hk => leadingMinor_pos_of_posDef h k hk, posDef_of_leadingMinor_pos hA⟩

/-- Sylvester's equivalent trailing-principal-minor criterion.
Horn--Johnson (2013), Theorem 7.2.5 and Corollary 7.2.4.
atlas: sylvester-criterion -/
theorem posDef_iff_trailingMinor_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < trailingMinor A k := by
  constructor
  · intro h k _ hk
    exact leadingMinor_pos_of_posDef (h.submatrix Fin.rev_injective) k hk
  · intro h
    have hrev : (A.submatrix Fin.rev Fin.rev).PosDef :=
      posDef_of_leadingMinor_pos (hA.submatrix Fin.rev) h
    have hA' := hrev.submatrix Fin.rev_injective
    have hmat : (A.submatrix Fin.rev Fin.rev).submatrix Fin.rev Fin.rev = A := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.rev_rev]
    rw [hmat] at hA'
    exact hA'

/-- The full leading principal minor is the determinant of the matrix.
The finite-prefix definition; helper for `sylvester-criterion`. -/
theorem leadingMinor_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    leadingMinor A n = A.det := by
  rw [leadingMinor, dif_pos le_rfl]
  rfl

/-- With a positive first pivot, a PSD pivot Schur complement makes the
whole symmetric matrix PSD. Completion of squares;
helper for `sylvester-criterion`. -/
theorem posSemidef_of_pivotSchur_posSemidef {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hAh : A.IsHermitian)
    (ha : 0 < A 0 0) (hP : (pivotSchur A).PosSemidef) : A.PosSemidef := by
  have hA : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hAh
  have hsym : ∀ y : Fin n → ℝ,
      ∑ i, y i * A i.succ 0 = ∑ j, A 0 j.succ * y j := fun y =>
    Finset.sum_congr rfl fun i _ => by rw [hA.apply 0 i.succ, mul_comm]
  apply PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hA)
  intro x
  have hxe : x = Matrix.vecCons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
  simp only [star_trivial]
  rw [hxe, dotProduct_mulVec_vecCons, hsym]
  set y := Fin.tail x
  set t := ∑ j, A 0 j.succ * y j
  have hq := hP.dotProduct_mulVec_nonneg y
  simp only [star_trivial] at hq
  rw [dotProduct_pivotSchur_mulVec, hsym] at hq
  have key : A 0 0 * (x 0 + (A 0 0)⁻¹ * t) ^ 2 =
      A 0 0 * x 0 ^ 2 + 2 * x 0 * t + (A 0 0)⁻¹ * (t * t) := by
    field_simp
    ring
  nlinarith [key, mul_nonneg ha.le (sq_nonneg (x 0 + (A 0 0)⁻¹ * t))]

/-- If the first `n-1` leading minors are positive and the determinant is
nonnegative, a real symmetric matrix is PSD. This includes dimensions zero
and one. Horn--Johnson (2013), Corollary 7.2.4.
atlas: sylvester-criterion -/
theorem posSemidef_of_leadingMinor_pos_and_det_nonneg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hminor : ∀ k, 1 ≤ k → k < n → 0 < leadingMinor A k) (hdet : 0 ≤ A.det) :
    A.PosSemidef := by
  induction n with
  | zero =>
    apply PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    simp
  | succ n ih =>
    cases n with
    | zero =>
      change Matrix (Fin 1) (Fin 1) ℝ at A
      change 0 ≤ (A : Matrix (Fin 1) (Fin 1) ℝ).det at hdet
      have ha : 0 ≤ A 0 0 := by simpa only [Matrix.det_fin_one] using hdet
      have hmat : A = diagonal (fun _ : Fin 1 => A 0 0) := by
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        simp only [hi, hj, Matrix.diagonal_apply_eq]
      rw [hmat]
      exact PosSemidef.diagonal fun _ => ha
    | succ n =>
      have ha : 0 < A 0 0 := by
        have h := hminor 1 (by rfl) (by omega)
        simpa [leadingMinor] using h
      apply posSemidef_of_pivotSchur_posSemidef ( hA) ha
      apply ih (Matrix.isHermitian_iff_isSymm.mpr
        (isSymm_pivotSchur (Matrix.isHermitian_iff_isSymm.mp hA)))
      · intro k hk hkn
        have h := hminor (k + 1) (by omega) (by omega)
        rw [leadingMinor_eq_pivot_mul_leadingMinor_pivotSchur A ha.ne' k (by omega)] at h
        by_contra hb
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hb))) h
      · have h := det_eq_mul_det_pivotSchur A ha.ne'
        rw [h] at hdet
        by_contra hb
        have hneg := mul_neg_of_pos_of_neg ha (lt_of_not_ge hb)
        exact (not_lt_of_ge hdet) hneg

end NLAlib
