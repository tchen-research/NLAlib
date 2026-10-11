/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.DirectionalOutputEnergy

set_option autoImplicit false

/-!
# Directional exact-grade operator bounds

The supported-vector and restricted matrix norm bounds for all three directional bands.
Ported from `SparseFockFormal.DirectionalConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace DirectionalConcrete

open ParsevalFrame LocalOperator BandInventory FiniteOperator ExternalOperator
  GlobalBands NamedBands FiniteHilbert
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Sharp squared-energy estimate for `Y₊` on an exactly supported vector.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Yplus m (frameRows F)) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  exact DirectionalBounds.directional_energy_sq_bound
    (Nat.cast_nonneg nu) (FiniteHilbert.normSq_nonneg x)
    (Yplus_output_energy_le_marked F hx)
    (markedEnergy_one_zero_le F hx)

/-- Sharp denominator-free squared-energy estimate for `Y₀` on an exactly
supported vector.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_two_mul_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    2 * FiniteHilbert.normSq
      (Matrix.mulVec (Yzero m (frameRows F)) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  exact DirectionalBounds.directional_energy_half_sq_bound
    (Nat.cast_nonneg nu) (Yzero_output_energy_le_marked F hx)
    (two_mul_markedEnergy_two_zero_le F hx)

/-- Sharp squared-energy estimate for the transpose light hop on an exactly
supported vector.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    FiniteHilbert.normSq
      (Matrix.mulVec (Hprime m (frameRows F)) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  exact DirectionalBounds.directional_energy_sq_bound
    (Nat.cast_nonneg nu) (FiniteHilbert.normSq_nonneg x)
    (Hprime_output_energy_le_marked F hx)
    (markedEnergy_one_zero_le F hx)

/-- Coordinate energy of the genuine restricted `Y₊` matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
      (Matrix.mulVec
        (Yplus m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  have h := Yplus_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    FiniteHilbert.normSq
        (Matrix.mulVec
          (Yplus m (frameRows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Denominator-free coordinate energy of the genuine restricted `Y₀`
matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_restricted_two_mul_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    2 * FiniteHilbert.normSq
      (Matrix.mulVec
        (Yzero m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  have h := Yzero_two_mul_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    2 * FiniteHilbert.normSq
        (Matrix.mulVec
          (Yzero m (frameRows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Coordinate energy of the genuine restricted transpose-hop matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
      (Matrix.mulVec
        (Hprime m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  have h := Hprime_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    FiniteHilbert.normSq
        (Matrix.mulVec
          (Hprime m (frameRows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Restricting the mixed preserving band to one grade gives its occupation-energy estimate.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
      (Matrix.mulVec
        (Yzero m (frameRows F) * gradeProjection (d := d) nu) x) ≤
      ((nu : ℝ) / Real.sqrt 2) ^ 2 * FiniteHilbert.normSq x := by
  have htwo := Yzero_restricted_two_mul_energy (m := m) F nu x
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hconstant : ((nu : ℝ) / Real.sqrt 2) ^ 2 =
      (nu : ℝ) ^ 2 / 2 := by
    rw [div_pow, hsqrt]
  rw [hconstant]
  nlinarith [FiniteHilbert.normSq_nonneg
    (Matrix.mulVec
      (Yzero m (frameRows F) * gradeProjection (d := d) nu) x)]

/-- The first directional row-local bound from the paper, as an actual L2
matrix operator norm.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_Yplus_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Yplus m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (Yplus_restricted_energy (m := m) F nu)

/-- The second directional row-local bound, including the sharp `sqrt 2`
denominator.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_Yzero_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Yzero m (frameRows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / Real.sqrt 2 := by
  exact norm_le_of_normSq_mulVec_le
    (div_nonneg (Nat.cast_nonneg nu) (Real.sqrt_nonneg 2))
    (Yzero_restricted_energy (m := m) F nu)

/-- The transpose light-hop directional row-local bound, as an actual L2
matrix operator norm.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_Hprime_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Hprime m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (Hprime_restricted_energy (m := m) F nu)

end

end DirectionalConcrete

end NLAlib.SparseFock
