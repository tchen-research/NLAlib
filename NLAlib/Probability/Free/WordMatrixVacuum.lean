import NLAlib.Probability.Free.WordMatrixAmplification
import NLAlib.Probability.Free.WordVacuumTrace
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# The actual normalized amplified vacuum functional

The native C*-matrix functional is the normalized sum of the actual vacuum
values of its diagonal entries. Positivity follows from its actual block
vector states. Traciality and faithfulness hold when the
entries belong to the concrete closed left-field algebra. No trace or
faithfulness on all bounded operators is asserted.

The squared entry bound is the native L2 part of Lemma 4.6 in
Bandeira--Cipolloni--Schroeder--van Handel, arXiv:2406.11453v2. It does not
assume any free norm or ultracontractive estimate.

-/

noncomputable section
set_option autoImplicit false

open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

/-- The actual dimension-normalized matrix vacuum, as a complex-linear map.
It is zero in empty matrix dimension; normalization at one requires nonempty D. -/
def wordMatrixVacuumExpectation : M →ₗ[ℂ] ℂ where
  toFun T := (Fintype.card D : ℂ)⁻¹ * ∑ j, wordVacuumExpectation ι (T j j)
  map_add' S T := by
    simp [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib, mul_add]
  map_smul' z T := by
    simp [CStarMatrix.smul_apply, map_smul, Finset.mul_sum, mul_left_comm]

omit [DecidableEq D] in
/-- The defining normalized diagonal formula. -/
@[simp]
theorem wordMatrixVacuumExpectation_apply (T : M) :
    wordMatrixVacuumExpectation (D := D) (ι := ι) T =
      (Fintype.card D : ℂ)⁻¹ * ∑ j, wordVacuumExpectation ι (T j j) := rfl

/-- The diagonal formula is exactly the normalized sum of actual vector
states on the native `PiLp 2` block representation, using one vacuum in each
coordinate. This is an identity of concrete operator expectations. -/
theorem wordMatrixVacuumExpectation_eq_sum_block_vector_states (T : M) :
    wordMatrixVacuumExpectation (D := D) (ι := ι) T =
      (Fintype.card D : ℂ)⁻¹ * ∑ j,
        inner ℂ (PiLp.single 2 j (wordVacuum ι))
          (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) T
            (PiLp.single 2 j (wordVacuum ι))) := by
  rw [wordMatrixVacuumExpectation_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [wordVacuumExpectation_apply]
  symm
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
    congr 1
    exact CStarMatrix.toPiLpCLM_apply_single T j (wordVacuum ι) j
  · intro k _ hkj
    simp [hkj]
  · simp

omit [DecidableEq D] in
/-- The actual amplified star-square expectation is the normalized sum of
squared Hilbert norms of all entrywise vacuum vectors. Empty D is included. -/
theorem wordMatrixVacuumExpectation_star_mul (T : M) :
    wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T) =
      (((Fintype.card D : ℝ)⁻¹ *
        ∑ j, ∑ i, ‖T i j (wordVacuum ι)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [wordMatrixVacuumExpectation_apply, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, map_sum, wordVacuumExpectation_star_mul]
  push_cast
  rfl

/-- Positivity of the actual amplified functional is derived from its
genuine Hilbert vector states under the actual native block representation. -/
def wordMatrixVacuumPositiveMap : M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (wordMatrixVacuumExpectation (D := D) (ι := ι)) fun T hT => by
    rw [wordMatrixVacuumExpectation_eq_sum_block_vector_states]
    apply mul_nonneg
    · have h : 0 ≤ (Fintype.card D : ℝ)⁻¹ := by positivity
      simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
        (Complex.zero_le_real.mpr h)
    · apply Finset.sum_nonneg
      intro j _
      have hBlock : 0 ≤ CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) T :=
        map_nonneg (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)) hT
      exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hBlock).inner_nonneg_right _

/-- The native positive-map bundle has the same actual diagonal values. -/
@[simp]
theorem wordMatrixVacuumPositiveMap_apply (T : M) :
    wordMatrixVacuumPositiveMap (D := D) (ι := ι) T =
      wordMatrixVacuumExpectation (D := D) (ι := ι) T := rfl

/-- The actual amplified vacuum is normalized in positive matrix dimension.
No nonempty-alphabet assumption is needed. -/
@[simp]
theorem wordMatrixVacuumExpectation_one [Nonempty D] :
    wordMatrixVacuumExpectation (D := D) (ι := ι) (1 : M) = 1 := by
  simp only [wordMatrixVacuumExpectation_apply, CStarMatrix.one_apply_eq,
    wordVacuumExpectation_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [DecidableEq D] in
/-- The actual amplified vacuum is tracial on matrices whose entries belong
to the concrete closed left-field algebra. Both factors have genuine membership. -/
theorem wordMatrixVacuumExpectation_mul_comm (S T : M)
    (hS : ∀ i j, S i j ∈ wordFieldAlgebra ι)
    (hT : ∀ i j, T i j ∈ wordFieldAlgebra ι) :
    wordMatrixVacuumExpectation (D := D) (ι := ι) (S * T) =
      wordMatrixVacuumExpectation (D := D) (ι := ι) (T * S) := by
  simp only [wordMatrixVacuumExpectation_apply, CStarMatrix.mul_apply, map_sum]
  congr 1
  calc
    ∑ i, ∑ j, wordVacuumExpectation ι (S i j * T j i) =
        ∑ i, ∑ j, wordVacuumExpectation ι (T j i * S i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact wordVacuumExpectation_mul_comm (hT j i) (hS i j)
    _ = _ := Finset.sum_comm

omit [DecidableEq D] in
/-- The actual amplified vacuum is faithful on the matrix algebra over the
concrete closed field algebra. Empty D is included because its matrix algebra
is trivial; no faithfulness on all ambient bounded operators is claimed. -/
theorem eq_zero_of_entries_mem_wordFieldAlgebra_of_wordMatrixVacuumExpectation_star_mul_eq_zero
    (T : M) (hT : ∀ i j, T i j ∈ wordFieldAlgebra ι)
    (hZero : wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T) = 0) : T = 0 := by
  apply CStarMatrix.ext
  intro i j
  have : Nonempty D := ⟨j⟩
  have hcard : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hreal : (Fintype.card D : ℝ)⁻¹ *
      ∑ j, ∑ i, ‖T i j (wordVacuum ι)‖ ^ 2 = 0 := by
    have h := congrArg Complex.re hZero
    simpa only [wordMatrixVacuumExpectation_star_mul, Complex.ofReal_re, Complex.zero_re] using h
  have hsum := (mul_eq_zero.mp hreal).resolve_left (inv_ne_zero hcard)
  have hcol := (Finset.sum_eq_zero_iff_of_nonneg (fun col _ =>
    Finset.sum_nonneg (fun row _ => sq_nonneg ‖T row col (wordVacuum ι)‖))).mp
      hsum j (Finset.mem_univ j)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun row _ =>
    sq_nonneg ‖T row j (wordVacuum ι)‖)).mp hcol i (Finset.mem_univ i)
  exact eq_zero_of_mem_wordFieldAlgebra_of_apply_wordVacuum_eq_zero (hT i j)
    (norm_eq_zero.mp (sq_eq_zero_iff.mp hentry))

omit [DecidableEq D] in
/-- The actual squared L2 mass of every matrix entry is bounded by dimension
times the actual normalized amplified L2 mass. This is the squared native
form of the second inequality in source Lemma 4.6, with no norm premise. -/
theorem norm_entry_wordVacuum_sq_le_card_mul_wordMatrixVacuumExpectation_star_mul_re
    (T : M) (i j : D) :
    ‖T i j (wordVacuum ι)‖ ^ 2 ≤ (Fintype.card D : ℝ) *
      (wordMatrixVacuumExpectation (D := D) (ι := ι) (star T * T)).re := by
  have : Nonempty D := ⟨j⟩
  have hcard : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [wordMatrixVacuumExpectation_star_mul, Complex.ofReal_re, ← mul_assoc,
    mul_inv_cancel₀ hcard, one_mul]
  exact (Finset.single_le_sum (fun row _ => sq_nonneg ‖T row j (wordVacuum ι)‖)
    (Finset.mem_univ i)).trans
    (Finset.single_le_sum (fun col _ =>
      Finset.sum_nonneg (fun row _ => sq_nonneg ‖T row col (wordVacuum ι)‖))
      (Finset.mem_univ j))

end NLAlib
