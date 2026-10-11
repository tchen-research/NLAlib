/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyGradeProjections

set_option autoImplicit false

/-!
# Restricted heavy raising operator bound

Coordinate energy converts to the exact-grade raising-band norm bound.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The explicit squared energy is the sum of squared real coordinates.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def coordNormSq {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Explicit coordinate squared energy equals the Euclidean norm squared.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordNormSq_toLp {I : Type*} [Fintype I] (x : I → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = coordNormSq x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [coordNormSq]

/-- Generic finite-dimensional conversion from a coordinate energy estimate
to the rectangular matrix L2 operator norm.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_norm_le_of_coord_energy
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {A : Matrix I J ℝ} {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ x : J → ℝ,
      coordNormSq (Matrix.mulVec A x) ≤ C ^ 2 * coordNormSq x) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp x))‖ ≤ C * ‖x‖
  have hsq := henergy (WithLp.ofLp x)
  have hout := coordNormSq_toLp (Matrix.mulVec A (WithLp.ofLp x))
  have hin := coordNormSq_toLp (WithLp.ofLp x)
  have hx : ‖x‖ ^ 2 = coordNormSq (WithLp.ofLp x) := by
    simpa using hin
  rw [← hout, ← hx] at hsq
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2
    (Matrix.mulVec A (WithLp.ofLp x)))]

/-- Creation block-column energy is the sum of physical-row creation energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordNormSq_AUpStack (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    coordNormSq (Matrix.mulVec (AUpStack F) x) =
      ∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r) x) := by
  simp only [coordNormSq, fockNormSq, AUpStack, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

/-- Annihilation block-column energy is the sum of physical-row annihilation energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordNormSq_ADownStack (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    coordNormSq (Matrix.mulVec (ADownStack F) x) =
      ∑ r, fockNormSq (Matrix.mulVec (ADownMatrix F r) x) := by
  simp only [coordNormSq, fockNormSq, ADownStack, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

/-- Operator form of the first heavy-leg Loewner/energy estimate.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpStack_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖AUpStack (m := m) F * gradeProjection (d := d) (m := m) nu‖ ≤
      Real.sqrt nu := by
  apply matrix_norm_le_of_coord_energy (Real.sqrt_nonneg _)
  intro x
  rw [← Matrix.mulVec_mulVec, coordNormSq_AUpStack]
  calc
    _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := AUp_grade_energy F nu x
    _ = (Real.sqrt nu) ^ 2 * coordNormSq x := by
      rw [Real.sq_sqrt (Nat.cast_nonneg nu)]
      rfl

/-- Operator form of the second heavy-leg Loewner/energy estimate.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownStack_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖ADownStack (m := m) F * gradeProjection (d := d) (m := m) nu‖ ≤
      Real.sqrt nu := by
  apply matrix_norm_le_of_coord_energy (Real.sqrt_nonneg _)
  intro x
  rw [← Matrix.mulVec_mulVec, coordNormSq_ADownStack]
  calc
    _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := ADown_grade_energy F nu x
    _ = (Real.sqrt nu) ^ 2 * coordNormSq x := by
      rw [Real.sq_sqrt (Nat.cast_nonneg nu)]
      rfl

/-- The transpose of a heavy synthesis row is the matching annihilation analysis column.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem BUpMatrix_transpose (F : Frame n d) (r : Fin m) :
    (BUpMatrix F r).transpose = ADownMatrix F r := by
  ext σ inp
  simp only [BUpMatrix, ADownMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun K : FockOp m n ↦ K σ inp.2) (rUpAt_transpose r i)
  simpa [Matrix.transpose_apply] using h

/-- Transposing a real matrix preserves its Euclidean operator norm.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_transpose_real
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℝ) : ‖A.transpose‖ = ‖A‖ := by
  have hct : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [← hct, Matrix.l2_opNorm_conjTranspose]

/-- The row synthesis factor, restricted to middle grade `mu`, has norm at
most `√(mu+1)`.  This is the concrete `B_r B_r†` estimate.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem BUpStack_rowGradeProjection_norm (F : Frame n d) (mu : ℕ) :
    ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) mu‖ ≤
      Real.sqrt (mu + 1) := by
  let B := BUpStack (m := m) F
  let R := rowGradeProjection (m := m) (n := n) mu
  let A := ADownStack (m := m) F
  let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
  have ht : (B * R).transpose = R * A := by
    simp [B, R, A, Matrix.transpose_mul]
  calc
    ‖B * R‖ = ‖(B * R).transpose‖ := (norm_transpose_real (B * R)).symm
    _ = ‖R * A‖ := by rw [ht]
    _ = ‖R * A * P‖ := by
      rw [rowProjection_ADownStack_input (m := m) F mu]
    _ = ‖R * (A * P)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖R‖ * ‖A * P‖ := Matrix.l2_opNorm_mul R (A * P)
    _ ≤ 1 * ‖A * P‖ := by
      exact mul_le_mul_of_nonneg_right (rowGradeProjection_norm_le_one mu)
        (norm_nonneg _)
    _ ≤ 1 * Real.sqrt (mu + 1) := by
      have ha := ADownStack_gradeProjection_norm (m := m) F (mu + 1)
      have ha' : ‖A * P‖ ≤ Real.sqrt ((mu : ℝ) + 1) := by
        simpa [A, P, Nat.cast_add, Nat.cast_one] using ha
      exact mul_le_mul_of_nonneg_left ha' zero_le_one
    _ = Real.sqrt (mu + 1) := one_mul _

/-- The raising heavy band factors through the exact intermediate grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Hplus m (frameRows F) * gradeProjection (d := d) nu =
      (BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (AUpStack (m := m) F * gradeProjection (d := d) nu) := by
  rw [Hplus_eq_BUpStack_mul_AUpStack]
  have hins := rowProjection_AUpStack_gradeProjection (m := m) F nu
  calc
    (BUpStack (m := m) F * AUpStack (m := m) F) * gradeProjection (d := d) nu =
        BUpStack (m := m) F *
          (AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [Matrix.mul_assoc]
    _ = BUpStack (m := m) F *
        (rowGradeProjection (m := m) (n := n) (nu + 1) *
          AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The square-root product of grades separated by two is bounded by the intervening grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sqrt_mul_sqrt_add_two_le (nu : ℕ) :
    Real.sqrt (nu + 2) * Real.sqrt nu ≤ (nu : ℝ) + 1 := by
  have hnu : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  have hnu2 : 0 ≤ (nu : ℝ) + 2 := by positivity
  have hs0 : 0 ≤ Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare :
      (Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ)) ^ 2 ≤
        ((nu : ℝ) + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnu2, Real.sq_sqrt hnu]
    nlinarith
  nlinarith [sq_nonneg
    (((nu : ℝ) + 1) + Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ))]

/-- Concrete heavy-heavy `+2` component estimate required by the component
table.  No abstract component-bound premise occurs in the statement.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hplus_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hplus m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) + 1 := by
  rw [Hplus_grade_factor]
  calc
    _ ≤
        ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖AUpStack (m := m) F * gradeProjection (d := d) nu‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((nu : ℝ) + 2) * Real.sqrt nu := by
      have hb := BUpStack_rowGradeProjection_norm (m := m) F (nu + 1)
      have hb' :
          ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
            Real.sqrt ((nu : ℝ) + 2) := by
        (convert hb using 1; norm_num; ring)
      exact mul_le_mul hb' (AUpStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ (nu : ℝ) + 1 := sqrt_mul_sqrt_add_two_le nu

end

end NLAlib.SparseFock.HeavyBandsConcrete
