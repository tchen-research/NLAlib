/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyOccupationIdentity

set_option autoImplicit false

/-!
# Restricted heavy preserving operator bound

Explicit quadratic forms prove the sharp exact-grade preserving-band norm estimate.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Real quadratic form of a concrete finite matrix.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def quadratic {I : Type*} [Fintype I] (M : Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  dotProduct (Matrix.mulVec M x) x

/-- A real Gram quadratic form equals the squared coordinate energy of its matrix action.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_gram
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (A : Matrix I J ℝ) (x : J → ℝ) :
    quadratic (A.transpose * A) x =
      coordNormSq (Matrix.mulVec A x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec]
  calc
    dotProduct (Matrix.mulVec A.transpose (Matrix.mulVec A x)) x =
        dotProduct x (Matrix.mulVec A.transpose (Matrix.mulVec A x)) :=
      dotProduct_comm _ _
    _ = dotProduct (Matrix.mulVec A x) (Matrix.mulVec A x) :=
      Matrix.dotProduct_transpose_mulVec A x (Matrix.mulVec A x)
    _ = coordNormSq (Matrix.mulVec A x) := by
      simp [coordNormSq, dotProduct, pow_two]

/-- The creation diagonal quadratic form is the sum of same-site creation-analysis energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_DUp (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (DUp (m := m) F) x =
      ∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x) := by
  calc
    quadratic (DUp (m := m) F) x =
        ∑ r, ∑ i,
          quadratic ((AUpOne F r i).transpose * AUpOne F r i) x := by
      simp only [quadratic, DUp, Matrix.sum_mulVec, sum_dotProduct]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quadratic_gram]
      rfl

/-- The annihilation diagonal quadratic form is the sum of same-site annihilation-analysis energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_DDown (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (DDown (m := m) F) x =
      ∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x) := by
  calc
    quadratic (DDown (m := m) F) x =
        ∑ r, ∑ i,
          quadratic ((ADownOne F r i).transpose * ADownOne F r i) x := by
      simp only [quadratic, DDown, Matrix.sum_mulVec, sum_dotProduct]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quadratic_gram]
      rfl

/-- The preserving heavy quadratic form is its two analysis energies minus the diagonal corrections.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_Hzero (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (Hzero m (frameRows F)) x =
      coordNormSq (Matrix.mulVec (AUpStack (m := m) F) x) +
      coordNormSq (Matrix.mulVec (ADownStack (m := m) F) x) -
      (quadratic (DUp (m := m) F) x + quadratic (DDown (m := m) F) x) := by
  rw [Hzero_gram_sub_diagonal]
  calc
    quadratic
          ((AUpStack (m := m) F).transpose * AUpStack F +
            (ADownStack (m := m) F).transpose * ADownStack F -
            (DUp F + DDown F)) x =
        quadratic
            ((AUpStack (m := m) F).transpose * AUpStack F +
              (ADownStack (m := m) F).transpose * ADownStack F) x -
          quadratic (DUp F + DDown F) x := by
      simp [quadratic, Matrix.add_mulVec, Matrix.sub_mulVec,
        add_dotProduct, sub_dotProduct]
    _ =
        (quadratic ((AUpStack (m := m) F).transpose * AUpStack F) x +
          quadratic ((ADownStack (m := m) F).transpose * ADownStack F) x) -
        (quadratic (DUp F) x + quadratic (DDown F) x) := by
      simp [quadratic, Matrix.add_mulVec, add_dotProduct]
    _ = _ := by
      rw [quadratic_gram, quadratic_gram]

/-- Conjugating by the grade projection evaluates the quadratic form on the projected vector.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_gradeConj (M : FullOp d m n) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    quadratic (gradeProjection (d := d) nu * M * gradeProjection nu) x =
      quadratic M (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h := Matrix.dotProduct_transpose_mulVec
    (gradeProjection (d := d) (m := m) (n := n) nu)
    x (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))
  rw [gradeProjection_transpose] at h
  calc
    dotProduct
          (Matrix.mulVec (gradeProjection (d := d) nu)
            (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))) x =
        dotProduct x
          (Matrix.mulVec (gradeProjection (d := d) nu)
            (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))) :=
      dotProduct_comm _ _
    _ = dotProduct
          (Matrix.mulVec M (Matrix.mulVec (gradeProjection (d := d) nu) x))
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
      simpa only using h

/-- The grade-preserving heavy band is symmetric.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_transpose (F : Frame n d) :
    (Hzero m (frameRows F)).transpose = Hzero m (frameRows F) := by
  unfold Hzero wordSum
  rw [Matrix.transpose_add,
    DirectionalConcrete.transpose_physicalWordSum,
    DirectionalConcrete.transpose_physicalWordSum]
  rfl

/-- The heavy preserving band has grade shift zero.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0 (Hzero m (frameRows F)) := by
  apply FiniteHilbert.homogeneous_add
  · simpa [Hzero, wordSum, Word.degree, Leg.degree] using
      DirectionalConcrete.physicalWordSum_homogeneous
        (m := m) (frameRows F) (.rUp, .rDown)
  · simpa [Hzero, wordSum, Word.degree, Leg.degree] using
      DirectionalConcrete.physicalWordSum_homogeneous
        (m := m) (frameRows F) (.rDown, .rUp)

/-- The grade-zero heavy band preserves every exact-grade subspace.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_grade_factor (F : Frame n d) (nu : ℕ) :
    gradeProjection (d := d) nu * Hzero m (frameRows F) * gradeProjection nu =
      Hzero m (frameRows F) * gradeProjection nu := by
  apply FiniteHilbert.output_projection_of_homogeneous
    (Hzero_homogeneous (m := m) F) nu nu
  norm_num

/-- Explicit coordinate squared energy is nonnegative.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordNormSq_nonneg {I : Type*} [Fintype I] (x : I → ℝ) :
    0 ≤ coordNormSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Scalar Fock-pattern squared energy is nonnegative.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem fockNormSq_nonneg (x : Pattern m n → ℝ) :
    0 ≤ fockNormSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Sharp quadratic-form estimate for the concrete grade-zero heavy band,
after restriction to one exact total grade.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gradeConj_quadratic_abs_le (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    |quadratic
      (gradeProjection (d := d) nu * Hzero m (frameRows F) *
        gradeProjection nu) x| ≤
      2 * (nu : ℝ) * FiniteHilbert.normSq x := by
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  let y := Matrix.mulVec P x
  have hUp :
      coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) ≤
        (nu : ℝ) * FiniteHilbert.normSq x := by
    rw [coordNormSq_AUpStack]
    simpa only [P, y] using
      AUp_grade_energy (m := m) F nu x
  have hDown :
      coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) ≤
        (nu : ℝ) * FiniteHilbert.normSq x := by
    rw [coordNormSq_ADownStack]
    simpa only [P, y] using
      ADown_grade_energy (m := m) F nu x
  have hDiag :
      quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y ≤
        (nu : ℝ) * FiniteHilbert.normSq x := by
    calc
      quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y =
          (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) y)) +
          (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) y)) := by
        rw [quadratic_DUp, quadratic_DDown]
      _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber y p) :=
        Dcombined_energy_le_weighted F y
      _ = (nu : ℝ) * FiniteHilbert.normSq y := by
        simpa [P, y] using weighted_gradeProjection (d := d) (m := m) (n := n) nu x
      _ ≤ (nu : ℝ) * FiniteHilbert.normSq x := by
        exact mul_le_mul_of_nonneg_left
          (gradeProjection_normSq_le nu x) (Nat.cast_nonneg _)
  have hDiag0 :
      0 ≤ quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y := by
    rw [quadratic_DUp, quadratic_DDown]
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ fockNormSq_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ fockNormSq_nonneg _)
  have hUp0 :
      0 ≤ coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) :=
    coordNormSq_nonneg _
  have hDown0 :
      0 ≤ coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) :=
    coordNormSq_nonneg _
  have hNorm0 : 0 ≤ FiniteHilbert.normSq x := FiniteHilbert.normSq_nonneg x
  have hNu0 : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  rw [quadratic_gradeConj, quadratic_Hzero, abs_le]
  change
    -(2 * (nu : ℝ) * FiniteHilbert.normSq x) ≤
          coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) +
            coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) -
            (quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y) ∧
      coordNormSq (Matrix.mulVec (AUpStack (m := m) F) y) +
            coordNormSq (Matrix.mulVec (ADownStack (m := m) F) y) -
            (quadratic (DUp (m := m) F) y + quadratic (DDown (m := m) F) y) ≤
        2 * (nu : ℝ) * FiniteHilbert.normSq x
  constructor <;> nlinarith

/-- The Hilbert quadratic form equals the explicit real coordinate quadratic form.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadraticForm_eq_quadratic (M : FullOp d m n)
    (x : EuclideanSpace ℝ (Fin d × Pattern m n)) :
    MatrixTail.quadraticForm M x = quadratic M (WithLp.ofLp x) := by
  simp [MatrixTail.quadraticForm, quadratic, PiLp.inner_apply,
    dotProduct, mul_comm]

/-- Restricting the preserving heavy band to one grade gives a Hermitian matrix.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gradeConj_isHermitian (F : Frame n d) (nu : ℕ) :
    (gradeProjection (d := d) nu * Hzero m (frameRows F) *
      gradeProjection nu).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, gradeProjection_transpose,
    Hzero_transpose, Matrix.mul_assoc]

/-- Concrete heavy-heavy grade-zero component estimate required by the
component table.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hzero m (frameRows F) * gradeProjection (d := d) nu‖ ≤
      2 * (nu : ℝ) := by
  rw [← Hzero_grade_factor]
  apply (MatrixTail.opNorm_le_iff_quadraticForm _
    (Hzero_gradeConj_isHermitian (m := m) F nu) (2 * (nu : ℝ)) (by positivity)).2
  intro x
  rw [quadraticForm_eq_quadratic]
  have h := Hzero_gradeConj_quadratic_abs_le (m := m) F nu (WithLp.ofLp x)
  have hx : FiniteHilbert.normSq (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    symm
    simpa using FiniteHilbert.norm_toLp_sq (d := d) (m := m) (n := n)
      (WithLp.ofLp x)
  rwa [hx] at h

end

end NLAlib.SparseFock.HeavyBandsConcrete
