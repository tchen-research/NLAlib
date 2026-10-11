/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightBlockDecomposition

/-!
# The shared-leg norm bound on a fixed grade

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseFock.LightSectorConcrete
open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
variable {d m n ell : ℕ}

/-- An operator-norm bound gives the corresponding squared coordinate-energy bound.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem coordinateEnergy_mulVec_le_of_norm_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (z : I → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hA : ‖A‖ ≤ C) :
    coordinateEnergy (A.mulVec z) ≤ C ^ 2 * coordinateEnergy z := by
  let zE : EuclideanSpace ℝ I := WithLp.toLp 2 z
  let yE : EuclideanSpace ℝ I :=
    (EuclideanSpace.equiv I ℝ).symm (Matrix.mulVec A zE)
  have hop : ‖yE‖ ≤ ‖A‖ * ‖zE‖ := by
    simpa [yE] using Matrix.l2_opNorm_mulVec A zE
  have hopC : ‖yE‖ ≤ C * ‖zE‖ :=
    hop.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg zE))
  have hz : ‖zE‖ ^ 2 = coordinateEnergy z := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [zE, coordinateEnergy]
  have hy : ‖yE‖ ^ 2 = coordinateEnergy (A.mulVec z) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [yE, zE, coordinateEnergy, Matrix.mulVec]
  calc
    coordinateEnergy (A.mulVec z) = ‖yE‖ ^ 2 := hy.symm
    _ ≤ (C * ‖zE‖) ^ 2 := by
      nlinarith [norm_nonneg yE, mul_nonneg _hC (norm_nonneg zE)]
    _ = C ^ 2 * coordinateEnergy z := by rw [mul_pow, hz]

set_option maxHeartbeats 1000000 in
/-- The grade-restricted shared-leg operator has the dimension-plus-grade squared-energy bound.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_gradeProjection_normSq_le
    (F : Frame n d) (nu : ℕ) (hnu : 1 ≤ nu)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
        (Matrix.mulVec
          (ghat (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu) x) ≤
      ((d : ℝ) + (nu : ℝ) - 1) ^ 2 * FiniteHilbert.normSq x := by
  classical
  let C : ℝ := (d : ℝ) + (nu : ℝ) - 1
  have hnuR : (1 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hC : 0 ≤ C := by
    dsimp [C]
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  rw [normSq_eq_sum_blockFiber, normSq_eq_sum_blockFiber]
  calc
    (∑ q : FockBlockKey m n,
      coordinateEnergy
        (blockFiber
          (Matrix.mulVec
            (ghat (m := m) F *
              gradeProjection (d := d) (m := m) (n := n) nu) x) q)) =
        ∑ q : FockBlockKey m n,
          if blockGrade q = nu then
            coordinateEnergy
              (Matrix.mulVec (ghatBlock F q.1 q.2.1) (blockFiber x q))
          else 0 := by
            apply Finset.sum_congr rfl
            intro q _hq
            rw [blockFiber_ghat_gradeProjection_mulVec]
            by_cases hg : blockGrade q = nu <;>
              simp [hg, coordinateEnergy]
    _ ≤ ∑ q : FockBlockKey m n, C ^ 2 * coordinateEnergy (blockFiber x q) := by
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hg : blockGrade q = nu
      · rw [if_pos hg]
        by_cases hell : q.2.1 = 0
        · have hzero : ghatBlock F q.1 q.2.1 = 0 := by
            rw [hell]
            exact ghatBlock_zero_light F q.1
          rw [hzero]
          have hnonneg := mul_nonneg (sq_nonneg C)
            (coordinateEnergy_nonneg (blockFiber x q))
          simpa [coordinateEnergy] using hnonneg
        · have hellPos : 1 ≤ q.2.1 := Nat.one_le_iff_ne_zero.mpr hell
          have hellLe : q.2.1 ≤ nu := by
            dsimp [blockGrade] at hg
            omega
          exact coordinateEnergy_mulVec_le_of_norm_le
            (ghatBlock F q.1 q.2.1) (blockFiber x q) C hC
            (by
              simpa [C] using
                ghatBlock_norm_le_grade F q.1 q.2.1 nu hellPos hellLe)
      · rw [if_neg hg]
        exact mul_nonneg (sq_nonneg C) (coordinateEnergy_nonneg (blockFiber x q))
    _ = C ^ 2 * ∑ q : FockBlockKey m n, coordinateEnergy (blockFiber x q) := by
      rw [Finset.mul_sum]
    _ = ((d : ℝ) + (nu : ℝ) - 1) ^ 2 *
        ∑ q : FockBlockKey m n, coordinateEnergy (blockFiber x q) := rfl

/-- Sharp positive-grade Euclidean operator bound on the actual Pattern/Fock
operator.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_gradeProjection_norm_le
    (F : Frame n d) (nu : ℕ) (hnu : 1 ≤ nu) :
    ‖ghat (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (d : ℝ) + (nu : ℝ) - 1 := by
  have hnuR : (1 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hC : 0 ≤ (d : ℝ) + (nu : ℝ) - 1 := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  exact FiniteHilbert.norm_le_of_normSq_mulVec_le hC
    (ghat_gradeProjection_normSq_le F nu hnu)

/-- The shared-leg operator vanishes on an input pattern with no light sites.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_apply_eq_zero_of_input_light_card_zero
    (F : Frame n d) (out inp : Fin d × Pattern m n)
    (hzero : inp.2.light.card = 0) :
    ghat (m := m) F out inp = 0 := by
  classical
  rw [ghat_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  apply Finset.sum_eq_zero
  intro i _hi
  apply Finset.sum_eq_zero
  intro j _hj
  rw [pDagAt_mul_pAt_apply]
  have hnot : ¬(inp.2 (r, j) = .one ∧
      ((r, i) = (r, j) ∨ inp.2 (r, i) = .zero) ∧
      out.2 = lightMove inp.2 (r, j) (r, i)) := by
    intro hlegal
    have hmem : (r, j) ∈ inp.2.light := Pattern.mem_light.mpr hlegal.1
    have hpos : 0 < inp.2.light.card := Finset.card_pos.mpr ⟨(r, j), hmem⟩
    omega
  rw [if_neg hnot]
  ring

/-- The shared-leg operator has zero entries between different grades.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_apply_eq_zero_of_grade_ne
    (F : Frame n d) (out inp : Fin d × Pattern m n)
    (hne : out.2.grade ≠ inp.2.grade) :
    ghat (m := m) F out inp = 0 := by
  apply ghat_apply_eq_zero_of_block_ne
  by_contra hblock
  simp only [not_or, not_ne_iff] at hblock
  apply hne
  rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy,
    Pattern.grade_eq_card_light_add_two_mul_card_heavy,
    hblock.1, hblock.2]

/-- Left grade projection retains precisely the shared-leg entries with the selected output grade.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem gradeProjection_mul_ghat_apply
    (F : Frame n d) (nu : ℕ)
    (out inp : Fin d × Pattern m n) :
    (gradeProjection (d := d) (m := m) (n := n) nu *
      ghat (m := m) F) out inp =
      if out.2.grade = nu then ghat F out inp else 0 := by
  classical
  rw [gradeProjection, Matrix.diagonal_mul]
  by_cases h : out.2.grade = nu <;> simp [h]

/-- `G-hat` preserves every exact total grade, so it commutes with the actual
orthogonal grade projection.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gradeProjection_mul_ghat_eq_ghat_mul_gradeProjection
    (F : Frame n d) (nu : ℕ) :
    gradeProjection (d := d) (m := m) (n := n) nu * ghat F =
      ghat F * gradeProjection nu := by
  ext out inp
  rw [gradeProjection_mul_ghat_apply, ghat_mul_gradeProjection_apply]
  by_cases hout : out.2.grade = nu
  · by_cases hinp : inp.2.grade = nu
    · simp [hout, hinp]
    · have hne : out.2.grade ≠ inp.2.grade := by
        intro h
        exact hinp (h.symm.trans hout)
      simp [hout, hinp, ghat_apply_eq_zero_of_grade_ne F out inp hne]
  · by_cases hinp : inp.2.grade = nu
    · have hne : out.2.grade ≠ inp.2.grade := by
        intro h
        exact hout (h.trans hinp)
      simp [hout, hinp, ghat_apply_eq_zero_of_grade_ne F out inp hne]
    · simp [hout, hinp]

/-- The grade-restricted shared-leg operator is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem ghat_gradeProjection_transpose
    (F : Frame n d) (nu : ℕ) :
    (ghat (m := m) F *
      gradeProjection (d := d) (m := m) (n := n) nu).transpose =
      ghat F * gradeProjection nu := by
  rw [Matrix.transpose_mul, gradeProjection_transpose, ghat_transpose,
    gradeProjection_mul_ghat_eq_ghat_mul_gradeProjection]

/-- The grade-restricted shared-leg operator is Hermitian.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_gradeProjection_isHermitian
    (F : Frame n d) (nu : ℕ) :
    (ghat (m := m) F *
      gradeProjection (d := d) (m := m) (n := n) nu).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact ghat_gradeProjection_transpose F nu

/-- The exact grade-zero restriction vanishes: `G-hat` always annihilates one
light site before recreating one.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_gradeProjection_zero
    (F : Frame n d) :
    ghat (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  ext out inp
  rw [ghat_mul_gradeProjection_apply]
  by_cases hg : inp.2.grade = 0
  · rw [if_pos hg]
    apply ghat_apply_eq_zero_of_input_light_card_zero
    rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy] at hg
    omega
  · simp [hg]

/-- All-grade envelope used by downstream C-stack estimates.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_gradeProjection_norm_le_all
    (F : Frame n d) (nu : ℕ) :
    ‖ghat (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (d : ℝ) + (nu : ℝ) := by
  by_cases hnu : nu = 0
  · subst nu
    rw [ghat_gradeProjection_zero]
    simp
  · have hnuPos : 1 ≤ nu := Nat.one_le_iff_ne_zero.mpr hnu
    calc
      ‖ghat (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
          (d : ℝ) + (nu : ℝ) - 1 :=
        ghat_gradeProjection_norm_le F nu hnuPos
      _ ≤ (d : ℝ) + (nu : ℝ) := by linarith

/-- Every physical shared-leg block is symmetric.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem ghatBlock_transpose
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (ghatBlock F T ell).transpose = ghatBlock F T ell := by
  ext out inp
  have h := congrFun (congrFun (ghat_transpose (m := m) F)
    (out.1, out.2.1)) (inp.1, inp.2.1)
  simpa [ghatBlock, Matrix.transpose_apply] using h

/-- Every physical shared-leg block is Hermitian.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghatBlock_isHermitian
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (ghatBlock F T ell).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact ghatBlock_transpose F T ell

end NLAlib.SparseFock.LightSectorConcrete
