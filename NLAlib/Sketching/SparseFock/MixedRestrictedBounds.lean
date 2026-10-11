/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.MixedRowFactorization

set_option autoImplicit false

/-!
# Mixed exact-grade operator bounds

The literal raising, preserving, and adjoint mixed-band restricted norm estimates.
Ported from `SparseFockFormal.MixedBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.MixedBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands
  BandInventory NamedBands FiniteHilbert ConcreteLadder
  HeavyBandsConcrete LightBandsConcrete DirectionalConcrete
  DirectionalNormalized BandCoefficientBounds BandEnvelope
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000

variable {d m n : ℕ}

/-- Exact L2-norm scaling for the nested normalized mixed coefficient.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_mixed_term_eq {s b : ℕ}
    (A : FullOp d m n) (P : FullOp d m n) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • A)) * P‖ =
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * ‖A * P‖ := by
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / (((s * b : ℕ) : ℝ))),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Raw restricted norm of the concrete `X₊` factorization.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_Xplus_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Xplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
  have hC := LightBandsConcrete.CStack_restricted_norm (m := m) F (nu + 1)
  have hC' :
      ‖gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
        Real.sqrt ((d : ℝ) + (nu + 1 : ℕ)) := by
    convert hC using 1
  calc
    _ = ‖(gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
            LightBandsConcrete.CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
          (HeavyBandsConcrete.AUpStack (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu)‖ :=
      congrArg norm (Xplus_grade_factor (m := m) F nu)
    _ ≤
        ‖gradeProjection (d := d) (nu + 2) *
            LightBandsConcrete.CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖HeavyBandsConcrete.AUpStack (m := m) F *
            gradeProjection (d := d) nu‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((d : ℝ) + (nu + 1 : ℕ)) * Real.sqrt nu := by
      exact mul_le_mul
        hC'
        (HeavyBandsConcrete.AUpStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg nu)]
      push_cast
      ring

/-- Raw restricted norm of the concrete grade-preserving `X₀` band.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_Xzero_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Xzero m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  rcases nu with (_ | k)
  · rw [Xzero_gradeProjection_zero]
    simp
  · have hC := LightBandsConcrete.CStack_restricted_norm (m := m) F k
    have hC' :
        ‖gradeProjection (d := d) (m := m) (n := n) (k + 1) *
            LightBandsConcrete.CStack (m := m) F *
            HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k‖ ≤
          Real.sqrt ((d : ℝ) + ((k + 1 : ℕ) : ℝ)) := by
      calc
        _ ≤ Real.sqrt ((d : ℝ) + (k : ℝ)) := hC
        _ ≤ Real.sqrt ((d : ℝ) + ((k + 1 : ℕ) : ℝ)) := by
          apply Real.sqrt_le_sqrt
          norm_num
    calc
      _ = ‖(gradeProjection (d := d) (m := m) (n := n) (k + 1) *
              LightBandsConcrete.CStack (m := m) F *
              HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k) *
            (HeavyBandsConcrete.ADownStack (m := m) F *
              gradeProjection (d := d) (m := m) (n := n) (k + 1))‖ :=
        congrArg norm (Xzero_grade_factor_add_one (m := m) F k)
      _ ≤
          ‖gradeProjection (d := d) (k + 1) *
              LightBandsConcrete.CStack (m := m) F *
              HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k‖ *
            ‖HeavyBandsConcrete.ADownStack (m := m) F *
              gradeProjection (d := d) (k + 1)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ Real.sqrt ((d : ℝ) + ((k + 1 : ℕ) : ℝ)) *
          Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul hC'
          (HeavyBandsConcrete.ADownStack_gradeProjection_norm
            (m := m) F (k + 1))
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (((k + 1 : ℕ) : ℝ) *
          ((d : ℝ) + ((k + 1 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg (k + 1))]
        ring

/-- Exact shifted adjoint estimate for `X₊†`.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_XplusAdj_restricted_add_two_le (F : Frame n d) (k : ℕ) :
    ‖XplusAdj m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) (k + 2)‖ ≤
      Real.sqrt ((k : ℝ) * ((d : ℝ) + k + 1)) := by
  calc
    _ = ‖(XplusAdj m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) (k + 2)).transpose‖ := by
      exact (DirectionalNormalized.l2_norm_transpose _).symm
    _ = ‖gradeProjection (d := d) (k + 2) *
          Xplus m (DirectionalConcrete.frameRows F)‖ := by
      rw [Matrix.transpose_mul, transpose_XplusAdj, gradeProjection_transpose]
    _ = ‖Xplus m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) k‖ := by
      rw [DirectionalNormalized.gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Xplus_homogeneous (m := m) F) (k + 2) k (by norm_num)]
    _ ≤ _ := norm_Xplus_restricted_le (m := m) F k

/-- The mixed lowering adjoint vanishes on grade-zero input.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem XplusAdj_gradeProjection_zero (F : Frame n d) :
    XplusAdj m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (XplusAdj_homogeneous (m := m) F) 0
  intro mu
  omega

/-- The mixed lowering adjoint vanishes on grade-one input.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem XplusAdj_gradeProjection_one (F : Frame n d) :
    XplusAdj m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 1 = 0 := by
  apply FiniteHilbert.input_grade_vanishes_of_no_output
    (XplusAdj_homogeneous (m := m) F) 1
  intro mu
  omega

/-- Uniform same-grade form of the transpose mixed raising bound.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_XplusAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖XplusAdj m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
  rcases nu with (_ | _ | k)
  · rw [XplusAdj_gradeProjection_zero]
    simp
  · rw [XplusAdj_gradeProjection_one]
    simp
  · calc
      _ ≤ Real.sqrt ((k : ℝ) * ((d : ℝ) + k + 1)) :=
        norm_XplusAdj_restricted_add_two_le (m := m) F k
      _ ≤ Real.sqrt (((k + 2 : ℕ) : ℝ) *
          ((d : ℝ) + ((k + 2 : ℕ) : ℝ) + 1)) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d),
          (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The grade-preserving adjoint has exactly the same restricted norm.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_XzeroAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖XzeroAdj m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  calc
    _ = ‖(XzeroAdj m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) nu).transpose‖ := by
      exact (DirectionalNormalized.l2_norm_transpose _).symm
    _ = ‖gradeProjection (d := d) nu *
          Xzero m (DirectionalConcrete.frameRows F)‖ := by
      rw [Matrix.transpose_mul, transpose_XzeroAdj, gradeProjection_transpose]
    _ = ‖Xzero m (DirectionalConcrete.frameRows F) *
          gradeProjection (d := d) nu‖ := by
      rw [DirectionalNormalized.gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Xzero_homogeneous (m := m) F) nu nu (by norm_num)]
    _ ≤ _ := norm_Xzero_restricted_le (m := m) F nu

end

end NLAlib.SparseFock.MixedBandsConcrete
