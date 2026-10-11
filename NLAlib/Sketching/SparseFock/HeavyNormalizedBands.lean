/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyPreservingBound

set_option autoImplicit false

/-!
# Normalized heavy-band estimates

The three heavy-band estimates with the exact nested paper normalization.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Exact L2-norm scaling for the nested normalized heavy-heavy coefficient
used verbatim in the concrete band assembly.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_heavy_term_eq {s b : ℕ}
    (A : FullOp d m n) (P : FullOp d m n) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 • A)) * P‖ =
      (Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ))) * ‖A * P‖ := by
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / (((s * b : ℕ) : ℝ))),
    abs_of_nonneg (sq_nonneg _)]
  ring

/-- Normalized concrete heavy-heavy `+2` estimate in exactly the nested
scalar shape consumed by `ConcreteBandAssembly`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_Hplus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hplus (s * b) (frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  rw [norm_normalized_heavy_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ‖Hplus (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left
        (Hplus_gradeProjection_norm (m := s * b) F nu)
        BandCoefficientBounds.rho_sq_div_stack_nonneg
    _ ≤ (1 / (s : ℝ)) * ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right
        (BandCoefficientBounds.rho_sq_div_stack_le_inv_s hs hb) (by positivity)
    _ = BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
      simp [BandEnvelope.cTerm]
      ring

/-- Normalized concrete heavy-heavy grade-zero estimate in exactly the nested
scalar shape consumed by `ConcreteBandAssembly`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_Hzero_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hzero (s * b) (frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      2 * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  rw [norm_normalized_heavy_term_eq]
  have hraw :
      ‖Hzero (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
        2 * ((nu : ℝ) + 1) := by
    calc
      _ ≤ 2 * (nu : ℝ) := Hzero_gradeProjection_norm (m := s * b) F nu
      _ ≤ 2 * ((nu : ℝ) + 1) := by linarith
  calc
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ‖Hzero (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        (2 * ((nu : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left hraw
        BandCoefficientBounds.rho_sq_div_stack_nonneg
    _ ≤ (1 / (s : ℝ)) * (2 * ((nu : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_right
        (BandCoefficientBounds.rho_sq_div_stack_le_inv_s hs hb) (by positivity)
    _ = 2 * BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
      simp [BandEnvelope.cTerm]
      ring

/-- Normalized concrete heavy-heavy `-2` estimate in exactly the nested
scalar shape consumed by `ConcreteBandAssembly`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_Hminus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) ^ 2 •
          Hminus (s * b) (frameRows F))) *
        gradeProjection (d := d) nu‖ ≤
      BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
  rw [norm_normalized_heavy_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ‖Hminus (s * b) (frameRows F) * gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) ^ 2 / (((s * b : ℕ) : ℝ)) *
        ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left
        (Hminus_gradeProjection_norm (m := s * b) F nu)
        BandCoefficientBounds.rho_sq_div_stack_nonneg
    _ ≤ (1 / (s : ℝ)) * ((nu : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right
        (BandCoefficientBounds.rho_sq_div_stack_le_inv_s hs hb) (by positivity)
    _ = BandEnvelope.cTerm (nu : ℝ) (s : ℝ) := by
      simp [BandEnvelope.cTerm]
      ring

end

end NLAlib.SparseFock.HeavyBandsConcrete
