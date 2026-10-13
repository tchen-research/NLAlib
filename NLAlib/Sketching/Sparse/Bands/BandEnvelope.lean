/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.BandAssembly
import NLAlib.Sketching.Sparse.Bands.Mixed.NormalizedBands
import Mathlib.Tactic


/-!
# Unconditional concrete uniform band envelope

This module closes Proposition `prop:band-envelope` from the source paper.
Every component estimate supplied to `ConcreteBandAssembly` is instantiated by
its concrete light, mixed, directional, or heavy proof; no operator-norm
hypothesis remains in the theorem statement.
-/

namespace NLAlib.SparseSketch

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n d : ℕ}

/-- The literal normalized `+2`, `0`, and `-2` bands all obey the common
`(3 + sqrt 2)` envelope.

Source: ported from `SparseFockFormal.ConcreteBandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem concrete_band_envelope
    (F : Frame n d) (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b)
    (shift : Shift) :
    ‖normalizedBand (s * b) F b shift * gradeProjection (d := d) nu‖ ≤
      bandConstant *
        (aTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
          bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
          cTerm (nu : ℝ) (s : ℝ)) := by
  have hb0 : 0 < b := by omega
  have hmNat : 1 ≤ s * b := Nat.mul_pos hs hb0
  have hm : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
  have hsR : (0 : ℝ) < (s : ℝ) := by positivity
  have ha : 0 ≤ aTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) :=
    aTerm_nonneg _ _ _
  have hbt : 0 ≤ bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) :=
    bTerm_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) hm
  have hc : 0 ≤ cTerm (nu : ℝ) (s : ℝ) :=
    cTerm_nonneg (Nat.cast_nonneg _) hsR
  have hdir : Frame.rows F =
      (fun i x ↦ F.u i x) := rfl
  cases shift with
  | plus =>
      apply plus_band_envelope_of_components F nu ha hc
      · rw [← hdir]
        exact Light.normalized_Lplus_gradeProjection_norm_le_envelope
          (m := s * b) F nu hmNat
      · rw [← hdir]
        exact Mixed.norm_normalized_mixed_plus_restricted_le
          F s b nu hs hb
      · rw [← hdir]
        exact Heavy.norm_normalized_Hplus_restricted_le
          F s b nu hs hb
      · exact hbt
  | zero =>
      apply zero_band_envelope_of_components F nu hc
      · rw [← hdir]
        exact Light.normalized_Lzero_gradeProjection_norm_le_envelope
          (m := s * b) F nu hmNat
      · rw [← hdir]
        exact Mixed.norm_normalized_mixed_zero_restricted_le
          F s b nu hs hb
      · rw [← hdir]
        exact Heavy.norm_normalized_Hzero_restricted_le
          F s b nu hs hb
      · exact hbt
      · exact ha
  | minus =>
      apply minus_band_envelope_of_components F nu ha hc
      · rw [← hdir]
        exact Light.normalized_Lminus_gradeProjection_norm_le_envelope
          (m := s * b) F nu hmNat
      · rw [← hdir]
        exact Mixed.norm_normalized_mixed_minus_restricted_le
          F s b nu hs hb
      · rw [← hdir]
        exact Heavy.norm_normalized_Hminus_restricted_le
          F s b nu hs hb
      · exact hbt

/-- Uniformize the concrete grade envelope over all grades reached by a word
of length `2q`.

Source: ported from `SparseFockFormal.ConcreteBandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem concrete_band_bound_le_beta
    (F : Frame n d) (s b q nu : ℕ) (hs : 0 < s) (hb : 1 < b)
    (hnu : nu ≤ 2 * q) (shift : Shift) :
    ‖normalizedBand (s * b) F b shift * gradeProjection (d := d) nu‖ ≤
      bandEnvelope d q (((s * b : ℕ) : ℝ)) (s : ℝ) := by
  have hm : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
  have hsR : (0 : ℝ) < (s : ℝ) := by positivity
  exact (concrete_band_envelope F s b nu hs hb shift).trans
    (grade_envelope_le_betaEnvelope hnu hm hsR)

end

end NLAlib.SparseSketch
