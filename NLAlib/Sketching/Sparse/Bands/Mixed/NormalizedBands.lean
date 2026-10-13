/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Mixed.RestrictedBounds

/-!
# Normalized mixed-band estimates

The explicit normalized mixed-band component bounds and their paper envelopes.
Ported from `SparseFockFormal.MixedBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch.Mixed

open SparseSketch.Heavy SparseSketch.Light SparseSketch.Directional
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000

variable {d m n : ℕ}

/-- The normalized mixed raising band satisfies its explicit exact-grade norm bound.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_Xplus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          Xplus (s * b) (Frame.rows F))) *
        gradeProjection (d := d) nu‖ ≤
      (1 / 2 : ℝ) *
        (bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖Xplus (s * b) (Frame.rows F) *
          gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (norm_Xplus_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ ≤ _ := by
      simpa [bTerm] using
        mixed_plus_absorb
          (d := d) (nu := nu) hs hb

/-- The normalized mixed lowering adjoint satisfies its explicit exact-grade norm bound.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_XplusAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          XplusAdj (s * b) (Frame.rows F))) *
        gradeProjection (d := d) nu‖ ≤
      (1 / 2 : ℝ) *
        (bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
          (nu : ℝ) / s) := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖XplusAdj (s * b) (Frame.rows F) *
          gradeProjection (d := d) nu‖ ≤
      Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (norm_XplusAdj_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ ≤ _ := by
      simpa [bTerm] using
        mixed_plus_absorb
          (d := d) (nu := nu) hs hb

/-- The normalized mixed preserving band satisfies its explicit exact-grade norm bound.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_Xzero_restricted_le (F : Frame n d)
    (s b nu : ℕ) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          Xzero (s * b) (Frame.rows F))) *
        gradeProjection (d := d) nu‖ ≤
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  rw [norm_normalized_directional_term_eq]
  exact mul_le_mul_of_nonneg_left
    (norm_Xzero_restricted_le (m := s * b) F nu)
    rho_div_stack_nonneg

/-- The normalized mixed preserving adjoint satisfies its explicit exact-grade norm bound.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_XzeroAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          XzeroAdj (s * b) (Frame.rows F))) *
        gradeProjection (d := d) nu‖ ≤
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) *
        Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu)) := by
  rw [norm_normalized_directional_term_eq]
  exact mul_le_mul_of_nonneg_left
    (norm_XzeroAdj_restricted_le (m := s * b) F nu)
    rho_div_stack_nonneg

/-- The two normalized `X₀` orientations satisfy the exact TeX allowance.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_Xzero_pair_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero (s * b) (Frame.rows F) +
            XzeroAdj (s * b) (Frame.rows F)))) *
        gradeProjection (d := d) nu‖ ≤
      ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (Frame.rows F) +
              XzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xzero (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XzeroAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xzero (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XzeroAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ 2 * (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          Real.sqrt ((nu : ℝ) * ((d : ℝ) + nu))) := by
      have h₁ := norm_normalized_Xzero_restricted_le F s b nu
      have h₂ := norm_normalized_XzeroAdj_restricted_le F s b nu
      linarith
    _ ≤ _ := mixed_zero_absorb hs hb

private theorem nu_div_s_le_cTerm {s nu : ℕ} (hs : 0 < s) :
    (nu : ℝ) / s ≤ cTerm (nu : ℝ) (s : ℝ) := by
  unfold cTerm
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Equation (mixed-plus), before replacing `nu/s` by the uniform envelope
term `(nu+1)/s`.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_mixed_plus_restricted_le_tex (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xplus (s * b) (Frame.rows F) +
            Yplus (s * b) (Frame.rows F)))) *
        gradeProjection (d := d) nu‖ ≤
      bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * ((nu : ℝ) / s) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xplus (s * b) (Frame.rows F) +
              Yplus (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xplus (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Yplus (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  have hX := norm_normalized_Xplus_restricted_le F s b nu hs hb
  have hY := norm_normalized_Yplus_restricted_le
    F s b nu hs hb
  have hB : 0 ≤ bTerm (d : ℝ) (nu : ℝ)
      (((s * b : ℕ) : ℝ)) :=
    bTerm_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Xplus (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            Yplus (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
            (nu : ℝ) / s) + (nu : ℝ) / s := add_le_add hX hY
    _ ≤ bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * ((nu : ℝ) / s) := by linarith

/-- Assembly-shaped normalized mixed `+2` estimate.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_mixed_plus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xplus (s * b) (Frame.rows F) +
            Yplus (s * b) (Frame.rows F)))) *
        gradeProjection (d := d) nu‖ ≤
      bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * cTerm (nu : ℝ) (s : ℝ) := by
  calc
    _ ≤ bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * ((nu : ℝ) / s) :=
      norm_normalized_mixed_plus_restricted_le_tex F s b nu hs hb
    _ ≤ _ := by
      have h := nu_div_s_le_cTerm (nu := nu) hs
      nlinarith

/-- Assembly-shaped normalized mixed `-2` estimate.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_mixed_minus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (XplusAdj (s * b) (Frame.rows F) +
            YplusAdj (s * b) (Frame.rows F)))) *
        gradeProjection (d := d) nu‖ ≤
      bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (3 / 2 : ℝ) * cTerm (nu : ℝ) (s : ℝ) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (XplusAdj (s * b) (Frame.rows F) +
              YplusAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XplusAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            YplusAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  have hX := norm_normalized_XplusAdj_restricted_le F s b nu hs hb
  have hY := norm_normalized_YplusAdj_restricted_le
    F s b nu hs hb
  have hB : 0 ≤ bTerm (d : ℝ) (nu : ℝ)
      (((s * b : ℕ) : ℝ)) :=
    bTerm_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)
  have hnu := nu_div_s_le_cTerm (nu := nu) hs
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            XplusAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            YplusAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
          (bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
            (nu : ℝ) / s) + (nu : ℝ) / s := add_le_add hX hY
    _ ≤ _ := by nlinarith

/-- Equation (mixed-zero), before the uniform-envelope relaxation.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_mixed_zero_restricted_le_tex (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero (s * b) (Frame.rows F) +
            XzeroAdj (s * b) (Frame.rows F) +
            Yzero (s * b) (Frame.rows F) +
            YzeroAdj (s * b) (Frame.rows F)))) *
        gradeProjection (d := d) nu‖ ≤
      ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) +
        (1 + Real.sqrt 2) * ((nu : ℝ) / s) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (Frame.rows F) +
              XzeroAdj (s * b) (Frame.rows F) +
              Yzero (s * b) (Frame.rows F) +
              YzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (Frame.rows F) +
              XzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Yzero (s * b) (Frame.rows F) +
              YzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
    abel
  rw [hsplit]
  have hX := norm_normalized_Xzero_pair_restricted_le F s b nu hs hb
  have hY := norm_normalized_Yzero_pair_restricted_le
    F s b nu hs hb
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Xzero (s * b) (Frame.rows F) +
              XzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Yzero (s * b) (Frame.rows F) +
              YzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ (((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) + (nu : ℝ) / s) +
        Real.sqrt 2 * ((nu : ℝ) / s) := add_le_add hX hY
    _ = _ := by ring

/-- Assembly-shaped normalized four-orientation grade-zero mixed bound.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_normalized_mixed_zero_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Xzero (s * b) (Frame.rows F) +
            XzeroAdj (s * b) (Frame.rows F) +
            Yzero (s * b) (Frame.rows F) +
            YzeroAdj (s * b) (Frame.rows F)))) *
        gradeProjection (d := d) nu‖ ≤
      bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) +
        (1 + Real.sqrt 2) * cTerm (nu : ℝ) (s : ℝ) := by
  calc
    _ ≤ ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) +
        (1 + Real.sqrt 2) * ((nu : ℝ) / s) :=
      norm_normalized_mixed_zero_restricted_le_tex F s b nu hs hb
    _ ≤ _ := by
      have hM : (0 : ℝ) < ((s * b : ℕ) : ℝ) := by positivity
      have hfirst :
          ((d : ℝ) + nu) / (((s * b : ℕ) : ℝ)) ≤
            bTerm (d : ℝ) (nu : ℝ) (((s * b : ℕ) : ℝ)) := by
        unfold bTerm
        exact div_le_div_of_nonneg_right (by linarith) hM.le
      have hnu := nu_div_s_le_cTerm (nu := nu) hs
      have hsqrt : 0 ≤ 1 + Real.sqrt 2 := by positivity
      exact add_le_add hfirst (mul_le_mul_of_nonneg_left hnu hsqrt)

end

end NLAlib.SparseSketch.Mixed
