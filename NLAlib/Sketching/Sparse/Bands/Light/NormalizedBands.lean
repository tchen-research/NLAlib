/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Light.MixedFactorization
import NLAlib.Sketching.Sparse.Bands.Directional.NormalizedBands

/-!
# Normalized light-band estimates

Transpose and grade identities yield the three normalized light-band envelope estimates.
Ported from `SparseFockFormal.LightBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseSketch.Light

open SparseSketch.Directional

noncomputable section

variable {d m n : ℕ}

/-- Transposing the light raising band gives the light lowering band.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lplus_transpose_eq_Lminus (F : Frame n d) :
    (Lplus m (Frame.rows F)).transpose =
      Lminus m (Frame.rows F) := by
  rw [Lplus, Lminus, wordSum, wordSum,
    transpose_physicalWordSum]
  rfl

/-- Transposing the light lowering band gives the light raising band.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lminus_transpose_eq_Lplus (F : Frame n d) :
    (Lminus m (Frame.rows F)).transpose =
      Lplus m (Frame.rows F) := by
  rw [← Lplus_transpose_eq_Lminus (m := m) F,
    Matrix.transpose_transpose]

/-- The light raising band has grade shift two.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lplus_homogeneous (F : Frame n d) :
    IsFullGradeShift 2
      (Lplus m (Frame.rows F)) := by
  simpa [Lplus, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous
      (m := m) (Frame.rows F) (.pUp, .pUp)

/-- The light lowering band has grade shift minus two.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lminus_homogeneous (F : Frame n d) :
    IsFullGradeShift (-2)
      (Lminus m (Frame.rows F)) := by
  simpa [Lminus, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous
      (m := m) (Frame.rows F) (.pDown, .pDown)

/-- The light-band envelope increases when its natural grade parameter increases.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem aTerm_add_bTerm_mono_nat {k nu m : ℕ} (d : ℕ)
    (hknu : k ≤ nu) (hm : 1 ≤ m) :
    aTerm d k m + bTerm d k m ≤
      aTerm d nu m + bTerm d nu m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hknuR : (k : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hknu
  have hfrac :
      ((d : ℝ) + (k : ℝ) + 1) / (m : ℝ) ≤
        ((d : ℝ) + (nu : ℝ) + 1) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) hmR.le
  have ha : aTerm d k m ≤ aTerm d nu m := by
    exact Real.sqrt_le_sqrt hfrac
  have hb : bTerm d k m ≤ bTerm d nu m := by
    exact hfrac
  exact add_le_add ha hb

/-- Raw restricted norm of the concrete light-light raising band.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lplus_gradeProjection_norm_le (F : Frame n d) (nu : ℕ) :
    ‖Lplus m (Frame.rows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) := by
  rw [Lplus_grade_factor]
  have hC := CStack_restricted_norm (m := m) F (nu + 1)
  have hC' :
      ‖gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          CStack (m := m) F *
          Heavy.rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
        Real.sqrt ((d : ℝ) + (nu : ℝ) + 1) := by
    (convert hC using 1; push_cast; ring)
  calc
    _ ≤
        ‖gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
            CStack (m := m) F *
            Heavy.rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖CreateAnalysisStack (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((d : ℝ) + (nu : ℝ) + 1) *
        Real.sqrt ((m : ℝ) + (nu : ℝ)) := by
      exact mul_le_mul hC'
        (CreateAnalysisStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) := by
      rw [Real.sqrt_mul (by positivity :
        0 ≤ (d : ℝ) + (nu : ℝ) + 1)]

/-- Exact normalized light raising estimate before its scalar envelope.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normalized_Lplus_gradeProjection_norm_le
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lplus m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) /
          (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hmR)]
  calc
    (1 / (m : ℝ)) *
        ‖Lplus m (Frame.rows F) *
          gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (1 / (m : ℝ)) * Real.sqrt
        (((d : ℝ) + (nu : ℝ) + 1) * ((m : ℝ) + (nu : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (Lplus_gradeProjection_norm_le (m := m) F nu) (by positivity)
    _ = _ := by ring

/-- Assembly-shaped light raising estimate, with exactly the `aTerm+bTerm`
right-hand side consumed by `ConcreteBandAssembly`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normalized_Lplus_gradeProjection_norm_le_envelope
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lplus m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      aTerm d nu m + bTerm d nu m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact (normalized_Lplus_gradeProjection_norm_le (m := m) F nu hm).trans
    (lightPlus_scalar_bound
      (Nat.cast_nonneg d) (Nat.cast_nonneg nu) hmR)

/-- Raw restricted norm of the concrete grade-preserving light-light band.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lzero_gradeProjection_norm_le (F : Frame n d) (nu : ℕ) :
    ‖Lzero m (Frame.rows F) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      3 * ((d : ℝ) + (nu : ℝ)) := by
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  have hG : ‖ghat (m := m) F * P‖ ≤ (d : ℝ) + (nu : ℝ) := by
    simpa [P] using ghat_gradeProjection_norm_le_all
      (m := m) F nu
  have hD : ‖D1 (m := m) F * P‖ ≤ (nu : ℝ) := by
    simpa [P] using D1_gradeProjection_norm (m := m) F nu
  have hH :
      ‖Hprime m (Frame.rows F) * P‖ ≤ (nu : ℝ) := by
    simpa [P] using norm_Hprime_restricted_le
      (m := m) F nu
  rw [Lzero_eq_ghat_sub_D1_add_Hprime, Matrix.add_mul, Matrix.sub_mul]
  change ‖ghat (m := m) F * P - D1 (m := m) F * P +
      Hprime m (Frame.rows F) * P‖ ≤ _
  calc
    _ ≤ ‖ghat (m := m) F * P - D1 (m := m) F * P‖ +
        ‖Hprime m (Frame.rows F) * P‖ := norm_add_le _ _
    _ ≤ (‖ghat (m := m) F * P‖ + ‖D1 (m := m) F * P‖) +
        ‖Hprime m (Frame.rows F) * P‖ := by
      exact add_le_add
        (norm_sub_le (ghat (m := m) F * P) (D1 (m := m) F * P))
        (le_refl ‖Hprime m (Frame.rows F) * P‖)
    _ ≤ (((d : ℝ) + (nu : ℝ)) + (nu : ℝ)) + (nu : ℝ) := by
      exact add_le_add (add_le_add hG hD) hH
    _ ≤ 3 * ((d : ℝ) + (nu : ℝ)) := by
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith

/-- Exact normalized grade-preserving light estimate before the assembly
envelope.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normalized_Lzero_gradeProjection_norm_le
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lzero m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      3 * ((d : ℝ) + (nu : ℝ)) / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hmR)]
  calc
    (1 / (m : ℝ)) *
        ‖Lzero m (Frame.rows F) *
          gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      (1 / (m : ℝ)) * (3 * ((d : ℝ) + (nu : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (Lzero_gradeProjection_norm_le (m := m) F nu) (by positivity)
    _ = _ := by ring

/-- Assembly-shaped grade-preserving light estimate, with exactly the
`3*bTerm` right-hand side consumed by `ConcreteBandAssembly`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normalized_Lzero_gradeProjection_norm_le_envelope
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lzero m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      3 * bTerm d nu m := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  calc
    _ ≤ 3 * ((d : ℝ) + (nu : ℝ)) / (m : ℝ) :=
      normalized_Lzero_gradeProjection_norm_le (m := m) F nu hm
    _ ≤ 3 * bTerm d nu m := by
      unfold bTerm
      calc
        3 * ((d : ℝ) + (nu : ℝ)) / (m : ℝ) ≤
            (3 * ((d : ℝ) + (nu : ℝ) + 1)) / (m : ℝ) := by
          exact div_le_div_of_nonneg_right (by linarith) hmR.le
        _ = 3 * (((d : ℝ) + (nu : ℝ) + 1) / (m : ℝ)) := by ring

/-- The light lowering band vanishes on grade-zero input.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lminus_gradeProjection_zero (F : Frame n d) :
    Lminus m (Frame.rows F) *
      gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  apply input_grade_vanishes_of_no_output
    (Lminus_homogeneous (m := m) F) 0
  intro mu
  omega

/-- The light lowering band vanishes on grade-one input.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lminus_gradeProjection_one (F : Frame n d) :
    Lminus m (Frame.rows F) *
      gradeProjection (d := d) (m := m) (n := n) 1 = 0 := by
  apply input_grade_vanishes_of_no_output
    (Lminus_homogeneous (m := m) F) 1
  intro mu
  omega

/-- Exact adjoint-grade transfer, including the normalized scalar.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normalized_Lminus_gradeProjection_norm_eq_shift
    (F : Frame n d) (k : ℕ) :
    ‖((1 / (m : ℝ)) • Lminus m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) (k + 2)‖ =
      ‖((1 / (m : ℝ)) • Lplus m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) k‖ := by
  have hshift :
      gradeProjection (d := d) (m := m) (n := n) (k + 2) *
          Lplus m (Frame.rows F) =
        Lplus m (Frame.rows F) *
          gradeProjection (d := d) (m := m) (n := n) k := by
    exact gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
      (Lplus_homogeneous (m := m) F) (k + 2) k (by norm_num)
  calc
    _ = ‖(((1 / (m : ℝ)) •
          Lminus m (Frame.rows F)) *
          gradeProjection (d := d) (m := m) (n := n) (k + 2)).transpose‖ := by
      exact (specNorm_transpose _).symm
    _ = _ := by
      rw [Matrix.transpose_mul, Matrix.transpose_smul,
        Lminus_transpose_eq_Lplus, gradeProjection_transpose,
        Matrix.mul_smul, hshift, Matrix.smul_mul]

/-- Assembly-shaped lowering estimate.  The two bottom grades vanish, while
all higher grades transfer exactly to the raising estimate two grades below.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem normalized_Lminus_gradeProjection_norm_le_envelope
    (F : Frame n d) (nu : ℕ) (hm : 1 ≤ m) :
    ‖((1 / (m : ℝ)) • Lminus m (Frame.rows F)) *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      aTerm d nu m + bTerm d nu m := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm
  have henv_nonneg (r : ℕ) :
      0 ≤ aTerm d r m + bTerm d r m :=
    add_nonneg (aTerm_nonneg _ _ _)
      (bTerm_nonneg
        (Nat.cast_nonneg d) (Nat.cast_nonneg r) hmR)
  rcases nu with (_ | _ | k)
  · rw [Matrix.smul_mul, Lminus_gradeProjection_zero]
    simpa using henv_nonneg 0
  · rw [Matrix.smul_mul, Lminus_gradeProjection_one]
    simpa using henv_nonneg 1
  · calc
      _ = ‖((1 / (m : ℝ)) • Lplus m
            (Frame.rows F)) *
          gradeProjection (d := d) (m := m) (n := n) k‖ := by
        exact normalized_Lminus_gradeProjection_norm_eq_shift (m := m) F k
      _ ≤ aTerm d k m + bTerm d k m :=
        normalized_Lplus_gradeProjection_norm_le_envelope (m := m) F k hm
      _ ≤ aTerm d (((k + 2 : ℕ) : ℝ)) m +
          bTerm d (((k + 2 : ℕ) : ℝ)) m :=
        aTerm_add_bTerm_mono_nat (k := k) (nu := k + 2) (m := m)
          d (by omega) hm
      _ = _ := by push_cast; ring

end

end NLAlib.SparseSketch.Light
