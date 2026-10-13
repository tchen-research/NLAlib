import NLAlib.Matrix.Perturbation.DavisKahanBounds
/-!
# Davis--Kahan bounds for arbitrary top spectral frames

The top-gap and population-gap spectral corollaries accept the supplied
invariant frames, including every valid choice at a tied perturbed boundary.
The population bound has no perturbation smallness hypothesis. Empty and full
widths and zero perturbations are explicit. Source: Davis--Kahan, Section 6;
Yu--Wang--Samworth (2015), Theorem 2. Supports `davis-kahan-sin-theta`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

open scoped Matrix.Norms.L2Operator in
/-- One-sided spectral separation gives both exact compressed residual bounds
for the invariant frames; Davis--Kahan, Section 6. -/
theorem sinePrincipalAngles_le_compressed_residual_div_of_one_sided_frames
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian)
    {Q Qhat : Matrix n k ℝ} {R : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hR : HasOrthonormalCols R) (hcomp : Qhat * Qhatᵀ + R * Rᵀ = 1)
    {L : Matrix k k ℝ} {M : Matrix r r ℝ}
    (hAQ : A * Q = Q * L) (hAR : (A + E) * R = R * M)
    {α δ : ℝ} (hδ : 0 < δ)
    (hmin : ∀ j, α ≤ (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j)
    (hmax : ∀ i,
      (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i ≤ α - δ) :
    specNorm (sinePrincipalAngles Q Qhat) ≤ specNorm (Rᵀ * E * Q) / δ ∧
      frobNorm (sinePrincipalAngles Q Qhat) ≤ frobNorm (Rᵀ * E * Q) / δ := by
  let hL := isHermitian_of_invariant_orthonormal_frame hA hQ hAQ
  let hM := isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR
  have hS := mul_specNorm_le_specNorm_sylvester_of_one_sided hM hL hδ hmax hmin (Rᵀ * Q)
  have hF := mul_frobNorm_le_frobNorm_sylvester hM hL hδ
    (by intro i j; have hi := hmax i; have hj := hmin j; rw [le_abs]; right; linarith)
    (Rᵀ * Q)
  rw [sylvester_complement_overlap_eq hA hE hAQ hAR hM] at hS hF
  have hswap : sinePrincipalAngles Q Qhat = sinePrincipalAngles Qhat Q := by
    unfold sinePrincipalAngles
    rw [principalAngles_comm]
  rw [← specNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp,
    ← hswap] at hS
  rw [← frobNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp,
    ← hswap] at hF
  exact ⟨(le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hS),
    (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hF)⟩

/-- Arbitrary equal-width orthonormal frames have zero sine matrices at empty
or full width; Stewart--Sun, Section I.5. -/
theorem sinePrincipalAngles_eq_zero_of_empty_or_full_frames
    {Q Qhat : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hwidth : Fintype.card k = 0 ∨ Fintype.card k = Fintype.card n) :
    sinePrincipalAngles Q Qhat = 0 := by
  rcases hwidth with hzero | hfull
  · ext i j
    have hi := i.isLt
    omega
  · exact sinePrincipalAngles_eq_zero_of_full_width hQ hQhat hfull

open scoped Matrix.Norms.L2Operator in
omit [Fintype k] [DecidableEq k] in
/-- Supplied top invariant frames satisfy the exact mixed-gap residual
bounds and unconditional population spectral bound, including tied perturbed
choices and zero perturbations; Davis--Kahan, Section 6, and Yu--Wang--Samworth,
Theorem 2. The spectral hypotheses describe the selected/complementary cluster
and contain no angle or desired norm inequality. -/
theorem davis_kahan_top_frame_bounds
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian)
    {j : ℕ} (hj0 : 0 < j) (hjN : j < Fintype.card n)
    {Q Qhat : Matrix n (Fin j) ℝ} {R : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hR : HasOrthonormalCols R) (hcomp : Qhat * Qhatᵀ + R * Rᵀ = 1)
    {L : Matrix (Fin j) (Fin j) ℝ} {M : Matrix r r ℝ}
    (hAQ : A * Q = Q * L) (hAR : (A + E) * R = R * M)
    (hmin : ∀ t, hA.eigenvalues₀ ⟨j - 1, by omega⟩ ≤
      (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues t)
    (hmax : ∀ t,
      (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues t ≤
        (hA.add hE).eigenvalues₀ ⟨j, hjN⟩) :
    let S := sinePrincipalAngles Q Qhat
    let δ := hA.eigenvalues₀ ⟨j - 1, by omega⟩ - (hA.add hE).eigenvalues₀ ⟨j, hjN⟩
    let g := hA.eigenvalues₀ ⟨j - 1, by omega⟩ - hA.eigenvalues₀ ⟨j, hjN⟩
    (0 < δ →
      specNorm S ≤ specNorm (Rᵀ * E * Q) / δ ∧
      specNorm (Rᵀ * E * Q) / δ ≤ specNorm (E * Q) / δ ∧
      specNorm (E * Q) / δ ≤ specNorm E / δ ∧
      frobNorm S ≤ frobNorm (Rᵀ * E * Q) / δ ∧
      frobNorm (Rᵀ * E * Q) / δ ≤ frobNorm (E * Q) / δ ∧
      frobNorm (E * Q) / δ ≤ min (Real.sqrt j * specNorm E) (frobNorm E) / δ) ∧
    (0 < g → specNorm S ≤ 2 * specNorm E / g) ∧
    (E = 0 → 0 < g → S = 0) := by
  dsimp only
  let S := sinePrincipalAngles Q Qhat
  let δ := hA.eigenvalues₀ ⟨j - 1, by omega⟩ - (hA.add hE).eigenvalues₀ ⟨j, hjN⟩
  let g := hA.eigenvalues₀ ⟨j - 1, by omega⟩ - hA.eigenvalues₀ ⟨j, hjN⟩
  have hmixed (hδ : 0 < δ) :
      specNorm S ≤ specNorm (Rᵀ * E * Q) / δ ∧
      frobNorm S ≤ frobNorm (Rᵀ * E * Q) / δ := by
    apply sinePrincipalAngles_le_compressed_residual_div_of_one_sided_frames
      hA hE hQ hQhat hR hcomp hAQ hAR hδ hmin
    intro t
    dsimp only [δ]
    have hh := hmax t
    linarith
  have hcompressed : specNorm (Rᵀ * E * Q) ≤ specNorm (E * Q) := by
    simpa only [← Matrix.mul_assoc] using specNorm_transpose_frame_mul_le hR (E * Q)
  have hpopulation (hg : 0 < g) : specNorm S ≤ 2 * specNorm E / g := by
    apply (le_div_iff₀ hg).2
    by_cases hsmall : specNorm E < g / 2
    · have hweyl := abs_eigenvalues₀_add_sub_le_specNorm hA hE ⟨j, hjN⟩
      rw [abs_le] at hweyl
      have hδ : 0 < δ := by dsimp only [δ, g] at *; linarith [hweyl.2]
      have hδg : g / 2 ≤ δ := by dsimp only [δ, g] at *; linarith [hweyl.2]
      have hmul := (le_div_iff₀ hδ).mp (hmixed hδ).1
      have hbound := hcompressed.trans (specNorm_mul_frame_le hQ E)
      have hS0 := specNorm_nonneg S
      nlinarith [mul_le_mul_of_nonneg_left hδg hS0]
    · have hS : specNorm S ≤ 1 := specNorm_sinePrincipalAngles_le_one hQ hQhat
      nlinarith [mul_le_mul_of_nonneg_right hS hg.le]
  refine ⟨?_, hpopulation, ?_⟩
  · intro hδ
    have hFcompressed : frobNorm (Rᵀ * E * Q) ≤ frobNorm (E * Q) := by
      simpa only [← Matrix.mul_assoc] using frobNorm_transpose_frame_mul_le hR (E * Q)
    have hFbound : frobNorm (E * Q) ≤ min (Real.sqrt j * specNorm E) (frobNorm E) :=
      le_min (by simpa only [Fintype.card_fin] using
        frobNorm_mul_frame_le_sqrt_card_mul_specNorm hQ E) (frobNorm_mul_frame_le hQ E)
    exact ⟨(hmixed hδ).1, div_le_div_of_nonneg_right hcompressed hδ.le,
      div_le_div_of_nonneg_right (specNorm_mul_frame_le hQ E) hδ.le,
      (hmixed hδ).2, div_le_div_of_nonneg_right hFcompressed hδ.le,
      div_le_div_of_nonneg_right hFbound hδ.le⟩
  · intro hzero hg
    have h := hpopulation hg
    rw [hzero, specNorm_zero, mul_zero, zero_div] at h
    apply norm_eq_zero.mp
    rw [← specNorm_eq_norm]
    exact le_antisymm h (specNorm_nonneg S)

open scoped Matrix.Norms.L2Operator in
/-- Every width-`j` invariant frame above the positive population
boundary gap has the canonical top spectral projector, independently of its
basis; Davis--Kahan, Section 6, at zero perturbation. -/
theorem mul_transpose_eq_topEigenframe_projector_of_lower_spectral_bound
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {j : ℕ}
    (hj0 : 0 < j) (hjN : j < Fintype.card n)
    (hg : 0 < hA.eigenvalues₀ ⟨j - 1, by omega⟩ - hA.eigenvalues₀ ⟨j, hjN⟩)
    {Q : Matrix n (Fin j) ℝ} (hQ : HasOrthonormalCols Q)
    {L : Matrix (Fin j) (Fin j) ℝ} (hAQ : A * Q = Q * L)
    (hmin : ∀ t, hA.eigenvalues₀ ⟨j - 1, by omega⟩ ≤
      (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues t) :
    Q * Qᵀ = topEigenframe hA hjN.le * (topEigenframe hA hjN.le)ᵀ := by
  let R := complementaryEigenframe hA hjN.le
  let e : Fin (Fintype.card n - j) → ℝ :=
    fun i => hA.eigenvalues₀ ⟨i.val + j, by omega⟩
  have hTop := hasOrthonormalCols_topEigenframe hA hjN.le
  have hR := hasOrthonormalCols_complementaryEigenframe hA hjN.le
  have hAR : (A + 0) * R = R * Matrix.diagonal e := by
    simpa only [add_zero] using mul_complementaryEigenframe_eq_mul_diagonal hA hjN.le
  have hmax : ∀ t,
      (isHermitian_of_invariant_orthonormal_frame (hA.add (Matrix.isHermitian_zero)) hR hAR).eigenvalues t ≤
        hA.eigenvalues₀ ⟨j - 1, by omega⟩ -
          (hA.eigenvalues₀ ⟨j - 1, by omega⟩ - hA.eigenvalues₀ ⟨j, hjN⟩) := by
    intro t
    obtain ⟨i, hi⟩ := exists_eq_eigenvalues_diagonal e t
    rw [← hi]
    have htail : e i ≤ hA.eigenvalues₀ ⟨j, hjN⟩ := by
      apply hA.eigenvalues₀_antitone
      change j ≤ i.val + j
      omega
    linarith
  have hs := (sinePrincipalAngles_le_compressed_residual_div_of_one_sided_frames
    hA Matrix.isHermitian_zero hQ hTop hR
    (topEigenframe_projector_add_complementary_eq_one hA hjN.le) hAQ hAR hg hmin hmax).1
  simp only [Matrix.mul_zero, Matrix.zero_mul, specNorm_zero, zero_div] at hs
  rw [specNorm_sinePrincipalAngles_eq_projector_distance hQ hTop] at hs
  have hz : Q * Qᵀ - topEigenframe hA hjN.le * (topEigenframe hA hjN.le)ᵀ = 0 := by
    apply norm_eq_zero.mp
    rw [← specNorm_eq_norm]
    exact le_antisymm hs (specNorm_nonneg _)
  exact sub_eq_zero.mp hz

open scoped Matrix.Norms.L2Operator in
/-- The sharp unconditional population Frobenius minimum accepts arbitrary
original top invariant frames and arbitrary perturbed top-trace maximizers,
including tied boundary choices; Yu--Wang--Samworth, Theorem 2. -/
theorem frobNorm_sinePrincipalAngles_le_min_div_population_gap_of_frames
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ}
    (hj0 : 0 < j) (hjN : j < Fintype.card n)
    (hg : 0 < hA.eigenvalues₀ ⟨j - 1, by omega⟩ - hA.eigenvalues₀ ⟨j, hjN⟩)
    {Q Qhat : Matrix n (Fin j) ℝ} (hQ : HasOrthonormalCols Q)
    (hQhat : HasOrthonormalCols Qhat)
    {L : Matrix (Fin j) (Fin j) ℝ} (hAQ : A * Q = Q * L)
    (hmin : ∀ t, hA.eigenvalues₀ ⟨j - 1, by omega⟩ ≤
      (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues t)
    (htop : (Qhatᵀ * (A + E) * Qhat).trace = eigenvaluePrefix (hA.add hE) j) :
    frobNorm (sinePrincipalAngles Q Qhat) ≤
      min (2 * Real.sqrt j * specNorm E) (Real.sqrt 2 * frobNorm E) /
        (hA.eigenvalues₀ ⟨j - 1, by omega⟩ - hA.eigenvalues₀ ⟨j, hjN⟩) := by
  have hproj := mul_transpose_eq_topEigenframe_projector_of_lower_spectral_bound
    hA hj0 hjN hg hQ hAQ hmin
  have hN := frobNorm_projector_distance_eq_sqrt_two_mul_sinePrincipalAngles hQ hQhat
  have hNTop := frobNorm_projector_distance_eq_sqrt_two_mul_sinePrincipalAngles
    (hasOrthonormalCols_topEigenframe hA hjN.le) hQhat
  rw [hproj] at hN
  have heq : frobNorm (sinePrincipalAngles Q Qhat) =
      frobNorm (sinePrincipalAngles (topEigenframe hA hjN.le) Qhat) := by
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [hN, hNTop]
  rw [heq]
  exact frobNorm_sinePrincipalAngles_le_min_div_population_gap hA hE hj0 hjN hg hQhat htop

end NLAlib
