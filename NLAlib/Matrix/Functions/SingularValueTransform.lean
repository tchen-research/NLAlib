/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Spectral.SVD
import NLAlib.Matrix.Functions.RealCalculus

/-! # Singular-value transforms through the Gram functional calculus

The finite real spectrum permits arbitrary scalar functions. The Gram formula makes
SVD independence, including repeated and zero singular values, an equality theorem.
Source: Cai–Candès–Shen (2010), §2.1; Fessler–Nadakuditi (2024), §7.5.
Atlas: `singular-value-shrinkage-def`.
-/

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The rectangular singular-value transform `A h(AᴴA)`, where
`h(t) = φ(√t)/√t` uses total division at zero. For `φ(0)=0` this equals the
usual SVD formula; no continuity assumption on `φ` is needed on a finite spectrum.
Cai–Candès–Shen (2010), §2.1; Fessler–Nadakuditi (2024), §7.5.
atlas: singular-value-shrinkage-def (partial) -/
def singularValueTransform (φ : ℝ → ℝ) (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  A * cfc (fun t => φ (Real.sqrt t) / Real.sqrt t) (Aᴴ * A)

/-- Every full SVD implements the same intrinsic singular-value transform. The equality
covers zero singular values and arbitrary rotations inside repeated singular spaces.
Cai–Candès–Shen (2010), §2.1.
atlas: singular-value-shrinkage-def (partial) -/
theorem IsSVD.singularValueTransform_eq {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V)
    {φ : ℝ → ℝ} (hφ : φ 0 = 0) :
    singularValueTransform φ A =
      U * (rectDiag (fun i => φ (singularValues A i)) : Matrix (Fin p) (Fin q) 𝕜) * Vᴴ := by
  rw [singularValueTransform, h.conjTranspose_mul_self,
    cfc_isometric_conj V h.conjTranspose_mul_right h.mul_conjTranspose_right _ _
      (Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext; simp)), cfc_diagonal_ofReal]
  conv_lhs => lhs; rw [h.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, h.conjTranspose_mul_right, Matrix.one_mul]
  have hd : (rectDiag (singularValues A) : Matrix (Fin p) (Fin q) 𝕜) *
      Matrix.diagonal (fun j : Fin q =>
        ((φ (Real.sqrt (singularValues A j ^ 2)) /
          Real.sqrt (singularValues A j ^ 2) : ℝ) : 𝕜)) =
      rectDiag (fun i => φ (singularValues A i)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [rectDiag_apply_ofReal, Real.sqrt_sq (singularValues_nonneg A _)]
    split_ifs with hij
    · rw [hij]
      rw [← RCLike.ofReal_mul]
      congr 1
      by_cases hz : singularValues A j = 0
      · simp [hz, hφ]
      · field_simp
    · simp
  simpa only [Matrix.mul_assoc] using congrArg (fun M => U * M * Vᴴ) hd

/-- Singular-value transforms commute with left and right unitary multiplication.
The Gram definition proves this independently of singular-vector choices.
Cai–Candès–Shen (2010), §2.1.
atlas: singular-value-shrinkage-def (partial) -/
theorem singularValueTransform_unitary_mul (φ : ℝ → ℝ) (A : Matrix m n 𝕜)
    (U : Matrix m m 𝕜) (V : Matrix n n 𝕜)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    singularValueTransform φ (U * A * Vᴴ) = U * singularValueTransform φ A * Vᴴ := by
  have hGram : (U * A * Vᴴ)ᴴ * (U * A * Vᴴ) = V * (Aᴴ * A) * Vᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.conjTranspose_mul_self, Matrix.one_mul]
  rw [singularValueTransform, hGram,
    cfc_isometric_conj V hV (mul_eq_one_comm.mp hV.conjTranspose_mul_self) _ _
      (Matrix.isHermitian_conjTranspose_mul_self A), singularValueTransform]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hV.conjTranspose_mul_self, Matrix.one_mul]

/-- A nonnegative monotone scalar transform maps each singular value by the same rule.
Zero padding is preserved by `φ(0)=0`, including on empty matrix spaces. -/
theorem singularValues_singularValueTransform (A : Matrix m n 𝕜) {φ : ℝ → ℝ}
    (hφ : φ 0 = 0) (hφ0 : ∀ s, 0 ≤ s → 0 ≤ φ s)
    (hφmono : MonotoneOn φ (Set.Ici 0)) (i : ℕ) :
    singularValues (singularValueTransform φ A) i = φ (singularValues A i) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  by_cases hi : i < min (Fintype.card m) (Fintype.card n)
  · exact singularValues_eq_of_eq_mul_rectDiag_mul h.conjTranspose_mul_left
      h.conjTranspose_mul_right (fun j => hφ0 _ (singularValues_nonneg A j))
      (fun j k hjk => hφmono (singularValues_nonneg A k) (singularValues_nonneg A j)
        (singularValues_antitone A hjk)) (h.singularValueTransform_eq hφ) hi
  · rw [singularValues_eq_zero_of_min_le _ (not_lt.mp hi),
      singularValues_eq_zero_of_min_le A (not_lt.mp hi), hφ]

/-- Singular-value soft thresholding, with the scalar rule `(s-τ)₊`.
Cai–Candès–Shen (2010), equations (2.1)–(2.2).
atlas: singular-value-shrinkage-def (partial) -/
def singularValueSoftThreshold (τ : ℝ) (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  singularValueTransform (fun s => max (s - τ) 0) A


/-- Every SVD realizes the usual scalar soft-threshold rule, including at zero.
Cai–Candès–Shen (2010), equations (2.1)–(2.2).
atlas: singular-value-shrinkage-def (partial) -/
theorem IsSVD.singularValueSoftThreshold_eq {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    singularValueSoftThreshold τ A =
      U * (rectDiag (fun i => max (singularValues A i - τ) 0) :
        Matrix (Fin p) (Fin q) 𝕜) * Vᴴ := by
  exact h.singularValueTransform_eq (max_eq_right (sub_nonpos.mpr hτ))

/-- Soft thresholding maps every padded singular value to its positive-part cutoff. -/
theorem singularValues_singularValueSoftThreshold (A : Matrix m n 𝕜)
    {τ : ℝ} (hτ : 0 ≤ τ) (i : ℕ) :
    singularValues (singularValueSoftThreshold τ A) i = max (singularValues A i - τ) 0 := by
  exact singularValues_singularValueTransform A (φ := fun s => max (s - τ) 0)
    (max_eq_right (sub_nonpos.mpr hτ))
    (fun s _ => le_max_right _ _) (fun a _ b _ hab => max_le_max (sub_le_sub_right hab τ) le_rfl) i

/-- Threshold zero returns the input matrix, independently of its rank or SVD choices.
atlas: singular-value-shrinkage-def (partial) -/
@[simp] theorem singularValueSoftThreshold_zero (A : Matrix m n 𝕜) :
    singularValueSoftThreshold 0 A = A := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  rw [h.singularValueSoftThreshold_eq le_rfl]
  simpa only [sub_zero, max_eq_left (singularValues_nonneg A _)] using h.eq.symm

end NLAlib
