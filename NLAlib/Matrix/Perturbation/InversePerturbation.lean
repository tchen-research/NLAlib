import Mathlib.Analysis.SpecificLimits.Normed
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Spectral.Weyl
/-!
# Perturbation of the inverse and of the Moore–Penrose inverse

Exact-arithmetic perturbation theory for `A⁻¹` and `A⁺ = moorePenroseInverse A`, in the spectral
norm `specNorm` (and the Frobenius norm `frobNorm` where the bound is the same).

* Neumann series (Golub–Van Loan 2013, Lemma 2.3.3): for `‖F‖₂ < 1`, `1 - F` is invertible,
  `(1 - F)⁻¹ = ∑ₖ Fᵏ`, `‖(1 - F)⁻¹‖₂ ≤ 1 / (1 - ‖F‖₂)` and `‖(1 - F)⁻¹ - 1‖₂ ≤ ‖F‖₂ / (1 - ‖F‖₂)`.
* Inverse perturbation (Golub–Van Loan 2013, Thm 2.3.4): for invertible `A` and `‖A⁻¹E‖₂ < 1`,
  `A + E` is invertible, `‖(A + E)⁻¹‖₂ ≤ ‖A⁻¹‖₂ / (1 - ‖A⁻¹E‖₂)` and
  `‖(A + E)⁻¹ - A⁻¹‖ ≤ ‖A⁻¹‖₂² ‖E‖ / (1 - ‖A⁻¹E‖₂)` (spectral and Frobenius), with the
  corollaries under the cruder hypothesis `‖A⁻¹‖₂ ‖E‖₂ < 1`.
* Wedin's identity (Wedin 1973; Stewart–Sun 1990, §III.3) for `B = A + E` at every rank:
  `B⁺ - A⁺ = -B⁺ E A⁺ + B⁺ B⁺ᵀ Eᵀ (I - A A⁺) + (I - B⁺ B) Eᵀ A⁺ᵀ A⁺`, proved from the four Penrose
  identities; the resulting bound `‖B⁺ - A⁺‖₂ ≤ (‖B⁺‖‖A⁺‖ + ‖B⁺‖² + ‖A⁺‖²) ‖E‖₂`, hence the
  constant `3` form; and, as scaffolds, the sharp constant `(1 + √5)/2` (Stewart–Sun Thm III.3.8),
  in the general and the equal-rank form, and the projector bound. The equal-rank inverse-norm
  bound `‖B⁺‖₂ ≤ ‖A⁺‖₂ / (1 - ‖A⁺‖₂‖E‖₂)` is proved from Weyl's inequality.

Atlas: `inverse-perturbation`, `pseudoinverse-perturbation`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-! ### Neumann series -/

section Neumann

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `‖F‖₂ < 1` then `1 - F` is invertible. Golub–Van Loan 2013, Lemma 2.3.3 (first clause);
Mathlib's `Units.oneSub` in the normed ring of matrices with the `ℓ²` operator norm.
atlas: inverse-perturbation (partial) -/
theorem isUnit_one_sub_of_specNorm_lt_one {F : Matrix n n ℝ} (hF : specNorm F < 1) :
    IsUnit (1 - F) :=
  (Units.oneSub F hF).isUnit

/-- The Neumann series: if `‖F‖₂ < 1` then `(1 - F)⁻¹ = ∑ₖ Fᵏ`, the series converging (absolutely
in the operator norm). Golub–Van Loan 2013, Lemma 2.3.3; Mathlib's `geom_series_eq_inverse`.
atlas: inverse-perturbation (partial) -/
theorem inv_one_sub_eq_tsum_pow {F : Matrix n n ℝ} (hF : specNorm F < 1) :
    (1 - F)⁻¹ = ∑' k : ℕ, F ^ k := by
  rw [Matrix.nonsing_inv_eq_ringInverse, geom_series_eq_inverse F hF]

/-- The Neumann series as a `HasSum`: `∑ₖ Fᵏ` converges to `(1 - F)⁻¹` when `‖F‖₂ < 1`.
Golub–Van Loan 2013, Lemma 2.3.3. -/
theorem hasSum_pow_inv_one_sub {F : Matrix n n ℝ} (hF : specNorm F < 1) :
    HasSum (fun k : ℕ => F ^ k) (1 - F)⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact hasSum_geom_series_inverse F hF

/-- `(1 - F)⁻¹ = 1 + F (1 - F)⁻¹` for invertible `1 - F`; the algebraic step behind the Neumann
bounds. Golub–Van Loan 2013, proof of Lemma 2.3.3. -/
theorem inv_one_sub_eq_one_add_mul {F : Matrix n n ℝ} (h : IsUnit (1 - F)) :
    (1 - F)⁻¹ = 1 + F * (1 - F)⁻¹ := by
  have hd : IsUnit (1 - F).det := (Matrix.isUnit_iff_isUnit_det _).mp h
  have h1 : (1 - F) * (1 - F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  rw [Matrix.sub_mul, Matrix.one_mul] at h1
  calc (1 - F)⁻¹ = ((1 - F)⁻¹ - F * (1 - F)⁻¹) + F * (1 - F)⁻¹ := by abel
    _ = 1 + F * (1 - F)⁻¹ := by rw [h1]

/-- The Neumann norm bound `‖(1 - F)⁻¹‖₂ ≤ 1 / (1 - ‖F‖₂)` for `‖F‖₂ < 1`.
Golub–Van Loan 2013, Lemma 2.3.3 (bound (2.3.10)).
atlas: inverse-perturbation (partial) -/
theorem specNorm_inv_one_sub_le {F : Matrix n n ℝ} (hF : specNorm F < 1) :
    specNorm (1 - F)⁻¹ ≤ 1 / (1 - specNorm F) := by
  have hX := inv_one_sub_eq_one_add_mul (isUnit_one_sub_of_specNorm_lt_one hF)
  have hle : specNorm (1 - F)⁻¹ ≤ 1 + specNorm F * specNorm (1 - F)⁻¹ := by
    calc specNorm (1 - F)⁻¹ = specNorm (1 + F * (1 - F)⁻¹) := by rw [← hX]
      _ ≤ specNorm (1 : Matrix n n ℝ) + specNorm (F * (1 - F)⁻¹) := specNorm_add_le _ _
      _ ≤ 1 + specNorm F * specNorm (1 - F)⁻¹ :=
        add_le_add specNorm_one_le (specNorm_mul_le _ _)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The Neumann bound for the correction: `‖(1 - F)⁻¹ - 1‖₂ ≤ ‖F‖₂ / (1 - ‖F‖₂)` for
`‖F‖₂ < 1`, since `(1 - F)⁻¹ - 1 = F (1 - F)⁻¹`. Golub–Van Loan 2013, Lemma 2.3.3 (bound
(2.3.11)).
atlas: inverse-perturbation (partial) -/
theorem specNorm_inv_one_sub_sub_one_le {F : Matrix n n ℝ} (hF : specNorm F < 1) :
    specNorm ((1 - F)⁻¹ - 1) ≤ specNorm F / (1 - specNorm F) := by
  have hX := inv_one_sub_eq_one_add_mul (isUnit_one_sub_of_specNorm_lt_one hF)
  have he : (1 - F)⁻¹ - 1 = F * (1 - F)⁻¹ := by
    calc (1 - F)⁻¹ - 1 = (1 + F * (1 - F)⁻¹) - 1 := congrArg (· - 1) hX
      _ = F * (1 - F)⁻¹ := by abel
  rw [he]
  calc specNorm (F * (1 - F)⁻¹) ≤ specNorm F * specNorm (1 - F)⁻¹ := specNorm_mul_le _ _
    _ ≤ specNorm F * (1 / (1 - specNorm F)) :=
        mul_le_mul_of_nonneg_left (specNorm_inv_one_sub_le hF) (specNorm_nonneg F)
    _ = specNorm F / (1 - specNorm F) := by ring

end Neumann

/-! ### Perturbation of the inverse -/

section Inverse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `A` is invertible and `‖A⁻¹E‖₂ < 1` then `A + E` is invertible, being
`A (1 - (-A⁻¹E))`. Golub–Van Loan 2013, Thm 2.3.4 (first clause).
atlas: inverse-perturbation (partial) -/
theorem isUnit_add_of_specNorm_inv_mul_lt_one {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) : IsUnit (A + E) := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have h1 : IsUnit (1 - (-(A⁻¹ * E))) := by
    apply isUnit_one_sub_of_specNorm_lt_one
    rwa [specNorm_neg]
  have heq : A + E = A * (1 - (-(A⁻¹ * E))) := by
    rw [sub_neg_eq_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  rw [heq]
  exact hA.mul h1

/-- The resolvent identity `(A + E)⁻¹ - A⁻¹ = -(A + E)⁻¹ E A⁻¹` for invertible `A` and `A + E`.
Golub–Van Loan 2013, proof of Thm 2.3.4. -/
theorem inv_add_sub_inv_eq {A E : Matrix n n ℝ} (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    (A + E)⁻¹ - A⁻¹ = -((A + E)⁻¹ * E * A⁻¹) := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hd' : IsUnit (A + E).det := (Matrix.isUnit_iff_isUnit_det _).mp hAE
  calc (A + E)⁻¹ - A⁻¹ = (A + E)⁻¹ * A * A⁻¹ - (A + E)⁻¹ * (A + E) * A⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hd', Matrix.one_mul]
    _ = -((A + E)⁻¹ * E * A⁻¹) := by
        simp only [Matrix.mul_add, Matrix.add_mul]; abel

/-- Inverse-norm bound under perturbation: for invertible `A` and `‖A⁻¹E‖₂ < 1`,
`‖(A + E)⁻¹‖₂ ≤ ‖A⁻¹‖₂ / (1 - ‖A⁻¹E‖₂)`. Golub–Van Loan 2013, Thm 2.3.4; Stewart–Sun 1990,
§III.2.
atlas: inverse-perturbation (partial) -/
theorem specNorm_inv_add_le {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm (A + E)⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  set F : Matrix n n ℝ := -(A⁻¹ * E) with hFdef
  have hF : specNorm F < 1 := by rwa [hFdef, specNorm_neg]
  have heq : A + E = A * (1 - F) := by
    rw [hFdef, sub_neg_eq_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hinv : (A + E)⁻¹ = (1 - F)⁻¹ * A⁻¹ := by
    rw [heq, Matrix.mul_inv_rev]
  rw [hinv]
  calc specNorm ((1 - F)⁻¹ * A⁻¹) ≤ specNorm (1 - F)⁻¹ * specNorm A⁻¹ := specNorm_mul_le _ _
    _ ≤ 1 / (1 - specNorm F) * specNorm A⁻¹ :=
        mul_le_mul_of_nonneg_right (specNorm_inv_one_sub_le hF) (specNorm_nonneg _)
    _ = specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) := by rw [hFdef, specNorm_neg]; ring

/-- Perturbation of the inverse in the spectral norm: for invertible `A` and `‖A⁻¹E‖₂ < 1`,
`‖(A + E)⁻¹ - A⁻¹‖₂ ≤ ‖A⁻¹‖₂² ‖E‖₂ / (1 - ‖A⁻¹E‖₂)`. Golub–Van Loan 2013, Thm 2.3.4;
Stewart–Sun 1990, Thm III.2.5.
atlas: inverse-perturbation -/
theorem specNorm_inv_add_sub_inv_le {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤
      specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) := by
  have hAE := isUnit_add_of_specNorm_inv_mul_lt_one hA hE
  have hpos : 0 < 1 - specNorm (A⁻¹ * E) := by linarith
  rw [inv_add_sub_inv_eq hA hAE, specNorm_neg]
  calc specNorm ((A + E)⁻¹ * E * A⁻¹)
      ≤ specNorm (A + E)⁻¹ * specNorm E * specNorm A⁻¹ := by
        refine (specNorm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) * specNorm E * specNorm A⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (specNorm_inv_add_le hA hE)
          (specNorm_nonneg _)) (specNorm_nonneg _)
    _ = specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) := by
        field_simp

/-- Perturbation of the inverse in the Frobenius norm: for invertible `A` and `‖A⁻¹E‖₂ < 1`,
`‖(A + E)⁻¹ - A⁻¹‖_F ≤ ‖A⁻¹‖₂² ‖E‖_F / (1 - ‖A⁻¹E‖₂)`. Golub–Van Loan 2013, Thm 2.3.4 (the
proof is norm-agnostic once `‖XYZ‖_F ≤ ‖X‖₂‖Y‖_F‖Z‖₂`); Stewart–Sun 1990, §III.2.
atlas: inverse-perturbation -/
theorem frobNorm_inv_add_sub_inv_le {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) :
    frobNorm ((A + E)⁻¹ - A⁻¹) ≤
      specNorm A⁻¹ ^ 2 * frobNorm E / (1 - specNorm (A⁻¹ * E)) := by
  have hAE := isUnit_add_of_specNorm_inv_mul_lt_one hA hE
  have hpos : 0 < 1 - specNorm (A⁻¹ * E) := by linarith
  rw [inv_add_sub_inv_eq hA hAE, frobNorm_neg]
  calc frobNorm ((A + E)⁻¹ * E * A⁻¹)
      ≤ frobNorm ((A + E)⁻¹ * E) * specNorm A⁻¹ :=
        frobNorm_mul_le_frobNorm_mul_specNorm ((A + E)⁻¹ * E) A⁻¹
    _ ≤ specNorm (A + E)⁻¹ * frobNorm E * specNorm A⁻¹ :=
        mul_le_mul_of_nonneg_right (frobNorm_mul_le_specNorm_mul_frobNorm (A + E)⁻¹ E)
          (specNorm_nonneg _)
    _ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) * frobNorm E * specNorm A⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (specNorm_inv_add_le hA hE)
          (frobNorm_nonneg _)) (specNorm_nonneg _)
    _ = specNorm A⁻¹ ^ 2 * frobNorm E / (1 - specNorm (A⁻¹ * E)) := by
        field_simp

/-- The cruder hypothesis `‖A⁻¹‖₂ ‖E‖₂ < 1` implies `‖A⁻¹E‖₂ < 1`. -/
theorem specNorm_inv_mul_lt_one {A E : Matrix n n ℝ}
    (hE : specNorm A⁻¹ * specNorm E < 1) : specNorm (A⁻¹ * E) < 1 :=
  lt_of_le_of_lt (specNorm_mul_le _ _) hE

/-- Perturbation of the inverse under `‖A⁻¹‖₂ ‖E‖₂ < 1` (the form usually quoted):
`A + E` is invertible and `‖(A + E)⁻¹ - A⁻¹‖₂ ≤ ‖A⁻¹‖₂² ‖E‖₂ / (1 - ‖A⁻¹‖₂ ‖E‖₂)`.
Golub–Van Loan 2013, Thm 2.3.4 with `‖A⁻¹E‖ ≤ ‖A⁻¹‖‖E‖`; Higham 2002, Problem 6.14.
atlas: inverse-perturbation -/
theorem specNorm_inv_add_sub_inv_le_of_mul_lt_one {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm A⁻¹ * specNorm E < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤
      specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm A⁻¹ * specNorm E) := by
  have h1 := specNorm_inv_add_sub_inv_le hA (specNorm_inv_mul_lt_one hE)
  refine h1.trans ?_
  have hle : specNorm (A⁻¹ * E) ≤ specNorm A⁻¹ * specNorm E := specNorm_mul_le _ _
  have hpos : 0 < 1 - specNorm A⁻¹ * specNorm E := by linarith
  apply div_le_div_of_nonneg_left _ hpos (by linarith)
  exact mul_nonneg (sq_nonneg _) (specNorm_nonneg _)

/-- Inverse-norm bound under `‖A⁻¹‖₂ ‖E‖₂ < 1`:
`‖(A + E)⁻¹‖₂ ≤ ‖A⁻¹‖₂ / (1 - ‖A⁻¹‖₂ ‖E‖₂)`. Golub–Van Loan 2013, Thm 2.3.4.
atlas: inverse-perturbation (partial) -/
theorem specNorm_inv_add_le_of_mul_lt_one {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm A⁻¹ * specNorm E < 1) :
    specNorm (A + E)⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm E) := by
  refine (specNorm_inv_add_le hA (specNorm_inv_mul_lt_one hE)).trans ?_
  have hle : specNorm (A⁻¹ * E) ≤ specNorm A⁻¹ * specNorm E := specNorm_mul_le _ _
  have hpos : 0 < 1 - specNorm A⁻¹ * specNorm E := by linarith
  exact div_le_div_of_nonneg_left (specNorm_nonneg _) hpos (by linarith)

end Inverse

/-! ### Perturbation of the Moore–Penrose inverse -/

section MoorePenrose

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The column-space projector annihilates on the left of its complement:
`Aᵀ (I - A A⁺) = 0` for any Moore–Penrose pair. Stewart–Sun 1990, §III.1. -/
theorem IsMoorePenroseInverse.transpose_mul_one_sub_mul_eq_zero [DecidableEq m]
    {A : Matrix m n ℝ} {A' : Matrix n m ℝ} (h : IsMoorePenroseInverse A A') :
    Aᵀ * (1 - A * A') = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← h.transpose_mul_eq, ← Matrix.transpose_mul,
    h.mul_mul_eq, sub_self]

/-- The row-space complement annihilates `Aᵀ` on the left: `(I - A⁺ A) Aᵀ = 0` for any
Moore–Penrose pair. Stewart–Sun 1990, §III.1. -/
theorem IsMoorePenroseInverse.one_sub_inv_mul_mul_transpose_eq_zero [DecidableEq n]
    {A : Matrix m n ℝ} {A' : Matrix n m ℝ} (h : IsMoorePenroseInverse A A') :
    (1 - A' * A) * Aᵀ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, ← h.transpose_inv_mul_eq, ← Matrix.transpose_mul,
    ← Matrix.mul_assoc, h.mul_mul_eq, sub_self]

/-- **Wedin's identity** for Moore–Penrose pairs `(A, A')`, `(B, B')` with `E = B - A`, at
every rank: `B' - A' = -B' E A' + B' B'ᵀ Eᵀ (I - A A') + (I - B' B) Eᵀ A'ᵀ A'`.
Wedin 1973, Thm 4.1 (proof); Stewart–Sun 1990, §III.3. Proof: `B' - A' = -B'(B - A)A' +
B'(I - AA') - (I - B'B)A'`, then `B' = B'B'ᵀBᵀ`, `Aᵀ(I - AA') = 0`, `A' = AᵀA'ᵀA'`,
`(I - B'B)Bᵀ = 0`. -/
theorem IsMoorePenroseInverse.sub_eq [DecidableEq m] [DecidableEq n]
    {A B : Matrix m n ℝ} {A' B' : Matrix n m ℝ} (hA : IsMoorePenroseInverse A A')
    (hB : IsMoorePenroseInverse B B') :
    B' - A' = -(B' * (B - A) * A') + B' * B'ᵀ * (B - A)ᵀ * (1 - A * A') +
      (1 - B' * B) * (B - A)ᵀ * A'ᵀ * A' := by
  have h0 : B' - A' = -(B' * (B - A) * A') + B' * (1 - A * A') - (1 - B' * B) * A' := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  have hB' : B' = B' * B'ᵀ * Bᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hB.transpose_mul_eq, ← Matrix.mul_assoc,
      hB.inv_mul_inv_eq]
  have hA' : A' = Aᵀ * A'ᵀ * A' := by
    rw [← Matrix.transpose_mul, hA.transpose_inv_mul_eq, hA.inv_mul_inv_eq]
  have h2 : B' * (1 - A * A') = B' * B'ᵀ * (B - A)ᵀ * (1 - A * A') := by
    have hz := hA.transpose_mul_one_sub_mul_eq_zero
    have hBt : Bᵀ = (B - A)ᵀ + Aᵀ := by rw [Matrix.transpose_sub, sub_add_cancel]
    calc B' * (1 - A * A') = B' * B'ᵀ * Bᵀ * (1 - A * A') := by rw [← hB']
      _ = B' * B'ᵀ * (B - A)ᵀ * (1 - A * A') + B' * B'ᵀ * (Aᵀ * (1 - A * A')) := by
          rw [hBt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc (B' * B'ᵀ) Aᵀ]
      _ = B' * B'ᵀ * (B - A)ᵀ * (1 - A * A') := by rw [hz, Matrix.mul_zero, add_zero]
  have h3 : (1 - B' * B) * A' = -((1 - B' * B) * (B - A)ᵀ * A'ᵀ * A') := by
    have hz := hB.one_sub_inv_mul_mul_transpose_eq_zero
    have hAt : Aᵀ = Bᵀ - (B - A)ᵀ := by rw [Matrix.transpose_sub, sub_sub_cancel]
    calc (1 - B' * B) * A' = (1 - B' * B) * Aᵀ * A'ᵀ * A' := by
          rw [Matrix.mul_assoc (1 - B' * B) Aᵀ, Matrix.mul_assoc (1 - B' * B), ← hA']
      _ = (1 - B' * B) * Bᵀ * A'ᵀ * A' - (1 - B' * B) * (B - A)ᵀ * A'ᵀ * A' := by
          rw [hAt, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
      _ = -((1 - B' * B) * (B - A)ᵀ * A'ᵀ * A') := by
          rw [hz, Matrix.zero_mul, Matrix.zero_mul, zero_sub]
  rw [h0, h2, h3, sub_neg_eq_add]

/-- **Wedin's identity** for the Moore–Penrose inverse of `B = A + E`:
`(A + E)⁺ - A⁺ = -(A + E)⁺ E A⁺ + (A + E)⁺ (A + E)⁺ᵀ Eᵀ (I - A A⁺)
  + (I - (A + E)⁺ (A + E)) Eᵀ A⁺ᵀ A⁺`,
with no rank assumption. Wedin 1973, Thm 4.1 (proof); Stewart–Sun 1990, §III.3.
atlas: pseudoinverse-perturbation (partial) -/
theorem moorePenroseInverse_add_sub_moorePenroseInverse [DecidableEq m] [DecidableEq n]
    (A E : Matrix m n ℝ) :
    moorePenroseInverse (A + E) - moorePenroseInverse A =
      -(moorePenroseInverse (A + E) * E * moorePenroseInverse A) +
        moorePenroseInverse (A + E) * (moorePenroseInverse (A + E))ᵀ * Eᵀ *
          (1 - A * moorePenroseInverse A) +
        (1 - moorePenroseInverse (A + E) * (A + E)) * Eᵀ * (moorePenroseInverse A)ᵀ *
          moorePenroseInverse A := by
  have h := (isMoorePenroseInverse A).sub_eq (isMoorePenroseInverse (A + E))
  rwa [add_sub_cancel_left] at h

/-- `‖I - A A'‖₂ ≤ 1` for a Moore–Penrose pair: `I - A A'` is a symmetric idempotent. -/
theorem IsMoorePenroseInverse.specNorm_one_sub_mul_le [DecidableEq m]
    {A : Matrix m n ℝ} {A' : Matrix n m ℝ} (h : IsMoorePenroseInverse A A') :
    specNorm (1 - A * A') ≤ 1 := by
  apply specNorm_le_one_of_isSymm_of_isIdempotentElem
  · change (1 - A * A')ᵀ = 1 - A * A'
    rw [Matrix.transpose_sub, Matrix.transpose_one, h.transpose_mul_eq]
  · exact h.mul_isIdempotentElem.one_sub

/-- `‖I - A' A‖₂ ≤ 1` for a Moore–Penrose pair: `I - A' A` is a symmetric idempotent. -/
theorem IsMoorePenroseInverse.specNorm_one_sub_inv_mul_le [DecidableEq n]
    {A : Matrix m n ℝ} {A' : Matrix n m ℝ} (h : IsMoorePenroseInverse A A') :
    specNorm (1 - A' * A) ≤ 1 :=
  h.swap.specNorm_one_sub_mul_le

/-- Pseudoinverse perturbation bound at every rank, from Wedin's identity term by term:
`‖(A + E)⁺ - A⁺‖₂ ≤ (‖(A + E)⁺‖₂ ‖A⁺‖₂ + ‖(A + E)⁺‖₂² + ‖A⁺‖₂²) ‖E‖₂`.
Wedin 1973, §4; Stewart–Sun 1990, Thm III.3.8 with the crude constant (each of the three
terms of the identity is bounded separately; `‖I - AA⁺‖, ‖I - B⁺B‖ ≤ 1`).
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_moorePenroseInverse_add_sub_le [DecidableEq m] [DecidableEq n]
    (A E : Matrix m n ℝ) :
    specNorm (moorePenroseInverse (A + E) - moorePenroseInverse A) ≤
      (specNorm (moorePenroseInverse (A + E)) * specNorm (moorePenroseInverse A) +
        specNorm (moorePenroseInverse (A + E)) ^ 2 + specNorm (moorePenroseInverse A) ^ 2) *
        specNorm E := by
  set A' := moorePenroseInverse A
  set B' := moorePenroseInverse (A + E)
  have hA := isMoorePenroseInverse A
  have hB := isMoorePenroseInverse (A + E)
  have hP := hA.specNorm_one_sub_mul_le
  have hQ := hB.specNorm_one_sub_inv_mul_le
  have ha := specNorm_nonneg A'
  have hb := specNorm_nonneg B'
  have he := specNorm_nonneg E
  rw [moorePenroseInverse_add_sub_moorePenroseInverse]
  have t1 : specNorm (-(B' * E * A')) ≤ specNorm B' * specNorm A' * specNorm E := by
    rw [specNorm_neg]
    calc specNorm (B' * E * A') ≤ specNorm (B' * E) * specNorm A' := specNorm_mul_le _ _
      _ ≤ specNorm B' * specNorm E * specNorm A' :=
          mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) ha
      _ = _ := by ring
  have t2 : specNorm (B' * B'ᵀ * Eᵀ * (1 - A * A')) ≤ specNorm B' ^ 2 * specNorm E := by
    have h0 := specNorm_nonneg (B' * B'ᵀ * Eᵀ)
    calc specNorm (B' * B'ᵀ * Eᵀ * (1 - A * A'))
        ≤ specNorm (B' * B'ᵀ * Eᵀ) * specNorm (1 - A * A') := specNorm_mul_le _ _
      _ ≤ specNorm (B' * B'ᵀ * Eᵀ) := by nlinarith
      _ ≤ specNorm (B' * B'ᵀ) * specNorm Eᵀ := specNorm_mul_le _ _
      _ ≤ specNorm B' * specNorm B'ᵀ * specNorm Eᵀ :=
          mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
      _ = specNorm B' ^ 2 * specNorm E := by
          rw [specNorm_transpose, specNorm_transpose]; ring
  have t3 : specNorm ((1 - B' * (A + E)) * Eᵀ * A'ᵀ * A') ≤ specNorm A' ^ 2 * specNorm E := by
    have hc : 0 ≤ specNorm Eᵀ * specNorm A'ᵀ * specNorm A' :=
      mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) ha
    calc specNorm ((1 - B' * (A + E)) * Eᵀ * A'ᵀ * A')
        ≤ specNorm ((1 - B' * (A + E)) * Eᵀ * A'ᵀ) * specNorm A' := specNorm_mul_le _ _
      _ ≤ specNorm ((1 - B' * (A + E)) * Eᵀ) * specNorm A'ᵀ * specNorm A' :=
          mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) ha
      _ ≤ specNorm (1 - B' * (A + E)) * specNorm Eᵀ * specNorm A'ᵀ * specNorm A' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _)) ha
      _ = specNorm (1 - B' * (A + E)) * (specNorm Eᵀ * specNorm A'ᵀ * specNorm A') := by ring
      _ ≤ 1 * (specNorm Eᵀ * specNorm A'ᵀ * specNorm A') := mul_le_mul_of_nonneg_right hQ hc
      _ = specNorm A' ^ 2 * specNorm E := by
          rw [specNorm_transpose, specNorm_transpose]; ring
  calc _ ≤ specNorm (-(B' * E * A') + B' * B'ᵀ * Eᵀ * (1 - A * A')) +
        specNorm ((1 - B' * (A + E)) * Eᵀ * A'ᵀ * A') := specNorm_add_le _ _
    _ ≤ specNorm (-(B' * E * A')) + specNorm (B' * B'ᵀ * Eᵀ * (1 - A * A')) +
        specNorm ((1 - B' * (A + E)) * Eᵀ * A'ᵀ * A') :=
          add_le_add_left (specNorm_add_le _ _) _
    _ ≤ specNorm B' * specNorm A' * specNorm E + specNorm B' ^ 2 * specNorm E +
        specNorm A' ^ 2 * specNorm E := add_le_add (add_le_add t1 t2) t3
    _ = _ := by ring

/-- Pseudoinverse perturbation bound with the constant `3` and no rank assumption:
`‖(A + E)⁺ - A⁺‖₂ ≤ 3 max(‖A⁺‖₂², ‖(A + E)⁺‖₂²) ‖E‖₂`. Wedin 1973, Thm 4.1 with `μ = 3`;
Stewart–Sun 1990, Thm III.3.8 (the constant for a general unitarily invariant norm; the sharp
spectral constant `(1 + √5)/2` is `specNorm_moorePenroseInverse_add_sub_le_goldenRatio_mul_max`).
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_moorePenroseInverse_add_sub_le_three_mul_max [DecidableEq m] [DecidableEq n]
    (A E : Matrix m n ℝ) :
    specNorm (moorePenroseInverse (A + E) - moorePenroseInverse A) ≤
      3 * max (specNorm (moorePenroseInverse A) ^ 2)
        (specNorm (moorePenroseInverse (A + E)) ^ 2) * specNorm E := by
  refine (specNorm_moorePenroseInverse_add_sub_le A E).trans ?_
  set a := specNorm (moorePenroseInverse A)
  set b := specNorm (moorePenroseInverse (A + E))
  have ha : 0 ≤ a := specNorm_nonneg _
  have hb : 0 ≤ b := specNorm_nonneg _
  apply mul_le_mul_of_nonneg_right _ (specNorm_nonneg E)
  have h1 : a ^ 2 ≤ max (a ^ 2) (b ^ 2) := le_max_left _ _
  have h2 : b ^ 2 ≤ max (a ^ 2) (b ^ 2) := le_max_right _ _
  have h3 : b * a ≤ max (a ^ 2) (b ^ 2) := by
    rcases le_total a b with h | h
    · calc b * a ≤ b * b := mul_le_mul_of_nonneg_left h hb
        _ = b ^ 2 := (sq b).symm
        _ ≤ _ := h2
    · calc b * a ≤ a * a := mul_le_mul_of_nonneg_right h ha
        _ = a ^ 2 := (sq a).symm
        _ ≤ _ := h1
  linarith

/-- SCAFFOLD: pseudoinverse-perturbation
Wedin's sharp spectral bound without a rank assumption:
`‖(A + E)⁺ - A⁺‖₂ ≤ ((1 + √5)/2) max(‖A⁺‖₂², ‖(A + E)⁺‖₂²) ‖E‖₂`.
Wedin 1973, Thm 4.1; Stewart–Sun 1990, Thm III.3.8 (`μ = (1 + √5)/2` for the spectral norm).
Deferred: the sharp constant needs Wedin's orthogonality argument, not the triangle inequality
over the three terms of `moorePenroseInverse_add_sub_moorePenroseInverse` (which gives `3`).
Proof sketch: write `B⁺ - A⁺ = X + Y` with `X = -B⁺EA⁺ + (I - B⁺B)EᵀA⁺ᵀA⁺` (range in
`range Bᵀ ⊕ (range Bᵀ)⊥` split) and `Y`; the first and third terms have orthogonal row/column
spaces so `‖·‖² ≤` sum of squares (`specNorm_add_sq_le_of_transpose_mul_eq_zero`), then a
`2 × 2` scalar optimisation gives `((1 + √5)/2)²`. Difficulty 4.
atlas: pseudoinverse-perturbation -/
theorem specNorm_moorePenroseInverse_add_sub_le_goldenRatio_mul_max [DecidableEq m]
    [DecidableEq n] (A E : Matrix m n ℝ) :
    specNorm (moorePenroseInverse (A + E) - moorePenroseInverse A) ≤
      (1 + Real.sqrt 5) / 2 * max (specNorm (moorePenroseInverse A) ^ 2)
        (specNorm (moorePenroseInverse (A + E)) ^ 2) * specNorm E := by
  sorry

/-- SCAFFOLD: pseudoinverse-perturbation
Wedin's sharp spectral bound under equal rank: if `rank (A + E) = rank A` then
`‖(A + E)⁺ - A⁺‖₂ ≤ ((1 + √5)/2) ‖A⁺‖₂ ‖(A + E)⁺‖₂ ‖E‖₂`.
Wedin 1973, Thm 4.1; Stewart–Sun 1990, Thm III.3.8. Deferred: needs, besides the orthogonality
argument of `specNorm_moorePenroseInverse_add_sub_le_goldenRatio_mul_max`, the equal-rank
symmetry `‖(I - AA⁺)BB⁺‖₂ = ‖(I - BB⁺)AA⁺‖₂` (sine of the largest principal angle between
subspaces of equal dimension, atlas `principal-angles-def`), which turns the middle term's
`‖B⁺‖²` into `‖A⁺‖‖B⁺‖` via `(I - BB⁺)AA⁺ = -(I - BB⁺)EA⁺`. Difficulty 4.
atlas: pseudoinverse-perturbation -/
theorem specNorm_moorePenroseInverse_add_sub_le_goldenRatio_mul_of_rank_eq [DecidableEq m]
    [DecidableEq n] (A E : Matrix m n ℝ) (hr : (A + E).rank = A.rank) :
    specNorm (moorePenroseInverse (A + E) - moorePenroseInverse A) ≤
      (1 + Real.sqrt 5) / 2 * specNorm (moorePenroseInverse A) *
        specNorm (moorePenroseInverse (A + E)) * specNorm E := by
  sorry

/-- SCAFFOLD: pseudoinverse-perturbation
Perturbation of the column-space projector under equal rank: if `rank (A + E) = rank A` then
`‖A A⁺ - (A + E)(A + E)⁺‖₂ ≤ min(‖A⁺‖₂, ‖(A + E)⁺‖₂) ‖E‖₂`.
Stewart–Sun 1990, Thm III.3.8 / Wedin 1973, Lemma 4.2 (projector form). Deferred: needs the
equal-dimension principal-angle identity `‖P_A - P_B‖₂ = ‖(I - P_B)P_A‖₂ = ‖(I - P_A)P_B‖₂`
(atlas `principal-angles-def`); then `(I - P_B)P_A = (I - P_B)AA⁺ = -(I - P_B)EA⁺` gives
`‖A⁺‖‖E‖` and symmetrically `‖B⁺‖‖E‖`. Difficulty 3.
atlas: pseudoinverse-perturbation -/
theorem specNorm_mul_moorePenroseInverse_sub_le_of_rank_eq [DecidableEq m] [DecidableEq n]
    (A E : Matrix m n ℝ) (hr : (A + E).rank = A.rank) :
    specNorm (A * moorePenroseInverse A - (A + E) * moorePenroseInverse (A + E)) ≤
      min (specNorm (moorePenroseInverse A)) (specNorm (moorePenroseInverse (A + E))) *
        specNorm E := by
  sorry

end MoorePenrose

/-- Equal-rank inverse-norm bound for the pseudoinverse: if `rank (A + E) = rank A` and
`‖A⁺‖₂ ‖E‖₂ < 1` then `‖(A + E)⁺‖₂ ≤ ‖A⁺‖₂ / (1 - ‖A⁺‖₂ ‖E‖₂)`. Stewart–Sun 1990, Thm III.3.8
(the bound on `‖B⁺‖`); Wedin 1973, §4. Proof: with `r = rank A > 0`, `‖A⁺‖ = 1/σ_r(A)` and
`‖B⁺‖ = 1/σ_r(B)` (`specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive`), and Weyl
gives `σ_r(B) ≥ σ_r(A) - ‖E‖ > 0`. Stated on `Fin` indices like the singular-value API.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_moorePenroseInverse_add_le_of_rank_eq {m n : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ) (hr : (A + E).rank = A.rank)
    (hE : specNorm (moorePenroseInverse A) * specNorm E < 1) :
    specNorm (moorePenroseInverse (A + E)) ≤
      specNorm (moorePenroseInverse A) / (1 - specNorm (moorePenroseInverse A) * specNorm E) := by
  have hpos : 0 < 1 - specNorm (moorePenroseInverse A) * specNorm E := by linarith
  by_cases h0 : A.rank = 0
  · rw [moorePenroseInverse_eq_zero_of_rank_eq_zero (A + E) (hr.trans h0)]
    rw [specNorm_zero]
    exact div_nonneg (specNorm_nonneg _) hpos.le
  · have hrpos : 0 < A.rank := Nat.pos_of_ne_zero h0
    set k := A.rank - 1
    have hsA : 0 < singularValues A k := (singularValues_pos_iff A k).mpr (by omega)
    have hA := specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A hrpos
    have hB := specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive (A + E)
      (hr ▸ hrpos)
    rw [hr] at hB
    have hW := singularValues_le_singularValues_add_add_specNorm A E k
    rw [hA] at hE ⊢
    rw [hB]
    have hEs : specNorm E < singularValues A k := by
      rw [one_div, inv_mul_lt_iff₀ hsA, mul_one] at hE
      exact hE
    have hsB : singularValues A k - specNorm E ≤ singularValues (A + E) k := by linarith
    have hd : 0 < singularValues A k - specNorm E := by linarith
    calc 1 / singularValues (A + E) k ≤ 1 / (singularValues A k - specNorm E) :=
          one_div_le_one_div_of_le hd hsB
      _ = 1 / singularValues A k / (1 - 1 / singularValues A k * specNorm E) := by
          field_simp

end NLAlib
