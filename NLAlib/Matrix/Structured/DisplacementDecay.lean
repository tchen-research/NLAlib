import NLAlib.Matrix.Structured.PolynomialDisplacement
import NLAlib.Matrix.Spectral.Weyl
import NLAlib.Matrix.Functions.RationalCalculus
import NLAlib.Matrix.Basic.RankBounds
import NLAlib.Polynomial.Approximation.Zolotarev

/-! # Singular-value bounds from low-rank rational displacement -/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- A low-rank difference `X-LXR` gives multiplicative singular-value decay.
Indices are zero-based and padded by zeros, so no positivity or dimensional
case is omitted. Source: user derivations, Eckart–Young competitor argument.
atlas: displacement-singular-value-decay (partial) -/
theorem singularValues_add_le_of_rank_sub_mul_mul_le
    (X : Matrix m n K) (L : Matrix m m K) (R : Matrix n n K) (r j : ℕ)
    (hD : (X - L * X * R).rank ≤ r) :
    singularValues X (j + r) ≤ specNorm L * specNorm R * singularValues X j := by
  let C := (X - L * X * R) + L * truncatedSVD X j * R
  have hC : C.rank ≤ j + r := by
    have hc : (L * truncatedSVD X j * R).rank ≤ j :=
      ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
        (isBestFrobRankApprox_truncatedSVD X j).1
    exact (rank_add_le _ _).trans (by omega)
  have heq : X - C = L * (X - truncatedSVD X j) * R := by
    simp only [C, Matrix.mul_sub, Matrix.sub_mul]
    abel
  calc
    _ ≤ specNorm (X - C) := singularValues_le_specNorm_sub_of_rank_le _ _ hC
    _ = specNorm (L * (X - truncatedSVD X j) * R) := by rw [heq]
    _ ≤ specNorm (L * (X - truncatedSVD X j)) * specNorm R := specNorm_mul_le _ _
    _ ≤ (specNorm L * specNorm (X - truncatedSVD X j)) * specNorm R :=
      mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ = _ := by rw [specNorm_sub_truncatedSVD_eq]; ring

/-- The rational-pair displacement bound precedes any normality hypothesis.
Only the two used denominator evaluations must be invertible.
Source: user derivations, rational displacement singular-value inequality.
atlas: displacement-singular-value-decay (partial) -/
theorem singularValues_add_mul_le_rational_displacement
    (A : Matrix m m K) (B : Matrix n n K) (X : Matrix m n K) (r k j : ℕ)
    (hD : displacementRank A B X ≤ r) (p q : K[X])
    (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k)
    (hqa : IsUnit (aeval A q).det) (hpb : IsUnit (aeval B p).det) :
    singularValues X (j + r * k) ≤
      specNorm ((aeval A q)⁻¹ * aeval A p) *
        specNorm (aeval B q * (aeval B p)⁻¹) * singularValues X j := by
  apply singularValues_add_le_of_rank_sub_mul_mul_le
  simpa [Matrix.mul_assoc] using rank_rational_displacement_le A B X r k hD p q hp hq hqa hpb

open scoped ENNReal in
/-- Normal operators with spectra in the two compact sets satisfy the
Zolotarev singular-value bound. Natural indices are zero-based, so this is
the source's one-based statement after replacing `j` by `j-1`. Padded zeros
also make the statement valid beyond the source's dimensional range.
Source: user derivations, normal displacement singular-value decay.
atlas: displacement-singular-value-decay -/
theorem singularValues_add_mul_le_zolotarev
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (X : Matrix m n ℂ) (r k j : ℕ)
    (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B)
    (hD : displacementRank A B X ≤ r) (E F : Set ℂ)
    (hE : IsCompact E) (hF : IsCompact F)
    (hAE : spectrum ℂ A ⊆ E) (hBF : spectrum ℂ B ⊆ F) :
    singularValues X (j + r * k) ≤ (zolotarevNumber E F k).toReal * singularValues X j := by
  have hpair (P : ZolotarevPair E F k) :
      ENNReal.ofReal (singularValues X (j + r * k)) ≤
        P.cost * ENNReal.ofReal (singularValues X j) := by
    have hqa : ∀ z ∈ spectrum ℂ A, P.denominator.eval z ≠ 0 :=
      fun z hz => P.denominator_ne_zero z (hAE hz)
    have hpb : ∀ z ∈ spectrum ℂ B, P.numerator.eval z ≠ 0 :=
      fun z hz => P.numerator_ne_zero z (hBF hz)
    have hleft : specNorm ((aeval A P.denominator)⁻¹ * aeval A P.numerator) ≤ P.leftSup.toReal :=
      specNorm_inv_aeval_mul_aeval_le A hA _ _ hqa ENNReal.toReal_nonneg
        (fun z hz => P.norm_div_le_leftSup_toReal hE (hAE hz))
    have hright : specNorm (aeval B P.denominator * (aeval B P.numerator)⁻¹) ≤ P.rightSup.toReal :=
      specNorm_aeval_mul_inv_aeval_le B hB _ _ hpb ENNReal.toReal_nonneg
        (fun z hz => P.norm_div_le_rightSup_toReal hF (hBF hz))
    have hreal := (singularValues_add_mul_le_rational_displacement A B X r k j hD
      P.numerator P.denominator P.numerator_degree P.denominator_degree
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_aeval_of_normal A hA _ hqa))
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_aeval_of_normal B hB _ hpb))).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hleft hright (specNorm_nonneg _) ENNReal.toReal_nonneg)
          (singularValues_nonneg X j))
    have henn := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (P.leftSup_ne_top hE),
      ENNReal.ofReal_toReal (P.rightSup_ne_top hF)] at henn
    exact henn
  have henn : ENNReal.ofReal (singularValues X (j + r * k)) ≤
      zolotarevNumber E F k * ENNReal.ofReal (singularValues X j) := by
    rw [zolotarevNumber, ENNReal.iInf_mul (by simp)]
    exact le_iInf hpair
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (zolotarevNumber_ne_top E F k) ENNReal.ofReal_ne_top) henn
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (singularValues_nonneg X _)] using hreal

end NLAlib
