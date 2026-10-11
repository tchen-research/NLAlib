import NLAlib.Concentration.Scalar.RademacherCube
import NLAlib.Concentration.Scalar.SubGaussian
import NLAlib.Gaussian.DirectionalSquaredNorm
import NLAlib.Matrix.Projections

/-!
# Row flattening for a classical one-diagonal SRHT

One actual shared diagonal of independent signs is applied to a fixed frame
before the fixed flat orthogonal transform. The row projection MGF is derived
from the concrete sign law, then Gaussian linearization supplies the additive
row norm tail. Supports atlas `srht-ose`, source `sh:srht`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal
namespace NLAlib

/-- The classical fixed transform and one shared random diagonal applied to a
fixed input frame. Source: operator re-derivation `sh:srht`. -/
def srhtSignedFrame {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ) (ξ : Fin n → Bool) : Matrix (Fin n) (Fin d) ℝ :=
  H * Matrix.diagonal (fun i => rademacherBoolSign (ξ i)) * U

/-- A row scaled by `√n`, whose directional MGF proxy is one.
Source: operator re-derivation `sh:srht-quadratic`. -/
def srhtNormalizedRow {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ) (j : Fin n) (ξ : Fin n → Bool) : Fin d → ℝ :=
  Real.sqrt (n : ℝ) • (fun a => srhtSignedFrame H U ξ j a)

/-- The actual shared diagonal sign transform preserves orthonormal columns.
Source: operator re-derivation `sh:srht`, since every sign has square one. -/
theorem hasOrthonormalCols_srhtSignedFrame {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U) (ξ : Fin n → Bool) :
    HasOrthonormalCols (srhtSignedFrame H U ξ) := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => rademacherBoolSign (ξ i))
  have hD : Dᵀ * D = 1 := by
    dsimp only [D]
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    simp only [← sq, rademacherBoolSign_sq, Matrix.diagonal_one]
  change (H * D * U)ᵀ * (H * D * U) = 1
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Hᵀ, hH, Matrix.one_mul,
    ← Matrix.mul_assoc Dᵀ, hD, Matrix.one_mul]
  exact hU

/-- The primitive directional MGF condition for the literal one-sign SRHT row
is derived from flatness, the input isometry and the actual independent sign
cube law. Coordinates of the row may be dependent.
Source: operator re-derivation `sh:srht-quadratic`. -/
theorem hasSubgaussianMGF_srhtNormalizedRow_dotProduct {n d : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    (j : Fin n) (u : Fin d → ℝ) :
    HasSubgaussianMGF (fun ξ => srhtNormalizedRow H U j ξ ⬝ᵥ u)
      ⟨u ⬝ᵥ u, dotProduct_self_nonneg u⟩ (rademacherCubePMF (Fin n)).toMeasure := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let a : Fin n → ℝ := fun i => (Real.sqrt (n : ℝ) * H j i) * (U *ᵥ u) i
  have hscale : ∀ i : Fin n, (Real.sqrt (n : ℝ) * H j i) ^ 2 = 1 := by
    intro i
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), hflat]
    field_simp
  have ha : a ⬝ᵥ a = u ⬝ᵥ u := by
    have hUnorm := mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hU u
    calc
      _ = ∑ i, ((Real.sqrt (n : ℝ) * H j i) * (U *ᵥ u) i) ^ 2 := by
        simp only [a, dotProduct, ← sq]
      _ = ∑ i, (U *ᵥ u) i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow, hscale, one_mul]
      _ = _ := by simpa only [dotProduct, ← sq] using hUnorm
  have hlin : ∀ ξ : Fin n → Bool, srhtNormalizedRow H U j ξ ⬝ᵥ u =
      ∑ i, a i * rademacherBoolSign (ξ i) := by
    intro ξ
    dsimp only [srhtNormalizedRow]
    rw [smul_dotProduct, smul_eq_mul]
    change Real.sqrt (n : ℝ) * ((H * Matrix.diagonal (fun i => rademacherBoolSign (ξ i)) * U)
      *ᵥ u) j = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change Real.sqrt (n : ℝ) * (∑ i, H j i *
      ((Matrix.diagonal (fun i => rademacherBoolSign (ξ i))) *ᵥ (U *ᵥ u)) i) = _
    simp only [Matrix.mulVec_diagonal, Finset.mul_sum, a]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh := hasSubgaussianMGF_sum_mul_rademacher a
    (fun i (ξ : Fin n → Bool) => rademacherBoolSign (ξ i))
    (iIndepFun_rademacherBoolSign_cube (Fin n))
    (isRademacher_rademacherBoolSign_cube (Fin n))
  simpa only [← hlin, ha] using hh

/-- The actual row's squared norm has the sharp additive chi-square tail,
from the shared sign law and genuine Gaussian linearization.
Source: supports the original additive classical SRHT flattening bound. -/
theorem measure_srht_row_sq_ge_add_two_sqrt_mul_add_le {n d : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    (j : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    (rademacherCubePMF (Fin n)).toMeasure
      {ξ | d + 2 * Real.sqrt (d * t) + 2 * t ≤
        (n : ℝ) * ((fun a => srhtSignedFrame H U ξ j a) ⬝ᵥ
          (fun a => srhtSignedFrame H U ξ j a))} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have hh := measure_sq_norm_ge_add_two_sqrt_mul_add_le (rademacherCubePMF (Fin n))
    (srhtNormalizedRow H U j) (hasSubgaussianMGF_srhtNormalizedRow_dotProduct H hflat U hU j) ht
  have hsq : ∀ ξ : Fin n → Bool,
      srhtNormalizedRow H U j ξ ⬝ᵥ srhtNormalizedRow H U j ξ =
      (n : ℝ) * ((fun a => srhtSignedFrame H U ξ j a) ⬝ᵥ
        (fun a => srhtSignedFrame H U ξ j a)) := by
    intro ξ
    rw [srhtNormalizedRow, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [hsq] using hh

/-- The original additive SRHT row threshold, with a shared sign diagonal.
Source: Tropp's classical SRHT analysis; atlas `srht-ose`. -/
def srhtSharpRowBound (n d : ℕ) (δ : ℝ) : ℝ :=
  (Real.sqrt (d : ℝ) + Real.sqrt (8 * Real.log (2 * n / δ))) ^ 2

/-- The chi-square row threshold is below the classical additive bound.
Source: operator re-derivation `sh:srht-quadratic`. -/
theorem srht_chi_square_threshold_le {d : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    d + 2 * Real.sqrt (d * t) + 2 * t ≤
      (Real.sqrt (d : ℝ) + Real.sqrt (8 * t)) ^ 2 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg d)
  have hr := Real.sq_sqrt (show 0 ≤ 8 * t by positivity)
  have hrt : Real.sqrt t ≤ Real.sqrt (8 * t) := Real.sqrt_le_sqrt (by linarith)
  have hm := mul_le_mul_of_nonneg_left hrt (Real.sqrt_nonneg (d : ℝ))
  rw [Real.sqrt_mul (Nat.cast_nonneg d)]
  nlinarith

/-- Simultaneous row flattening for the actual one-diagonal sign law, with
the sharp additive threshold and failure `δ/2`. No separate-coordinate union
bound is used. Source: `sh:flat-event`, classical SRHT. -/
theorem measure_srhtSharpRowBound_failure_le {n d : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((rademacherCubePMF (Fin n)).toMeasure
      {ξ | ∃ j : Fin n, srhtSharpRowBound n d δ <
        (n : ℝ) * ((fun a => srhtSignedFrame H U ξ j a) ⬝ᵥ
          (fun a => srhtSignedFrame H U ξ j a))}).toReal ≤ δ / 2 := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have ht : 0 ≤ Real.log (2 * n / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  let μ := (rademacherCubePMF (Fin n)).toMeasure
  let B : Fin n → Set (Fin n → Bool) := fun j => {ξ | srhtSharpRowBound n d δ <
    (n : ℝ) * ((fun a => srhtSignedFrame H U ξ j a) ⬝ᵥ
      (fun a => srhtSignedFrame H U ξ j a))}
  have hrow (j : Fin n) : (μ (B j)).toReal ≤ Real.exp (-Real.log (2 * n / δ)) := by
    have hsub : B j ⊆ {ξ | d + 2 * Real.sqrt (d * Real.log (2 * n / δ)) +
        2 * Real.log (2 * n / δ) ≤ (n : ℝ) *
          ((fun a => srhtSignedFrame H U ξ j a) ⬝ᵥ
            (fun a => srhtSignedFrame H U ξ j a))} := by
      intro ξ hξ
      exact (srht_chi_square_threshold_le ht).trans hξ.le
    have hh := (measure_mono hsub).trans
      (measure_srht_row_sq_ge_add_two_sqrt_mul_add_le H hflat U hU j ht)
    have hr := ENNReal.toReal_mono (by simp) hh
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr
  have hset : {ξ | ∃ j : Fin n, srhtSharpRowBound n d δ <
        (n : ℝ) * ((fun a => srhtSignedFrame H U ξ j a) ⬝ᵥ
          (fun a => srhtSignedFrame H U ξ j a))} = ⋃ j, B j := by
    ext ξ
    simp only [B, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  calc
    _ ≤ ∑ j : Fin n, (μ (B j)).toReal := measureReal_iUnion_fintype_le B
    _ ≤ ∑ _j : Fin n, Real.exp (-Real.log (2 * n / δ)) :=
      Finset.sum_le_sum (fun j _ => hrow j)
    _ = δ / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * (n : ℝ) / δ)]
      field_simp

end NLAlib
