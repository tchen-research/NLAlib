import NLAlib.Matrix.Functions.SchattenFiniteInterpolation
import NLAlib.Matrix.Norms.SchattenBlockDiagonal
import NLAlib.Matrix.Norms.ComplexSchattenNorms
import NLAlib.ForMathlib.Analysis.FiniteLatticeFactorization

/-!
# Analytic interpolation for finite matrix-valued measures

A finite matrix-valued random output is represented by a weighted block
diagonal matrix. Analytic powers of the atom weights adjust its Schatten
exponent on the two boundaries and at the center. The resulting theorem
is the genuine `L^p(S_p)` interpolation estimate on any finite measure
space, with exact weights and constant one.

Source: the finite-output form of Latała--van Handel--Youssef,
arXiv:1711.00807v2, §2.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

private def finiteMeasureInterpolationWeight (w p₀ p₁ : ℝ) (z : ℂ) : ℂ :=
  powerInterpolationCoefficient (w ^ (1 / p₀)) (w ^ (1 / p₁)) z

private theorem norm_finiteMeasureInterpolationWeight_rpow
    {w p₀ p₁ s : ℝ} (hw : 0 ≤ w) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hs : 0 < s)
    {z : ℂ} (hz : (1 - z.re) / p₀ + z.re / p₁ = 1 / s) :
    ‖finiteMeasureInterpolationWeight w p₀ p₁ z‖ ^ s = w := by
  by_cases hwpos : 0 < w
  · rw [finiteMeasureInterpolationWeight, norm_powerInterpolationCoefficient_of_pos
      (Real.rpow_pos_of_pos hwpos _) (Real.rpow_pos_of_pos hwpos _),
      ← Real.rpow_mul hw, ← Real.rpow_mul hw, ← Real.rpow_add hwpos,
      ← Real.rpow_mul hw]
    have he : ((1 / p₀) * (1 - z.re) + (1 / p₁) * z.re) * s = 1 := by
      calc
        _ = ((1 - z.re) / p₀ + z.re / p₁) * s := by ring
        _ = 1 := by rw [hz]; field_simp
    rw [he, Real.rpow_one]
  · have hwzero := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [finiteMeasureInterpolationWeight, powerInterpolationCoefficient,
      Real.zero_rpow (inv_ne_zero hp₀.ne'), Real.zero_rpow (inv_ne_zero hp₁.ne'),
      Real.zero_rpow hs.ne']

/-- Sharp `L^p(S_p)` strip interpolation for an arbitrary finite weighted
matrix output. The atom weights need not sum to one. Every endpoint and
center uses the actual finite weighted Schatten moment, and the conclusion
has constant one. Vanishing atoms, singular blocks, and empty finite spaces
are included. -/
theorem sum_mul_schattenNormReal_rpow_root_le_of_finite_boundary_bounds
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {θ p₀ p₁ p M₀ M₁ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp : 1 < p)
    (hexp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (G : ι → ℂ → Matrix n n ℂ)
    (hG : ∀ i, DiffContOnCl ℂ (G i) (Complex.HadamardThreeLines.verticalStrip 0 1))
    (B : ι → ℝ)
    (hbound : ∀ i z, z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 →
      specNorm (G i z) ≤ B i)
    (hleft : ∀ t : ℝ,
      (∑ i, w i * schattenNormReal (G i ((t : ℂ) * Complex.I)) p₀ ^ p₀) ^ (1 / p₀) ≤ M₀)
    (hright : ∀ t : ℝ,
      (∑ i, w i * schattenNormReal (G i (1 + (t : ℂ) * Complex.I)) p₁ ^ p₁) ^ (1 / p₁) ≤ M₁) :
    (∑ i, w i * schattenNormReal (G i (θ : ℂ)) p ^ p) ^ (1 / p) ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  classical
  have hp₀0 : 0 < p₀ := zero_lt_one.trans hp₀
  have hp₁0 : 0 < p₁ := zero_lt_one.trans hp₁
  have hp0 : 0 < p := zero_lt_one.trans hp
  let c : ι → ℂ → ℂ := fun i => finiteMeasureInterpolationWeight (w i) p₀ p₁
  let F : ℂ → ι → Matrix n n ℂ := fun z i => c i z • G i z
  let H : ℂ → Matrix (n × ι) (n × ι) ℂ := fun z => Matrix.blockDiagonal (F z)
  have hc (i : ι) : Differentiable ℂ (c i) :=
    differentiable_powerInterpolationCoefficient _ _
  have hF : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine ⟨differentiableOn_pi.mpr fun i => ?_, continuousOn_pi.mpr fun i => ?_⟩
    · exact (hc i).differentiableOn.smul (hG i).differentiableOn
    · exact (hc i).continuous.continuousOn.smul (hG i).continuousOn
  let D : (ι → Matrix n n ℂ) →ₗ[ℂ] Matrix (n × ι) (n × ι) ℂ :=
    { toFun := Matrix.blockDiagonal
      map_add' := Matrix.blockDiagonal_add
      map_smul' := fun a f => Matrix.blockDiagonal_smul a f }
  have hH : DiffContOnCl ℂ H (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    exact ⟨D.toContinuousLinearMap.differentiable.comp_differentiableOn hF.differentiableOn,
      D.toContinuousLinearMap.continuous.comp_continuousOn hF.continuousOn⟩
  have hnorm {s : ℝ} (hs : 0 < s) {z : ℂ}
      (hz : (1 - z.re) / p₀ + z.re / p₁ = 1 / s) :
      schattenNormReal (H z) s = (∑ i, w i * schattenNormReal (G i z) s ^ s) ^ (1 / s) := by
    rw [show H z = Matrix.blockDiagonal (fun i => c i z • G i z) from rfl,
      schattenNormReal_blockDiagonal_complex _ hs]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [schattenNormReal_smul_complex _ _ hs,
      Real.mul_rpow (norm_nonneg _) (schattenNormReal_nonneg _ _),
      show ‖c i z‖ ^ s = w i from
        norm_finiteMeasureInterpolationWeight_rpow (hw i) hp₀0 hp₁0 hs hz]
  let C : ι → ℝ := fun i => max (w i ^ (1 / p₀)) (w i ^ (1 / p₁)) *
    (Fintype.card n : ℝ) ^ (1 / (2 : ℝ)) * |B i|
  have hmax (i : ι) : 0 ≤ max (w i ^ (1 / p₀)) (w i ^ (1 / p₁)) :=
    le_max_of_le_left (Real.rpow_nonneg (hw i) _)
  have hFbound {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1)
      (i : ι) : schattenNormReal (F z i) 2 ≤ C i := by
    have hci : ‖c i z‖ ≤ max (w i ^ (1 / p₀)) (w i ^ (1 / p₁)) :=
      norm_powerInterpolationCoefficient_le_max (Real.rpow_nonneg (hw i) _)
        (Real.rpow_nonneg (hw i) _) hz
    have hGi := (schattenNormReal_le_card_rpow_mul_specNorm (G i z) (by norm_num : (0 : ℝ) < 2)).trans
      (mul_le_mul_of_nonneg_left ((hbound i z hz).trans (le_abs_self _)) (by positivity))
    rw [show F z i = c i z • G i z from rfl, schattenNormReal_smul_complex _ _ (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul hci hGi (schattenNormReal_nonneg _ _) (hmax i)).trans_eq (by dsimp [C]; ring)
  have hHbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      specNorm (H z) ≤ (∑ i, C i ^ 2) ^ (1 / (2 : ℝ)) := by
    intro z hz
    apply (specNorm_le_schattenNormReal (H z) (by norm_num : (0 : ℝ) < 2)).trans
    rw [show H z = Matrix.blockDiagonal (F z) from rfl,
      schattenNormReal_blockDiagonal_complex _ (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (schattenNormReal_nonneg _ _) _) _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    simpa only [Real.rpow_two] using pow_le_pow_left₀ (schattenNormReal_nonneg _ _) (hFbound hz i) 2
  rw [← hnorm hp0 (by simpa only [Complex.ofReal_re] using hexp.symm)]
  apply schattenNormReal_le_rpow_mul_rpow_of_finite_boundary_bounds hθ hp₀ hp₁ hp hexp hH hHbound
  · intro t
    rw [hnorm hp₀0 (by simp)]
    exact hleft t
  · intro t
    rw [hnorm hp₁0 (by simp)]
    exact hright t

end NLAlib
