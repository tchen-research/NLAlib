import NLAlib.Matrix.Functions.SchattenDualTestMatrix
import Mathlib.Analysis.Complex.Hadamard

/-!
# Schatten interpolation between two finite endpoints

An analytic matrix family with finite Schatten bounds on the two sides of
a strip obeys the sharp geometric interpolation estimate. Entire dual tests
reduce the statement to scalar Hadamard three-lines. Singular and zero
matrices are included, and the norms are the ordinary unnormalized norms.

This is the finite-dimensional output interpolation needed for the Gaussian
entry multiplier in Latała--van Handel--Youssef, arXiv:1711.00807v2, §2.3.
The statement concerns an actual analytic family; it assumes no operator
interpolation theorem or interpolated norm bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace NLAlib

private theorem norm_schattenDualTestCoefficient_rpow_of_reciprocal
    {p s t w : ℝ} (hp : 0 < p) (hst : Real.HolderConjugate s t)
    (hw : 0 ≤ w) {z : ℂ} (hz : z.re = 1 / s) :
    ‖schattenDualTestCoefficient (1 / p) 1 w z‖ ^ t = w ^ p := by
  by_cases hwpos : 0 < w
  · rw [norm_schattenDualTestCoefficient_of_pos hwpos, hz, ← Real.rpow_mul hw]
    congr 1
    have hst' := hst.sub_one_mul_conj
    field_simp [hp.ne', hst.ne_zero]
    nlinarith
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [schattenDualTestCoefficient, Real.zero_rpow hst.symm.ne_zero,
      Real.zero_rpow hp.ne']

private theorem schattenNormReal_schattenDualTestMatrix_eq_one_of_reciprocal
    {n : Type*} [Fintype n] [DecidableEq n]
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {p s t : ℝ} (hp : 0 < p) (hst : Real.HolderConjugate s t)
    {w : Fin (Fintype.card n) → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hpower : ∑ i, w i ^ p = 1) {z : ℂ} (hz : z.re = 1 / s) :
    schattenNormReal (schattenDualTestMatrix U V (1 / p) 1 w z) t = 1 := by
  rw [schattenDualTestMatrix, schattenNormReal_isometry_mul_mul_conjTranspose hV hU,
    schattenNormReal_diagonal_complex]
  simp_rw [norm_schattenDualTestCoefficient_rpow_of_reciprocal hp hst (hw _) hz]
  rw [hpower, Real.one_rpow]

/-- Sharp analytic strip interpolation between any two finite Schatten
exponents greater than one. The center exponent has the affine reciprocal
`1/p = (1-θ)/p₀ + θ/p₁`. The family may have deficient rank, vanish at the
center, or act on an empty matrix space. This is the finite-dimensional
Riesz--Thorin output estimate, proved directly from scalar three-lines. -/
theorem schattenNormReal_le_rpow_mul_rpow_of_finite_boundary_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    {θ p₀ p₁ p M₀ M₁ B : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp : 1 < p)
    (hexp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    {G : ℂ → Matrix n n ℂ}
    (hG : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (G z) ≤ B)
    (hleft : ∀ t : ℝ, schattenNormReal (G ((t : ℂ) * Complex.I)) p₀ ≤ M₀)
    (hright : ∀ t : ℝ, schattenNormReal (G (1 + (t : ℂ) * Complex.I)) p₁ ≤ M₁) :
    schattenNormReal (G (θ : ℂ)) p ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hA : G (θ : ℂ) = 0
  · rw [hA, schattenNormReal_zero hp0]
    exact mul_nonneg
      (Real.rpow_nonneg ((schattenNormReal_nonneg _ _).trans (hleft 0)) _)
      (Real.rpow_nonneg ((schattenNormReal_nonneg _ _).trans (hright 0)) _)
  obtain ⟨U, V, hSVD⟩ := exists_isSVD (G (θ : ℂ))
  let w : Fin (Fintype.card n) → ℝ := fun i =>
    singularValues (G (θ : ℂ)) i / schattenNormReal (G (θ : ℂ)) p
  let a : ℂ → ℂ := fun z => (1 - z) / (p₀ : ℂ) + z / (p₁ : ℂ)
  let T : ℂ → Matrix n n ℂ := fun z => schattenDualTestMatrix U V (1 / p) 1 w (a z)
  have hw : ∀ i, w i ∈ Icc (0 : ℝ) 1 := fun i =>
    singularValues_div_schattenNormReal_mem_Icc _ hp0 hA i
  have hpower : ∑ i, w i ^ p = 1 := by
    change (∑ i : Fin (Fintype.card n),
      (singularValues (G (θ : ℂ)) i / schattenNormReal (G (θ : ℂ)) p) ^ p) = 1
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (singularValues (G (θ : ℂ)) i / schattenNormReal (G (θ : ℂ)) p) ^ p)]
    simpa only [min_self] using
      sum_singularValues_div_schattenNormReal_rpow_eq_one (G (θ : ℂ)) hp0 hA
  have ha : Differentiable ℂ a := by dsimp [a]; fun_prop
  have hTdiff : Differentiable ℂ T :=
    (differentiable_schattenDualTestMatrix U V (1 / p) 1 w).comp ha
  have hare (z : ℂ) : (a z).re = (1 - z.re) / p₀ + z.re / p₁ := by
    dsimp [a]
    simp [Complex.div_re]
    field_simp [(zero_lt_one.trans hp₀).ne', (zero_lt_one.trans hp₁).ne']
  have hTnorm {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
      specNorm (T z) ≤ 1 := by
    apply specNorm_schattenDualTestMatrix_le_one hSVD.conjTranspose_mul_left
      hSVD.conjTranspose_mul_right (one_div_pos.mpr hp0) (by norm_num) hw
    rw [hare]
    have h₀ : 1 / p₀ ≤ 1 := (div_le_one (zero_lt_one.trans hp₀)).mpr hp₀.le
    have h₁ : 1 / p₁ ≤ 1 := (div_le_one (zero_lt_one.trans hp₁)).mpr hp₁.le
    have hh₀ := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hz.2)
    have hh₁ := mul_le_mul_of_nonneg_left h₁ hz.1
    simp only [div_eq_mul_inv, one_mul, mul_one] at *
    nlinarith
  let g : ℂ → ℂ := fun z => (T z * G z).trace
  let L := (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap
  have hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine ⟨?_, ?_⟩
    · exact L.differentiable.comp_differentiableOn
        (hTdiff.differentiableOn.mul hG.differentiableOn)
    · exact L.continuous.comp_continuousOn
        (hTdiff.continuous.continuousOn.mul hG.continuousOn)
  have hbounded : BddAbove ((norm ∘ g) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨(Fintype.card n : ℝ) * B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hTnuclear : nuclearNorm (T z) ≤ (Fintype.card n : ℝ) := by
      have h := schattenNormReal_le_rank_rpow_mul_specNorm (T z) (by norm_num : (0 : ℝ) < 1)
      simp only [schattenNormReal_one, one_div_one, Real.rpow_one] at h
      calc
        nuclearNorm (T z) ≤ ((T z).rank : ℝ) * specNorm (T z) := h
        _ ≤ (Fintype.card n : ℝ) * 1 :=
          mul_le_mul (by exact_mod_cast Matrix.rank_le_card_width (T z)) (hTnorm hz)
            (specNorm_nonneg _) (Nat.cast_nonneg _)
        _ = _ := mul_one _
    calc
      ‖g z‖ ≤ nuclearNorm (T z) * specNorm (G z) := by
        simpa only [schattenNorm_one, schattenNorm_top] using
          norm_trace_mul_le_schattenNorm_mul_complex (T z) (G z) (p := 1) (q := ∞)
      _ ≤ _ := mul_le_mul hTnuclear (hbound z hz) (specNorm_nonneg _) (Nat.cast_nonneg _)
  have hboundary {s M : ℝ} (hs : 1 < s) {z : ℂ}
      (hz : (a z).re = 1 / s) (hGs : schattenNormReal (G z) s ≤ M) : ‖g z‖ ≤ M := by
    have hst := Real.HolderConjugate.conjExponent hs
    have hT := schattenNormReal_schattenDualTestMatrix_eq_one_of_reciprocal
      hSVD.conjTranspose_mul_left hSVD.conjTranspose_mul_right hp0 hst
      (fun i => (hw i).1) hpower hz
    have hh := norm_trace_mul_le_schattenNormReal_mul_complex (T z) (G z) hst.symm
    change schattenNormReal (T z) s.conjExponent = 1 at hT
    rw [hT, one_mul] at hh
    exact hh.trans hGs
  have hgl : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖g z‖ ≤ M₀ := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have heq : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz0]
    apply hboundary hp₀
    · rw [hare, hz0]; simp
    · simpa only [← heq] using hleft z.im
  have hgr : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖g z‖ ≤ M₁ := by
    intro z hz
    have hz1 : z.re = 1 := hz
    have heq : z = 1 + (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz1]
    apply hboundary hp₁
    · rw [hare, hz1]; simp
    · simpa only [← heq] using hright z.im
  have hacenter : a (θ : ℂ) = ((1 / p : ℝ) : ℂ) := by
    dsimp [a]
    exact_mod_cast hexp.symm
  have hcenter : ‖g (θ : ℂ)‖ = schattenNormReal (G (θ : ℂ)) p := by
    have hh := hSVD.trace_schattenDualTestMatrix_center_mul (r := 1 / p) (p := 1)
      (one_div_pos.mpr hp0) ((div_lt_one hp0).mpr hp) hA
    simp only [one_div_one_div] at hh
    change (schattenDualTestMatrix U V (1 / p) 1 w ((1 / p : ℝ) : ℂ) * G (θ : ℂ)).trace = _ at hh
    change ‖(T (θ : ℂ) * G (θ : ℂ)).trace‖ = _
    rw [show T (θ : ℂ) = schattenDualTestMatrix U V (1 / p) 1 w ((1 / p : ℝ) : ℂ) from
      congrArg (schattenDualTestMatrix U V (1 / p) 1 w) hacenter, hh,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (schattenNormReal_nonneg _ _)]
  rw [← hcenter]
  simpa only [Complex.ofReal_re] using
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' g
      (z := (θ : ℂ)) ⟨by simpa using hθ.1.le, by simpa using hθ.2.le⟩ hg hbounded hgl hgr

end NLAlib
