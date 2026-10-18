import NLAlib.Matrix.Functions.SchattenDualTestMatrix
import NLAlib.ForMathlib.Analysis.Complex.Hirschman

/-!
# Matrix Stein--Hirschman interpolation with an infinity left boundary

Actual entire dual tests reduce Schatten matrix interpolation to the checked
scalar theorem with explicit Hirschman densities. The norm exponents are
`p₀ = ∞`, `p₁ = p`, and `pᵣ = p/r`, exactly as used for multivariate ALT.
Rank-deficient and zero center matrices and the endpoint `p = 1` are included.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Theorem 3.1 and Appendix D.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite-dimensional matrix Stein--Hirschman interpolation in its exact
infinity/finite endpoint specialization. Bounded measurable logarithmic
majorants need no nonvanishing assumptions on the matrix family. -/
theorem schattenNormReal_le_exp_hirschman_boundary_majorants
    {r p B H : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hp : 1 ≤ p)
    {G : ℂ → Matrix n n ℂ}
    (hG : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (G z) ≤ B)
    (h₀ h₁ : ℝ → ℝ) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁)
    (hb₀ : ∀ t, |h₀ t| ≤ H) (hb₁ : ∀ t, |h₁ t| ≤ H)
    (hleft : ∀ t : ℝ, specNorm (G ((t : ℂ) * Complex.I)) ≤ Real.exp (h₀ t))
    (hright : ∀ t : ℝ,
      schattenNormReal (G (1 + (t : ℂ) * Complex.I)) p ≤ Real.exp (h₁ t)) :
    schattenNormReal (G (r : ℂ)) (p / r) ≤ Real.exp (
      (∫ t : ℝ, ((1 - r) * Real.hirschmanDensity (1 - r) t) * h₀ t) +
      ∫ t : ℝ, (r * Real.hirschmanDensity r t) * h₁ t) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hα : 0 < p / r := div_pos hp0 hr.1
  by_cases hA : G (r : ℂ) = 0
  · rw [hA, schattenNormReal_zero hα]
    exact (Real.exp_pos _).le
  obtain ⟨U, V, hSVD⟩ := exists_isSVD (G (r : ℂ))
  let w : Fin (Fintype.card n) → ℝ := fun i =>
    singularValues (G (r : ℂ)) i / schattenNormReal (G (r : ℂ)) (p / r)
  let T := schattenDualTestMatrix U V r p w
  have hw : ∀ i, w i ∈ Icc (0 : ℝ) 1 := fun i =>
    singularValues_div_schattenNormReal_mem_Icc _ hα hA i
  have hpower : ∑ i, w i ^ (p / r) = 1 := by
    change (∑ i : Fin (Fintype.card n),
      (singularValues (G (r : ℂ)) i / schattenNormReal (G (r : ℂ)) (p / r)) ^ (p / r)) = 1
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (singularValues (G (r : ℂ)) i / schattenNormReal (G (r : ℂ)) (p / r)) ^ (p / r))]
    simpa only [min_self] using
      sum_singularValues_div_schattenNormReal_rpow_eq_one (G (r : ℂ)) hα hA
  have hTdiff : Differentiable ℂ T := differentiable_schattenDualTestMatrix U V r p w
  have hTnorm {z : ℂ} (hz : z.re ≤ 1) : specNorm (T z) ≤ 1 :=
    specNorm_schattenDualTestMatrix_le_one hSVD.conjTranspose_mul_left
      hSVD.conjTranspose_mul_right hr.1 hp hw hz
  let g : ℂ → ℂ := fun z => (T z * G z).trace
  let L := (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap
  have hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine ⟨?_, ?_⟩
    · exact L.differentiable.comp_differentiableOn (hTdiff.differentiableOn.mul hG.differentiableOn)
    · exact L.continuous.comp_continuousOn (hTdiff.continuous.continuousOn.mul hG.continuousOn)
  have hg_bound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      ‖g z‖ ≤ (Fintype.card n : ℝ) * B := by
    intro z hz
    have hzre : z.re ≤ 1 := hz.2
    have hTnuclear : nuclearNorm (T z) ≤ (Fintype.card n : ℝ) := by
      have h := schattenNormReal_le_rank_rpow_mul_specNorm (T z) (by norm_num : (0 : ℝ) < 1)
      simp only [schattenNormReal_one, one_div_one, Real.rpow_one] at h
      calc
        nuclearNorm (T z) ≤ ((T z).rank : ℝ) * specNorm (T z) := h
        _ ≤ (Fintype.card n : ℝ) * 1 :=
          mul_le_mul (by exact_mod_cast Matrix.rank_le_card_width (T z)) (hTnorm hzre)
            (specNorm_nonneg _) (Nat.cast_nonneg _)
        _ = _ := mul_one _
    calc
      ‖g z‖ ≤ nuclearNorm (T z) * specNorm (G z) := by
        simpa only [schattenNorm_one, schattenNorm_top] using
          norm_trace_mul_le_schattenNorm_mul_complex (T z) (G z) (p := 1) (q := ∞)
      _ ≤ _ := mul_le_mul hTnuclear (hbound z hz) (specNorm_nonneg _) (Nat.cast_nonneg _)
  have hg_left (t : ℝ) : ‖g ((t : ℂ) * Complex.I)‖ ≤ Real.exp (h₀ t) := by
    have hTl := nuclearNorm_schattenDualTestMatrix_left hSVD.conjTranspose_mul_left
      hSVD.conjTranspose_mul_right hr.1 hp0 (fun i => (hw i).1) hpower t
    have h := norm_trace_mul_le_schattenNorm_mul_complex
      (T ((t : ℂ) * Complex.I)) (G ((t : ℂ) * Complex.I)) (p := 1) (q := ∞)
    change ‖g ((t : ℂ) * Complex.I)‖ ≤ _ at h
    simp only [schattenNorm_one, schattenNorm_top, T, hTl, one_mul] at h
    exact h.trans (hleft t)
  have hg_right (t : ℝ) : ‖g (1 + (t : ℂ) * Complex.I)‖ ≤ Real.exp (h₁ t) := by
    by_cases hp1 : p = 1
    · subst p
      have h := norm_trace_mul_le_schattenNorm_mul_complex
        (T (1 + (t : ℂ) * Complex.I)) (G (1 + (t : ℂ) * Complex.I)) (p := ∞) (q := 1)
      simp only [schattenNorm_one, schattenNorm_top] at h
      apply h.trans
      calc
        _ ≤ 1 * nuclearNorm (G (1 + (t : ℂ) * Complex.I)) :=
          mul_le_mul_of_nonneg_right (hTnorm (by simp))
            (by simpa only [← schattenNormReal_one] using
              schattenNormReal_nonneg (G (1 + (t : ℂ) * Complex.I)) 1)
        _ ≤ _ := by simpa only [one_mul, schattenNormReal_one] using hright t
    · have hp1' : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
      have hpq := Real.HolderConjugate.conjExponent hp1'
      have hTr := schattenNormReal_schattenDualTestMatrix_right hSVD.conjTranspose_mul_left
        hSVD.conjTranspose_mul_right hr.1 hpq (fun i => (hw i).1) hpower t
      have h := norm_trace_mul_le_schattenNormReal_mul_complex
        (T (1 + (t : ℂ) * Complex.I)) (G (1 + (t : ℂ) * Complex.I)) hpq.symm
      simp only [T, hTr, one_mul] at h
      exact h.trans (hright t)
  have hcenter : ‖g (r : ℂ)‖ = schattenNormReal (G (r : ℂ)) (p / r) := by
    have htr := hSVD.trace_schattenDualTestMatrix_center_mul hr.1
      (lt_of_lt_of_le hr.2 hp) hA
    change g (r : ℂ) = (schattenNormReal (G (r : ℂ)) (p / r) : ℂ) at htr
    rw [htr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (schattenNormReal_nonneg _ _)]
  rw [← hcenter]
  exact Complex.norm_le_exp_hirschman_boundary_majorants hr hg hg_bound
    h₀ h₁ hm₀ hm₁ hb₀ hb₁ hg_left hg_right

/-- The matrix interpolation bound when the left boundary consists of
spectral contractions, as for ordered imaginary-time Hermitian exponentials. -/
theorem schattenNormReal_le_exp_hirschman_of_left_contractions
    {r p B H : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hp : 1 ≤ p)
    {G : ℂ → Matrix n n ℂ}
    (hG : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (G z) ≤ B)
    (h₁ : ℝ → ℝ) (hm₁ : Measurable h₁) (hb₁ : ∀ t, |h₁ t| ≤ H)
    (hleft : ∀ t : ℝ, specNorm (G ((t : ℂ) * Complex.I)) ≤ 1)
    (hright : ∀ t : ℝ,
      schattenNormReal (G (1 + (t : ℂ) * Complex.I)) p ≤ Real.exp (h₁ t)) :
    schattenNormReal (G (r : ℂ)) (p / r) ≤
      Real.exp (∫ t : ℝ, (r * Real.hirschmanDensity r t) * h₁ t) := by
  have hH : 0 ≤ H := (abs_nonneg (h₁ 0)).trans (hb₁ 0)
  simpa only [mul_zero, integral_zero, zero_add] using
    schattenNormReal_le_exp_hirschman_boundary_majorants hr hp hG hbound
      (fun _ => 0) h₁ measurable_const hm₁ (fun _ => by simpa using hH) hb₁
      (fun t => by simpa only [Real.exp_zero] using hleft t) hright

end NLAlib
