import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeSpectralNets
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeResolventProbability
import NLAlib.Probability.Gaussian.Moments.SeriesFrobenius
import NLAlib.ForMathlib.MeasureTheory.CStarSpectralTwoGrids

/-! # Actual Gaussian/free spectral probability from finite grids

All interpolation, concentration and localization inputs are derived from
the actual Gaussian series and native free model. Remaining hypotheses are
explicit numerical height, mesh and moment-budget inequalities.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]

open scoped Matrix.Norms.L2Operator in
/-- The actual two-sided spectral distance has an explicit probability
bound from the actual coefficient parameters, at every numerically admissible
height and comparison error. The two grids and all their event bounds are proved.
Source: arXiv:2406.11453v2, Theorem 2.2, spectral discretization step.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_hausdorffDist_gaussian_wordNative_gt_le_grid_error
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hmass : 0 < bilinearSquareMass A Finset.univ)
    {q : ℕ} (hq : 0 < q) (hlog : Real.log (Fintype.card d : ℝ) ≤ q)
    {η C δ t : ℝ} (hη : 0 < η) (ht : 0 ≤ t)
    (hscale : Real.sqrt (specNorm (coefficientVariance A)) ≤
      2*(Fintype.card d : ℝ)*(Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q))
    (hCfwd : Real.exp 1*(Fintype.card d : ℝ)^(1/(4*q : ℝ)) ≤ C)
    (hCfree : 438*Real.exp 5 ≤ C)
    (hforward : (Real.exp 1*(Fintype.card d : ℝ)^(1/(4*q : ℝ))) *
      (((2*(2*q)+1)*(2*(2*q)+2)^2 : ℕ) *
        (specNorm (coefficientVariance A)*specNorm (coefficientCovariance A))*η⁻¹^5) ≤ δ)
    (hreverse : (438*Real.exp 5) *
      (Real.sqrt (4*(bilinearSquareMass A Finset.univ*η⁻¹^4)*(2*q)) + t +
        ((2*(2*q)+1)*(2*(2*q)+2)^2 : ℕ) *
          (specNorm (coefficientVariance A)*specNorm (coefficientCovariance A))*η⁻¹^5 +
        Real.sqrt (specNorm (coefficientVariance A))/((Fintype.card d : ℝ)^2*η^2)) ≤ δ)
    (herror : δ+(C+1)*(2*(Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q))/η^2 ≤
      (2*η)⁻¹) :
    (gaussianVector ι).real {x : ι → ℝ | 2*C*η < Metric.hausdorffDist
      (spectrum ℝ (A₀+∑ i,x i•A i)) (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A))} ≤
      1/(16*(q : ℝ)) + (9*(Fintype.card d)^2 : ℕ)*Real.exp (-4*q : ℝ) +
        (18*(Fintype.card d)^2 : ℕ)*Real.exp (-t^2/(2*(bilinearSquareMass A Finset.univ*η⁻¹^4))) := by
  classical
  let : Nontrivial (WordHilbertSpace ι) := by
    apply nontrivial_of_ne (wordVacuum ι) 0
    intro hz
    have hn := norm_wordVacuum (ι := ι)
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  let ε := Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q
  have hε : 0 < ε := mul_pos (Real.sqrt_pos.mpr hmass) (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨N,M,hNc,hMc,hMS,hN,hM⟩ := exists_finset_gaussian_free_spectral_nets
    A₀ hA₀ A hA hε hscale
  let X : (ι → ℝ) → Matrix d d ℂ := fun x => A₀+∑ i,x i•A i
  let F := wordNativeMatrixLinearCombination A₀ A
  let ζ (u : ℝ) : ℂ := (u : ℂ)+(η : ℂ)*Complex.I
  have hζim (u : ℝ) : (ζ u).im=η := by simp [ζ]
  have hζre (u : ℝ) : (ζ u).re=u := by simp [ζ]
  have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ 438*Real.exp 5).trans hCfree
  have hHerm (x : ι → ℝ) : (X x).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hF := isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA
  have hvar : coefficientVariance A = ∑ k,A k^2 := by simp only [coefficientVariance,pow_two]
  have hexp : 1 / (((2*(2*q) : ℕ)) : ℝ) = 1/(4*q : ℝ) := by push_cast; ring
  have hfwd (u : ℝ) : (gaussianVector ι).real {x : ι → ℝ |
      C*‖resolvent F (ζ u)‖+δ < ‖resolvent (X x) (ζ u)‖} ≤ Real.exp (-4*q : ℝ) := by
    have hp := measureReal_specNorm_gaussian_resolvent_gt_free_le A₀ hA₀ A hA (ζ := ζ u)
      (by rw [hζim]; exact hη.ne') (by omega : 0 < 2*q)
    dsimp only at hp
    rw [hexp, hζim,abs_of_pos hη] at hp
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hp
    rw [show -(2*(2*(q : ℝ))) = -4*q by ring] at hp
    refine le_trans ?_ hp
    apply measureReal_mono _ (by finiteness)
    intro x hx
    change _ < specNorm (resolvent (X x) (ζ u))
    rw [specNorm_eq_norm (resolvent (X x) (ζ u))]
    have hmul := mul_le_mul_of_nonneg_right hCfwd (norm_nonneg (resolvent F (ζ u)))
    have hb : (Real.exp 1*(Fintype.card d : ℝ)^(1/(4*q : ℝ))) *
      (((2*(2*q)+1)*(2*(2*q)+2)^2 : ℕ) *
        (specNorm (coefficientVariance A)*specNorm (coefficientCovariance A))*η⁻¹^5) ≤ δ := hforward
    dsimp only [F] at *
    change C*‖resolvent (wordNativeMatrixLinearCombination A₀ A) (ζ u)‖+δ < _ at hx
    push_cast at hb ⊢
    dsimp only [X] at hx ⊢
    nlinarith only [hx,hmul,hb]
  have hrev (u : ℝ) (hu : u ∈ M) : (gaussianVector ι).real {x : ι → ℝ |
      C*‖resolvent (X x) (ζ u)‖+δ < ‖resolvent F (ζ u)‖} ≤
      2*Real.exp (-t^2/(2*(bilinearSquareMass A Finset.univ*η⁻¹^4))) := by
    have hp := measureReal_free_resolvent_gt_gaussian_le A₀ hA₀ A hA hq hlog (ζ := ζ u)
      (by rw [hζim]; exact hη) (by rw [hζre]; exact hMS hu) ht
    dsimp only at hp
    rw [hζim,abs_of_pos hη,← hvar] at hp
    refine le_trans ?_ hp
    apply measureReal_mono _ (by finiteness)
    intro x hx
    change _ < ‖resolvent F (ζ u)‖
    have hmul := mul_le_mul_of_nonneg_right hCfree (norm_nonneg (resolvent (X x) (ζ u)))
    have hb := hreverse
    change C*‖resolvent (X x) (ζ u)‖+δ < ‖resolvent F (ζ u)‖ at hx
    rw [specNorm_eq_norm (resolvent (X x) (ζ u))]
    nlinarith only [hx,hmul,hb]
  have hLA : (gaussianVector ι).real {x : ι → ℝ |
      ¬ ∀ ξ ∈ spectrum ℝ (X x), ∃ u ∈ N, |ξ-u| ≤ 2*ε} ≤ 1/(16*(q : ℝ)) := by
    refine le_trans ?_ (measureReal_specNorm_gaussianSeries_gt_bilinear_scale_le A hmass
      (by positivity : (0 : ℝ) < q))
    apply measureReal_mono _ (by finiteness)
    intro x hx
    change 4*(Fintype.card d : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q <
      specNorm (∑ i,x i•A i)
    by_contra hn
    apply hx
    intro ξ hξ
    have hb : specNorm (X x-A₀) ≤ 4*(Fintype.card d : ℝ)*ε := by
      simpa only [X,add_sub_cancel_left,ε,mul_assoc] using le_of_not_gt hn
    obtain ⟨u,hu,hd⟩ := hN (X x) hb ξ hξ
    exact ⟨u,hu,hd.trans (by linarith only [hε])⟩
  have hLB : (gaussianVector ι).real {x : ι → ℝ |
      ¬ ∀ ξ ∈ spectrum ℝ F, ∃ u ∈ M, |ξ-u| ≤ 2*ε}=0 := by
    have he : {x : ι → ℝ | ¬ ∀ ξ ∈ spectrum ℝ F, ∃ u ∈ M, |ξ-u| ≤ 2*ε}=∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_not]
      exact hM
    rw [he,measureReal_empty]
  have hh := MeasureTheory.measureReal_hausdorffDist_spectra_gt_le_two_resolvent_grids
    (gaussianVector ι) X (fun _ : ι → ℝ => F)
    (Filter.Eventually.of_forall hHerm) (Filter.Eventually.of_forall fun _ => hF)
      N M hη hC herror
  change (gaussianVector ι).real {x | 2*C*η < Metric.hausdorffDist
    (spectrum ℝ (X x)) (spectrum ℝ F)} ≤ _
  refine hh.trans ?_
  rw [hLB,add_zero]
  have hsumF : (∑ u ∈ N, (gaussianVector ι).real {x : ι → ℝ |
      C*‖resolvent F (ζ u)‖+δ < ‖resolvent (X x) (ζ u)‖}) ≤
      (N.card : ℝ)*Real.exp (-4*q : ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s := N)
      (fun u _ => hfwd u)
  have hsumR : (∑ u ∈ M, (gaussianVector ι).real {x : ι → ℝ |
      C*‖resolvent (X x) (ζ u)‖+δ < ‖resolvent F (ζ u)‖}) ≤
      (M.card : ℝ)*(2*Real.exp (-t^2/(2*(bilinearSquareMass A Finset.univ*η⁻¹^4)))) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s := M)
      (fun u hu => hrev u hu)
  have hNcR : (N.card : ℝ) ≤ (9*(Fintype.card d)^2 : ℕ) := by exact_mod_cast hNc
  have hMcR : (M.card : ℝ) ≤ (9*(Fintype.card d)^2 : ℕ) := by exact_mod_cast hMc
  have hFcard := mul_le_mul_of_nonneg_right hNcR (Real.exp_pos (-4*q : ℝ)).le
  have hRcard := mul_le_mul_of_nonneg_right hMcR
    (by positivity : (0 : ℝ) ≤ 2*Real.exp (-t^2/(2*(bilinearSquareMass A Finset.univ*η⁻¹^4))))
  change _ ≤ _ at hLA
  dsimp only [ζ] at hsumF hsumR
  push_cast at hNcR hMcR hFcard hRcard ⊢
  linarith only [hLA,hsumF,hsumR,hFcard,hRcard]

end NLAlib
