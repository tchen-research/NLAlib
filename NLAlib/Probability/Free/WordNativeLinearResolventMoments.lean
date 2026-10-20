import NLAlib.Probability.Free.WordNativeMatrixLinearCombination
import NLAlib.Probability.Free.WordMatrixMeanResolventMoments

/-!
# Mean-uniform resolvent moments of the actual coefficient free model

This applies the proved native mean-clipping estimate to the concrete
matrix-coefficient semicircular word fields. Both the variance scale and
the amplified vacuum moments are those of this actual operator.
Source: arXiv:2406.11453v2, Theorem 4.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

/-- The exact actual matrix-coefficient free model satisfies the source's
mean-uniform resolvent bound, with a stronger dimension-free clipping
error. The scale is the genuine square-mass norm of its Hermitian
coefficients; all dimensions and finite index families are retained.

Source: arXiv:2406.11453v2, Theorem 4.3.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_resolvent_wordNativeMatrixLinearCombination_le_evenMoment_mean_uniform
    (q r : ℕ) (hq : 0<q) (hr : 0<r)
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ k, (A k).IsHermitian)
    {K : ℝ} (hK : 4<K) {z : ℂ} (hz : 0<z.im)
    (hησ : z.im≤Real.sqrt (specNorm (∑ k, A k^2))) :
    ‖resolvent (wordNativeMatrixLinearCombination A₀ A) z‖ ≤
      (Fintype.card D : ℝ) ^ (3 / (4*q : ℝ)) *
        (2*q*r+1 : ℝ) ^ (3 / (4*q : ℝ)) *
          (((wordMatrixVacuumExpectation (D := D) (ι := ι)
            ((star (resolvent (wordNativeMatrixLinearCombination A₀ A) z) *
              resolvent (wordNativeMatrixLinearCombination A₀ A) z) ^ (2*q))).re) ^
                (1 / (4*q : ℝ)) +
            18*Real.sqrt (specNorm (∑ k, A k^2))/z.im^2*(K/(r : ℝ)+K⁻¹)) := by
  let C := CStarMatrix.mapStarAlgHom (D := D) (StarAlgHom.ofId ℂ B)
  let Y := wordNativeMatrixLinearCombination (0 : Matrix D D ℂ) A
  have hD : IsSelfAdjoint (CStarMatrix.ofMatrix A₀) :=
    hA₀.isSelfAdjoint.map
      (CStarMatrix.ofMatrixStarAlgEquiv (n := D) (A := ℂ)).toStarAlgHom
  have hY : IsSelfAdjoint Y := isSelfAdjoint_wordNativeMatrixLinearCombination (by simp) hA
  have hdeg : ∀ i j, Y i j∈wordWickDegreeSpan (ι := ι) 1 :=
    wordNativeMatrixLinearCombination_mem_wordWickDegreeSpan 0 A
  have hzero : CStarMatrix.ofMatrix (0 : Matrix D D ℂ)=0 := rfl
  have hnorm : ‖Y‖≤2*Real.sqrt (specNorm (∑ k, A k^2)) := by
    simpa only [hzero,map_zero,sub_zero] using
      norm_wordNativeMatrixLinearCombination_sub_mean_le 0 A hA
  have heq : C (CStarMatrix.ofMatrix A₀)+Y=wordNativeMatrixLinearCombination A₀ A := by
    simp only [Y,wordNativeMatrixLinearCombination,C,hzero,map_zero,zero_add]
  have h := norm_resolvent_le_wordMatrixVacuum_evenMoment_rpow_mean_uniform
    q r hq hr (CStarMatrix.ofMatrix A₀) hD Y hY hdeg hK hnorm hz hησ
  rwa [heq] at h

end NLAlib

end
