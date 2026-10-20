import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeSpectrum
import NLAlib.Matrix.Structured.GramDilationAffine
import NLAlib.Matrix.Norms.GramDilationWeakParameter
import NLAlib.ForMathlib.Analysis.LogarithmicDimensionChange

/-! # Actual shifted quadratic Gaussian/free spectral comparison

The actual positive rectangular linearization transfers the full linear
comparison to non-Hermitian Gaussian Gram matrices with an arbitrary
Hermitian shift. Both the actual Gaussian law and the arbitrary faithful
free model are retained; zero weak variance gives deterministic equality.
Source: arXiv:2406.11453v2, Theorem 2.5 and Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d Ω E : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]
  [MeasurableSpace Ω] [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

open scoped Matrix.Norms.L2Operator in
/-- The full shifted quadratic Gaussian/free spectral comparison for the
original non-Hermitian coefficient parameters. The constant `10^44` is
universal. The zero-weak-variance equality is pointwise in the actual
Gaussian realization.
Source: arXiv:2406.11453v2, Theorem 2.5 and Section 5.3.
atlas: gaussian-quadratic-free-spectrum -/
theorem gaussian_free_shiftedGram_spectrum_comparison
    (hd : 2 ≤ Fintype.card d) (A₀ B : Matrix d d ℂ) (hB : B.IsHermitian)
    (A : ι → Matrix d d ℂ)
    (φ : E →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (hfaithful : ∀ a : E, φ (star a * a) = 0 → a = 0)
    (S : ι → E) (hS : ∀ i, IsSelfAdjoint (S i))
    (hfree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap S)
    (hlaw : ∀ (i : ι) (n : ℕ), φ (S i ^ n) = if Even n then (catalan (n / 2) : ℂ) else 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → (ι → ℝ))
    (hg : HasLaw g (gaussianVector ι) μ) :
    let X := fun ω : Ω => A₀ + ∑ i, g ω i • A i
    let F := CStarMatrix.affineCombination ℂ A₀ A S
    let Bf := CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ E) (CStarMatrix.ofMatrix B)
    let σ := Real.sqrt (max (specNorm (∑ i, A i * (A i)ᴴ)) (specNorm (∑ i, (A i)ᴴ * A i)))
    let v := Real.sqrt (specNorm (coefficientCovariance A))
    let ξ := Real.sqrt (σ * v)
    let s := Real.sqrt (bilinearSquareMass A Finset.univ)
    (s = 0 → ∀ ω, spectrum ℝ (X ω * (X ω)ᴴ + B) = spectrum ℝ (F * star F + Bf)) ∧
      (0 < s → ∀ t : ℝ, ξ * Real.log (Fintype.card d : ℝ) ^ (3 / 4 : ℝ) ≤ t →
        μ.real {ω | (10 : ℝ) ^ 44 * (‖F‖ + Real.sqrt (specNorm B)) * t +
          (10 : ℝ) ^ 44 * t ^ 2 < Metric.hausdorffDist
            (spectrum ℝ (X ω * (X ω)ᴴ + B)) (spectrum ℝ (F * star F + Bf))} ≤
          Real.exp (-t ^ 2 / s ^ 2)) := by
  classical
  have h10 : (1 : E) ≠ 0 := by
    intro h
    have hp := congrArg φ h
    rw [hφ, map_zero] at hp
    exact one_ne_zero hp
  let : Nontrivial E := ⟨⟨1, 0, h10⟩⟩
  dsimp only
  let X := fun ω : Ω => A₀ + ∑ i, g ω i • A i
  let F := CStarMatrix.affineCombination ℂ A₀ A S
  let f := CStarMatrix.mapStarAlgHom (D := d) (StarAlgHom.ofId ℂ E)
  let Bf := f (CStarMatrix.ofMatrix B)
  let ξ := Real.sqrt
    (Real.sqrt (max (specNorm (∑ i, A i * (A i)ᴴ)) (specNorm (∑ i, (A i)ᴴ * A i))) *
      Real.sqrt (specNorm (coefficientCovariance A)))
  let s := Real.sqrt (bilinearSquareMass A Finset.univ)
  change (s = 0 → ∀ ω, spectrum ℝ (X ω * (X ω)ᴴ + B) = spectrum ℝ (F * star F + Bf)) ∧ _
  refine ⟨?_, ?_⟩
  · intro hs0 ω
    have hm : bilinearSquareMass A Finset.univ = 0 := by
      have hh := Real.sq_sqrt (bilinearSquareMass_nonneg A Finset.univ)
      change Real.sqrt (bilinearSquareMass A Finset.univ) = 0 at hs0
      rw [hs0] at hh
      simpa using hh.symm
    have hA := (bilinearSquareMass_univ_eq_zero_iff A).mp hm
    have hx : X ω = A₀ := by simp only [X, hA, smul_zero, Finset.sum_const_zero, add_zero]
    rw [hx]
    exact (spectrum_shiftedGram_affineCombination_eq_of_zero_weak A₀ B hB A hm S).symm
  · intro hs t ht
    change 0 < s at hs
    change ξ * Real.log (Fintype.card d : ℝ) ^ (3 / 4 : ℝ) ≤ t at ht
    have hweak := sqrt_bilinearSquareMass_le_sqrt_rectangular_variance_covariance A
    change s ≤ ξ at hweak
    have hξpos : 0 < ξ := hs.trans_le hweak
    have hdreal : (2 : ℝ) ≤ Fintype.card d := by exact_mod_cast hd
    have hlogpos : 0 < Real.log (Fintype.card d : ℝ) := Real.log_pos (by linarith)
    have htpos : 0 < t := lt_of_lt_of_le
      (mul_pos hξpos (Real.rpow_pos_of_pos hlogpos _)) ht
    let L : ℝ := 100000000000000000000
    let δ : ℝ := 8 * L * t
    let b := specNorm B
    let H₀ : Matrix (d ⊕ (d ⊕ d)) (d ⊕ (d ⊕ d)) ℂ := CStarMatrix.ofMatrix.symm
      (CStarMatrix.rectangularDilation (CStarMatrix.positiveGramRow
        (CStarMatrix.ofMatrix A₀) (CStarMatrix.ofMatrix B) b δ))
    let H := gramCoefficientDilation A
    let HX := fun ω : Ω => H₀ + ∑ i, g ω i • H i
    let HF := CStarMatrix.affineCombination ℂ H₀ H S
    let ξH := Real.sqrt (Real.sqrt (specNorm (coefficientVariance H)) *
      Real.sqrt (specNorm (coefficientCovariance H)))
    let sH := Real.sqrt (bilinearSquareMass H Finset.univ)
    have hδ : 0 < δ := by dsimp [δ, L]; positivity
    have hb : specNorm B ≤ b := le_rfl
    have hH₀ : H₀.IsHermitian := isHermitian_dilation _
    have hH (i : ι) : (H i).IsHermitian := isHermitian_gramCoefficientDilation A i
    have hdH : 2 ≤ Fintype.card (d ⊕ (d ⊕ d)) := by simp only [Fintype.card_sum]; omega
    have hξH : ξH ≤ 2 * ξ := sqrt_variance_covariance_gramCoefficientDilation_le A
    have hsH : sH ≤ 2 * s := sqrt_bilinearSquareMass_gramCoefficientDilation_le A
    have hcardH : (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) = 3 * (Fintype.card d : ℝ) := by
      simp only [Fintype.card_sum, Nat.cast_add]
      ring
    have hlogH : Real.log (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) ^ (3 / 4 : ℝ) ≤
        3 * Real.log (Fintype.card d : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hcardH]
      exact Real.log_three_mul_rpow_three_quarters_le hd
    have hlogH0 : 0 ≤ Real.log (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card (d ⊕ (d ⊕ d))))) _
    have hbaseH : ξH * Real.log (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) ^ (3 / 4 : ℝ) ≤
        6 * ξ * Real.log (Fintype.card d : ℝ) ^ (3 / 4 : ℝ) := by
      have hh := mul_le_mul hξH hlogH hlogH0 (show 0 ≤ 2 * ξ by positivity)
      nlinarith only [hh]
    have hthreshold : L * ξH * Real.log (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) ^ (3 / 4 : ℝ) +
        L * sH * (t / s) ≤ δ := by
      have hbase := mul_le_mul_of_nonneg_left hbaseH (show 0 ≤ L by dsimp [L]; norm_num)
      have hscale := mul_le_mul_of_nonneg_left ht (show 0 ≤ 6 * L by dsimp [L]; norm_num)
      have hweak' := mul_le_mul_of_nonneg_right hsH (div_nonneg htpos.le hs.le)
      have hcancel : (2 * s) * (t / s) = 2 * t := by field_simp [hs.ne']
      rw [hcancel] at hweak'
      dsimp only [δ, L] at hbase hscale hweak' ⊢
      nlinarith only [hbase, hscale, hweak']
    have hlin := gaussian_free_spectrum_comparison hdH H₀ hH₀ H hH
      φ hφ hfaithful S hS hfree hlaw μ g hg
    dsimp only at hlin
    have hp := (hlin.2.2.2.2 (t / s) (div_nonneg htpos.le hs.le)).1
    change μ.real {ω | L * ξH * Real.log (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) ^ (3 / 4 : ℝ) +
      L * sH * (t / s) < Metric.hausdorffDist (spectrum ℝ (HX ω)) (spectrum ℝ HF)} ≤
        Real.exp (-(t / s) ^ 2) at hp
    have hDfree : CStarMatrix.rectangularDilation
        (CStarMatrix.positiveGramRow F Bf b δ) = HF := by
      exact rectangularDilation_positiveGramRow_affineCombination A₀ B hB A S hS hb δ
    have hDsample (ω : Ω) : spectrum ℝ (CStarMatrix.rectangularDilation
        (CStarMatrix.positiveGramRow (CStarMatrix.ofMatrix (X ω)) (CStarMatrix.ofMatrix B) b δ)) =
        spectrum ℝ (HX ω) := by
      have hSreal (i : ι) : IsSelfAdjoint (g ω i : ℂ) := by change star (g ω i : ℂ) = _; simp
      have hh := rectangularDilation_positiveGramRow_affineCombination
        (A := ℂ) A₀ B hB A (fun i => (g ω i : ℂ)) hSreal hb δ
      have hid (T : CStarMatrix d d ℂ) :
          CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ ℂ) T = T := by ext; rfl
      rw [hid, affineCombination_ofReal_eq_ofMatrix_real_series,
        affineCombination_ofReal_eq_ofMatrix_real_series] at hh
      exact (congrArg (spectrum ℝ) hh).trans (spectrum_real_ofMatrix_complex (HX ω))
    have hBsrc : IsSelfAdjoint (CStarMatrix.ofMatrix B) := hB
    have hBfree : IsSelfAdjoint Bf := hBsrc.map f
    have hsrcNorm : ‖CStarMatrix.ofMatrix B‖ ≤ b := by
      simpa only [CStarMatrix.norm_ofMatrix_complex, ← specNorm_eq_norm] using hb
    have hf : Function.Injective f := CStarMatrix.mapStarAlgHom_injective _
      (FaithfulSMul.algebraMap_injective ℂ E)
    have hfreeNorm : ‖Bf‖ ≤ b := by
      rw [show ‖Bf‖ = ‖CStarMatrix.ofMatrix B‖ from NonUnitalStarAlgHom.norm_map f hf _]
      exact hsrcNorm
    have hsub : {ω | (10 : ℝ) ^ 44 * (‖F‖ + Real.sqrt (specNorm B)) * t +
        (10 : ℝ) ^ 44 * t ^ 2 < Metric.hausdorffDist
          (spectrum ℝ (X ω * (X ω)ᴴ + B)) (spectrum ℝ (F * star F + Bf))} ⊆
        {ω | L * ξH * Real.log (Fintype.card (d ⊕ (d ⊕ d)) : ℝ) ^ (3 / 4 : ℝ) +
          L * sH * (t / s) < Metric.hausdorffDist (spectrum ℝ (HX ω)) (spectrum ℝ HF)} := by
      intro ω hω
      change _ < Metric.hausdorffDist (spectrum ℝ (HX ω)) (spectrum ℝ HF)
      by_contra hn
      have hdil : Metric.hausdorffDist
          (spectrum ℝ (CStarMatrix.rectangularDilation (CStarMatrix.positiveGramRow
            (CStarMatrix.ofMatrix (X ω)) (CStarMatrix.ofMatrix B) b δ)))
          (spectrum ℝ (CStarMatrix.rectangularDilation (CStarMatrix.positiveGramRow F Bf b δ))) ≤ δ := by
        rw [hDsample, hDfree]
        exact (le_of_not_gt hn).trans hthreshold
      have hquad := CStarMatrix.hausdorffDist_spectrum_shiftedGram_le_of_positiveGramRow
        (CStarMatrix.ofMatrix (X ω)) (CStarMatrix.ofMatrix B) F Bf
        hBsrc hBfree hsrcNorm hfreeNorm hδ hdil
      change Metric.hausdorffDist (spectrum ℝ (CStarMatrix.ofMatrix (X ω * (X ω)ᴴ + B)))
        (spectrum ℝ (F * star F + Bf)) ≤ 4 * (‖F‖ + Real.sqrt b) * δ + 5 * δ ^ 2 at hquad
      rw [spectrum_real_ofMatrix_complex] at hquad
      have hnum : 4 * (‖F‖ + Real.sqrt b) * δ + 5 * δ ^ 2 ≤
          (10 : ℝ) ^ 44 * (‖F‖ + Real.sqrt b) * t + (10 : ℝ) ^ 44 * t ^ 2 := by
        dsimp [δ, L]
        nlinarith [mul_nonneg (add_nonneg (norm_nonneg F) (Real.sqrt_nonneg b)) htpos.le,
          sq_nonneg t]
      exact (not_lt_of_ge (hquad.trans hnum)) hω
    have hprob := (measureReal_mono hsub (by finiteness)).trans hp
    simpa only [div_pow, neg_div] using hprob

end NLAlib
