import NLAlib.ForMathlib.MeasureTheory.WassersteinOne

/-!
# Lipschitz pushforwards of the primal Wasserstein distance

Push an actual coupling forward in both coordinates and bound its cost.
The positive constant permits commuting multiplication with arbitrary infima,
including the empty coupling family.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace NLAlib

/-- A Lipschitz map multiplies one-Wasserstein distance by at most its positive
Lipschitz constant. The assertion is about the infimum over actual couplings. -/
theorem wassersteinEDistOne_map_le_mul {X Y : Type*}
    [MeasurableSpace X] [PseudoEMetricSpace X] [BorelSpace X]
    [MeasurableSpace Y] [PseudoEMetricSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ ν : Measure X) {K : ℝ≥0} (hK : K ≠ 0) {f : X → Y} (hf : LipschitzWith K f) :
    wassersteinEDistOne (μ.map f) (ν.map f) ≤ K * wassersteinEDistOne μ ν := by
  have hK' : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK
  simp only [wassersteinEDistOne, ENNReal.mul_iInf_of_ne hK' ENNReal.coe_ne_top]
  refine le_iInf fun π => le_iInf fun hπ => ?_
  have hfm := hf.continuous.measurable
  apply (iInf_le_of_le (π.map (fun p => (f p.1, f p.2)))
    (iInf_le_of_le (hπ.map hfm hfm) le_rfl)).trans
  rw [lintegral_map (g := fun p : X × X => (f p.1, f p.2))
    (measurable_fst.edist measurable_snd) (by fun_prop), ← lintegral_const_mul' _ _]
  · exact lintegral_mono fun p => hf p.1 p.2
  · exact ENNReal.coe_ne_top

/-- Positive real dilation scales the actual transport distance by at most the
dilation factor. This applies to atomic laws without choosing a coupling. -/
theorem wassersteinEDistOne_map_mul_le (μ ν : Measure ℝ) {S : ℝ} (hS : 0 < S) :
    wassersteinEDistOne (μ.map (fun x => S * x)) (ν.map (fun x => S * x)) ≤
      ENNReal.ofReal S * wassersteinEDistOne μ ν := by
  have hf : LipschitzWith ⟨S, hS.le⟩ (fun x : ℝ => S * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hS]
    rfl
  rw [ENNReal.ofReal_eq_coe_nnreal hS.le]
  exact wassersteinEDistOne_map_le_mul μ ν (K := ⟨S, hS.le⟩)
    (by intro he; exact hS.ne' (congrArg (fun x : ℝ≥0 => (x : ℝ)) he)) hf

/-- Positive real dilation of a normed real space scales the genuine transport
cost by at most the dilation factor. This also applies to complex spectral laws. -/
theorem wassersteinEDistOne_map_real_smul_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ ν : Measure E) {S : ℝ} (hS : 0 < S) :
    wassersteinEDistOne (μ.map (fun z => S•z)) (ν.map (fun z => S•z)) ≤
      ENNReal.ofReal S * wassersteinEDistOne μ ν := by
  have hf : LipschitzWith ⟨S,hS.le⟩ (fun z : E => S•z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hS.le]
    rw [dist_eq_norm]
    exact le_rfl
  rw [ENNReal.ofReal_eq_coe_nnreal hS.le]
  exact wassersteinEDistOne_map_le_mul μ ν (K := ⟨S,hS.le⟩)
    (by intro he; exact hS.ne' (congrArg (fun x : ℝ≥0 => (x:ℝ)) he)) hf

end NLAlib
