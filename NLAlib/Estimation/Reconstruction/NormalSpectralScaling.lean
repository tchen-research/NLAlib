import NLAlib.Estimation.Reconstruction.NormalSpectralDensity
import NLAlib.Matrix.Spectral.NormalScaling
import NLAlib.Matrix.Norms.RealScaling
import NLAlib.Krylov.QueryModel.OracleAdapter

/-!
# Supplied physical scales in normal spectral-density queries

Removing the known scale acts only on oracle responses. The final law is dilated
in the complex plane, and native empirical eigenvalue laws scale identically.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real dilation of a normal matrix dilates its empirical eigenvalue law. -/
theorem normalEmpiricalSpectralLaw_smul {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (S : ℝ) :
    normalEmpiricalSpectralLaw (normal_real_smul hA S) =
      (normalEmpiricalSpectralLaw hA).map (fun z => S•z) := by
  obtain ⟨U,d,hU⟩ := exists_unitary_diagonalization_of_normal hA
  have hUs : S•A = (U : Matrix n n ℂ)*Matrix.diagonal (fun i => S•d i)*(U : Matrix n n ℂ)ᴴ := by
    have hd : Matrix.diagonal (fun i => S•d i) = S•Matrix.diagonal d := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [hU, hd]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [normalEmpiricalSpectralLaw_eq_uniformComplexSpectralLaw _ U _ hUs,
    normalEmpiricalSpectralLaw_eq_uniformComplexSpectralLaw hA U d hU]
  have hf : Measurable (fun z : ℂ => S•z) := by fun_prop
  simp only [uniformComplexSpectralLaw, Measure.map_smul,
    Measure.map_finset_sum' hf.aemeasurable, Measure.map_dirac' hf]

omit [DecidableEq n] in
/-- Normalize the response to each primitive matrix or adjoint query. -/
theorem matrixAdjointOracle_real_smul (A : Matrix n n ℂ) (S : ℝ) :
    matrixAdjointOracle (S•A) = (fun v : n → ℂ => S•v) ∘ matrixAdjointOracle A := by
  funext q
  rcases q with ⟨imaginary,x⟩
  cases imaginary <;> simp [matrixAdjointOracle, Matrix.conjTranspose_smul, Matrix.smul_mulVec]

/-- The physical-scale strategy, chosen from `S,b,M` before the oracle is given. -/
def normalScaledSpectralDensityProgram (S : ℝ) (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (Measure ℂ)
      (hermitianPartChebyshevCost M+hermitianPartChebyshevCost M) :=
  ((normalSpectralDensityProgram b M).adaptResponses (fun v => S⁻¹•v)).map
    (fun μ => μ.map (fun z => S•z))

omit [DecidableEq n] in
/-- The native strategy on the supplied matrix is exactly the normalized
strategy followed by physical dilation. Its primitive query count is unchanged. -/
theorem run_normalScaledSpectralDensityProgram (A : Matrix n n ℂ) (S : ℝ)
    (b : n → ℂ) (M : ℕ) :
    (normalScaledSpectralDensityProgram S b M).run (matrixAdjointOracle A) =
      (((normalSpectralDensityProgram b M).run (matrixAdjointOracle (S⁻¹•A))).map
        (fun z => S•z)) := by
  rw [normalScaledSpectralDensityProgram, QueryProgram.run_map, QueryProgram.run_adaptResponses,
    ← matrixAdjointOracle_real_smul]

/-- Supplied-scale native inputs produce an actual probability law.
atlas: normal-spectral-density-query (partial) -/
theorem isProbabilityMeasure_run_normalScaledSpectralDensityProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1) (M : ℕ) :
    IsProbabilityMeasure ((normalScaledSpectralDensityProgram S b M).run (matrixAdjointOracle A)) := by
  rw [run_normalScaledSpectralDensityProgram]
  have := isProbabilityMeasure_run_normalSpectralDensityProgram
    (normal_real_smul hA S⁻¹) b hb (specNorm_inv_smul_le_one hS hbound) M
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The source's explicit estimate at the supplied physical scale, for the
actual native two-sided query strategy and actual single complex-sphere probe.
atlas: normal-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_normalScaledSpectralDensityProgram_gt_le [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (complexSphereVector n).real {b |
      ENNReal.ofReal (S*(84/M + π*normalTensorMomentRadius (Fintype.card n) M δ *
        sqrt (5+(π/2)*log M))) <
      wassersteinEDistOne (normalEmpiricalSpectralLaw hA)
        ((normalScaledSpectralDensityProgram S b M).run (matrixAdjointOracle A))} ≤ δ := by
  let B := S⁻¹•A
  have hB := normal_real_smul hA S⁻¹
  have hBn := specNorm_inv_smul_le_one hS hbound
  have hlaw : (normalEmpiricalSpectralLaw hB).map (fun z => S•z) = normalEmpiricalSpectralLaw hA := by
    have hh := normalEmpiricalSpectralLaw_smul hB S
    simpa only [smul_smul, mul_inv_cancel₀ hS.ne', one_smul] using hh.symm
  apply (measureReal_mono (s₂ := {b : n → ℂ |
      ENNReal.ofReal (84/M + π*normalTensorMomentRadius (Fintype.card n) M δ *
        sqrt (5+(π/2)*log M)) < wassersteinEDistOne (normalEmpiricalSpectralLaw hB)
        ((normalSpectralDensityProgram b M).run (matrixAdjointOracle B))}) ?_).trans
    (measureReal_wassersteinEDistOne_normalSpectralDensityProgram_gt_le hB hBn hM hδ hδ1)
  intro b hbad
  change ENNReal.ofReal _ < _ at hbad
  change ENNReal.ofReal _ < _
  by_contra hnot
  have hs := le_of_not_gt hnot
  have hw := wassersteinEDistOne_map_real_smul_le (normalEmpiricalSpectralLaw hB)
    ((normalSpectralDensityProgram b M).run (matrixAdjointOracle B)) hS
  rw [hlaw, ← run_normalScaledSpectralDensityProgram] at hw
  have hh := hw.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  rw [← ENNReal.ofReal_mul hS.le] at hh
  exact (not_lt_of_ge hh) hbad

end NLAlib
