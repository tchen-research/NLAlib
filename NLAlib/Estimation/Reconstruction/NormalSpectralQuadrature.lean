import NLAlib.Estimation.Reconstruction.NormalSpectralReconstruction
import NLAlib.Probability.Transforms.TensorChebyshevQuadratureArithmetic
import NLAlib.ForMathlib.MeasureTheory.WassersteinMap

/-!
# Finite positive normal spectral reconstruction from native queries

The observed moment table is read by the existing `normalMomentTable` adapter.
Two separable scalar transforms produce the actual positive density samples.
The finite output keeps the same `4M` matrix/adjoint query budget.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix Real
open scoped ENNReal NNReal
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Oracle-free positive quadrature readout from the observed mixed-moment table. -/
def normalMomentQuadratureLaw (M : ℕ) (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) : Measure ℂ :=
  (tensorChebyshevQuadratureLawOfMoments M
    (fun j k => normalMomentTable M Γ ![j.val,k.val])).map Complex.orthonormalBasisOneI.repr.symm

/-- The finite native-query output is exactly the sampled positive kernel law. -/
theorem normalMomentQuadratureLaw_run_eq_native
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A≤1) (M : ℕ) :
    normalMomentQuadratureLaw M ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) =
      (tensorChebyshevQuadratureLaw (normalSpectralCubeLaw hA b) M).map
        Complex.orthonormalBasisOneI.repr.symm := by
  have := isProbabilityMeasure_normalSpectralCubeLaw hA b hb hbound
  unfold normalMomentQuadratureLaw
  have he : (fun j k : Fin (M+1) => normalMomentTable M
      ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) ![j.val,k.val]) =
      fun j k : Fin (M+1) => tensorChebyshevMoment (normalSpectralCubeLaw hA b) ![j.val,k.val] := by
    funext j k
    apply normalMomentTable_run_eq_tensorMoment hA b hbound M
    intro i
    fin_cases i
    · exact j.isLt
    · exact k.isLt
  rw [he,tensorChebyshevQuadratureLawOfMoments_eq_native]

/-- The native finite output samples the existing reconstructed density on the
actual Gauss grid; it is the same density postprocessor as the continuous output. -/
theorem normalMomentQuadratureLaw_run_eq_density_samples
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A≤1) (M : ℕ) :
    normalMomentQuadratureLaw M ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) =
      (∑ σ : Fin 2 → Fin (M+1),
        (((π/(M+1))^2)*normalMomentDensity M
          ((normalMixedMomentProgram b M).run (matrixAdjointOracle A))
            (WithLp.ofLp (tensorGaussChebyshevNode (M+1) σ))).toNNReal •
          Measure.dirac (tensorGaussChebyshevNode (M+1) σ)).map
            Complex.orthonormalBasisOneI.repr.symm := by
  rw [normalMomentQuadratureLaw_run_eq_native hA b hb hbound,tensorChebyshevQuadratureLaw]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [tensorChebyshevQuadratureWeight,normalMomentDensity_run_eq_smoothedDensity hA b hb hbound]
  simp

omit [Fintype n] [DecidableEq n] in
/-- All supplied observed tables admit the actual separable cubic scalar readout.
atlas: normal-spectral-density-query (partial) -/
theorem normalMomentQuadratureScalarWork_le (M : ℕ)
    (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) :
    tensorChebyshevQuadratureScalarWork M (fun j k => normalMomentTable M Γ ![j.val,k.val]) ≤
      9*(M+1)^3 := tensorChebyshevQuadratureScalarWork_le _ _

/-- The positive finite-law strategy is selected before receiving the oracle. -/
def normalSpectralQuadratureProgram (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (Measure ℂ)
      (hermitianPartChebyshevCost M+hermitianPartChebyshevCost M) :=
  (normalMixedMomentProgram b M).map (normalMomentQuadratureLaw M)

/-- Exact native output of the charged two-sided finite-law strategy. -/
theorem run_normalSpectralQuadratureProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A≤1) (M : ℕ) :
    (normalSpectralQuadratureProgram b M).run (matrixAdjointOracle A) =
      (tensorChebyshevQuadratureLaw (normalSpectralCubeLaw hA b) M).map
        Complex.orthonormalBasisOneI.repr.symm := by
  rw [normalSpectralQuadratureProgram,QueryProgram.run_map]
  exact normalMomentQuadratureLaw_run_eq_native hA b hb hbound M

/-- Valid native inputs give an actual finite probability law. -/
theorem isProbabilityMeasure_run_normalSpectralQuadratureProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A≤1) (M : ℕ) :
    IsProbabilityMeasure ((normalSpectralQuadratureProgram b M).run (matrixAdjointOracle A)) := by
  rw [run_normalSpectralQuadratureProgram hA b hb hbound]
  have := isProbabilityMeasure_normalSpectralCubeLaw hA b hb hbound
  exact Measure.isProbabilityMeasure_map
    Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.aemeasurable

/-- Finite positive quadrature adds at most `24/M` transport error in the complex
plane; isometric coordinates preserve the Euclidean constant exactly. -/
theorem wassersteinEDistOne_run_normalSpectralQuadratureProgram_le
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A≤1) {M : ℕ} (hM : 1≤M) :
    wassersteinEDistOne ((normalSpectralQuadratureProgram b M).run (matrixAdjointOracle A))
      (normalSpectralDensityKernelLaw hA b M) ≤ ENNReal.ofReal (24/(M : ℝ)) := by
  rw [run_normalSpectralQuadratureProgram hA b hb hbound,normalSpectralDensityKernelLaw]
  have := isProbabilityMeasure_normalSpectralCubeLaw hA b hb hbound
  have h := wassersteinEDistOne_map_le_mul
    (tensorChebyshevQuadratureLaw (normalSpectralCubeLaw hA b) M)
    (tensorChebyshevSmoothedLaw (normalSpectralCubeLaw hA b) M)
    (K := 1) one_ne_zero Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitz
  simp only [ENNReal.coe_one,one_mul] at h
  exact h.trans (wassersteinEDistOne_tensorChebyshevQuadratureLaw_le _ hM)

/-- The actual native finite output has at most `(M+1)^2` complex atoms. -/
theorem exists_finite_support_run_normalSpectralQuadratureProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A≤1) (M : ℕ) :
    ∃ s : Finset ℂ,s.card≤(M+1)^2 ∧
      (normalSpectralQuadratureProgram b M).run (matrixAdjointOracle A) (s : Set ℂ)ᶜ = 0 := by
  classical
  rw [run_normalSpectralQuadratureProgram hA b hb hbound]
  obtain ⟨s,hcard,hnull⟩ := exists_finite_support_tensorChebyshevQuadratureLaw
    (normalSpectralCubeLaw hA b) M
  let t := s.image Complex.orthonormalBasisOneI.repr.symm
  refine ⟨t,Finset.card_image_le.trans (by simpa using hcard),?_⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hh : ∀ᵐ z ∂(tensorChebyshevQuadratureLaw (normalSpectralCubeLaw hA b) M).map
      Complex.orthonormalBasisOneI.repr.symm,z ∈ (t : Set ℂ) := by
    apply (ae_map_iff Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.aemeasurable
      (p := fun z : ℂ => z ∈ (t : Set ℂ)) t.finite_toSet.measurableSet).mpr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    have hx' : x ∈ s := by simpa only [Set.mem_compl_iff,not_not,Finset.mem_coe] using hx
    exact Finset.mem_image.mpr ⟨x,hx',rfl⟩
  filter_upwards [hh] with z hz
  exact fun he => he hz

end NLAlib
