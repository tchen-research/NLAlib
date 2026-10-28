import NLAlib.Estimation.Reconstruction.NormalMixedQuery
import NLAlib.Probability.Transforms.ChebyshevCubeSmoothing

/-!
# Positive normal spectral reconstruction from the observed moment table

The output density uses only the finite cross-Gram array. For native moments it
is exactly the actual positive Jackson-kernel mixture, so positivity and mass
one are consequences of the input model, rather than assumptions on an array.
Source: MMSUW 2026, Algorithms 1--2 and Theorem 2.5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Read a retained tensor mode from the observed complex cross-Gram table. -/
def normalMomentTable (M : ℕ) (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ)
    (α : Fin 2 → ℕ) : ℝ :=
  if h : ∀ i, α i < M+1 then (Γ ⟨α 0,h 0⟩ ⟨α 1,h 1⟩).re else 0

/-- The explicit finite density computed from the observed array. -/
def normalMomentDensity (M : ℕ) (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ)
    (x : Fin 2 → ℝ) : ℝ :=
  ∑ α ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M+1)),
    tensorChebyshevJacksonDamping M α * tensorNormalizedChebyshev α x * normalMomentTable M Γ α

/-- Interpret the finite density in the complex plane through the isometric
real/imaginary coordinates. The definition uses no matrix or spectral data. -/
def normalMomentDensityLaw (M : ℕ) (Γ : Matrix (Fin (M+1)) (Fin (M+1)) ℂ) : Measure ℂ :=
  (((Measure.pi (fun _ : Fin 2 => Polynomial.Chebyshev.measureT)).withDensity
    (fun x => ENNReal.ofReal (normalMomentDensity M Γ x))).map (WithLp.toLp 2)).map
      Complex.orthonormalBasisOneI.repr.symm

/-- The native cube input of the positive kernel reconstruction. -/
def normalSpectralCubeLaw {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) :
    Measure (chebyshevCube (Fin 2)) := chebyshevCubeLift (normalCoordinateSpectralLaw hA b)

/-- The native contractive spectral cube law has mass one for a unit start. -/
theorem isProbabilityMeasure_normalSpectralCubeLaw
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A ≤ 1) : IsProbabilityMeasure (normalSpectralCubeLaw hA b) := by
  have := isProbabilityMeasure_normalCoordinateSpectralLaw hA b hb
  exact isProbabilityMeasure_chebyshevCubeLift (normalCoordinateSpectralLaw hA b)
    (ae_mem_chebyshevCube_normalCoordinateSpectralLaw hA b hbound)

/-- The actual positive kernel mixture, in the complex plane. -/
def normalSpectralDensityKernelLaw {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A)
    (b : n → ℂ) (M : ℕ) : Measure ℂ :=
  (tensorChebyshevSmoothedLaw (normalSpectralCubeLaw hA b) M).map
    Complex.orthonormalBasisOneI.repr.symm

/-- Every observed retained entry is the actual cube-law tensor moment. -/
theorem normalMomentTable_run_eq_tensorMoment
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hbound : specNorm A ≤ 1)
    (M : ℕ) (α : Fin 2 → ℕ) (hα : ∀ i, α i < M+1) :
    normalMomentTable M ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) α =
      tensorChebyshevMoment (normalSpectralCubeLaw hA b) α := by
  rw [normalMomentTable, dif_pos hα, tensorChebyshevMoment, normalSpectralCubeLaw,
    chebyshevCubeLift]
  have hi := integral_subtype_comap (μ := normalCoordinateSpectralLaw hA b)
    isCompact_chebyshevCube.measurableSet
    (fun x : EuclideanSpace ℝ (Fin 2) => tensorNormalizedChebyshev α (WithLp.ofLp x))
  rw [Measure.restrict_eq_self_of_ae_mem
    (ae_mem_chebyshevCube_normalCoordinateSpectralLaw hA b hbound)] at hi
  rw [hi]
  have he := congrArg Complex.re
    (run_normalMixedMomentProgram_eq_coordinate_integral hA b M ⟨α 0,hα 0⟩ ⟨α 1,hα 1⟩)
  simpa only [integral_complex_ofReal, Complex.ofReal_re, tensorNormalizedChebyshev,
    Fin.prod_univ_two] using he

/-- The observed finite density is exactly the native positive kernel density. -/
theorem normalMomentDensity_run_eq_smoothedDensity
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A ≤ 1) (M : ℕ) (x : Fin 2 → ℝ) :
    normalMomentDensity M ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) x =
      tensorChebyshevSmoothedDensity (normalSpectralCubeLaw hA b) M x := by
  have := isProbabilityMeasure_normalSpectralCubeLaw hA b hb hbound
  rw [normalMomentDensity, tensorChebyshevSmoothedDensity_eq_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [normalMomentTable_run_eq_tensorMoment hA b hbound M α
    (fun i => Finset.mem_range.mp ((Fintype.mem_piFinset.mp hα) i))]

/-- Native query output is the actual kernel-mixture law.
atlas: normal-spectral-density-query (partial) -/
theorem normalMomentDensityLaw_run_eq_kernelLaw
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A ≤ 1) (M : ℕ) :
    normalMomentDensityLaw M ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) =
      normalSpectralDensityKernelLaw hA b M := by
  have := isProbabilityMeasure_normalSpectralCubeLaw hA b hb hbound
  rw [normalMomentDensityLaw, normalSpectralDensityKernelLaw,
    tensorChebyshevSmoothedLaw_eq_map_withDensity]
  simp_rw [normalMomentDensity_run_eq_smoothedDensity hA b hb hbound]

/-- An oracle-independent strategy: two vector recurrences followed by the
explicit positive finite density reconstruction. -/
def normalSpectralDensityProgram (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (Measure ℂ)
      (hermitianPartChebyshevCost M+hermitianPartChebyshevCost M) :=
  (normalMixedMomentProgram b M).map (normalMomentDensityLaw M)

/-- The strategy's actual result equals the native positive reconstruction. -/
theorem run_normalSpectralDensityProgram
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (hb : ‖WithLp.toLp 2 b‖=1)
    (hbound : specNorm A ≤ 1) (M : ℕ) :
    (normalSpectralDensityProgram b M).run (matrixAdjointOracle A) =
      normalSpectralDensityKernelLaw hA b M := by
  rw [normalSpectralDensityProgram, QueryProgram.run_map]
  exact normalMomentDensityLaw_run_eq_kernelLaw hA b hb hbound M

end NLAlib
