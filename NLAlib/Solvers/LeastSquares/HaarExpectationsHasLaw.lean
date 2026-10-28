import NLAlib.Solvers.LeastSquares.HaarExpectations
import NLAlib.Solvers.LeastSquares.HaarLawTransport

/-!
# Exact Haar least-squares expectations on arbitrary sample spaces

The native real/complex frame theorems transport to random ambient matrices
with exactly the compact-Haar frame law, or directly to the adjoint sketch law.
All matrix ranks and right-hand-side shapes of the native theorem are retained.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
private local instance {K a b : Type*} [RCLike K] [Fintype a] [Fintype b] [DecidableEq b] :
    NormedSpace ℝ (Matrix a b K) := NormedSpace.restrictScalars ℝ K (Matrix a b K)

private local instance {K a b : Type*} [RCLike K] [Fintype a] [Fintype b] :
    SecondCountableTopology (Matrix a b K) := inferInstanceAs (SecondCountableTopology (a → b → K))

open scoped Matrix.Norms.L2Operator in
/-- Native ambient real Haar matrices give the exact integrable estimator mean.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_sketchAndSolve_haar_real_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (hs : A.rank+2≤ell) (helln : ell≤n) {Z : Ω → Matrix (Fin n) (Fin ell) ℝ}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw ℝ n ell helln) μ) :
    Integrable (fun ω => sketchAndSolve A (Z ω)ᴴ B) μ ∧
      (∫ ω,sketchAndSolve A (Z ω)ᴴ B ∂μ)=moorePenroseInverse A*B := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_sketchAndSolve_haar_real A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarFrameMatrixLaw_of_hasLaw hZ
    (fun Q => sketchAndSolve A Qᴴ B)
    ((measurable_sketchAndSolve A B).comp Matrix.measurable_conjTranspose) hi
  exact ⟨hμ,hE.trans hv⟩

open scoped Matrix.Norms.L2Operator in
/-- Native ambient complex Haar matrices give the exact integrable estimator mean.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_sketchAndSolve_haar_complex_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (hs : A.rank+1≤ell) (helln : ell≤n) {Z : Ω → Matrix (Fin n) (Fin ell) ℂ}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw ℂ n ell helln) μ) :
    Integrable (fun ω => sketchAndSolve A (Z ω)ᴴ B) μ ∧
      (∫ ω,sketchAndSolve A (Z ω)ᴴ B ∂μ)=moorePenroseInverse A*B := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_sketchAndSolve_haar_complex A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarFrameMatrixLaw_of_hasLaw hZ
    (fun Q => sketchAndSolve A Qᴴ B)
    ((measurable_sketchAndSolve A B).comp Matrix.measurable_conjTranspose) hi
  exact ⟨hμ,hE.trans hv⟩

/-- The full finite-dimensional real Haar residual factor on any sample space.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_real_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (hs : A.rank+2≤ell) (helln : ell≤n) {Z : Ω → Matrix (Fin n) (Fin ell) ℝ}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw ℝ n ell helln) μ) :
    Integrable (fun ω => frobSq (B-A*sketchAndSolve A (Z ω)ᴴ B)) μ ∧
      (∫ ω,frobSq (B-A*sketchAndSolve A (Z ω)ᴴ B) ∂μ)=
        (1+(((n:ℝ)-ell)/((n:ℝ)-A.rank))*((A.rank:ℝ)/((ell:ℝ)-A.rank-1)))*
          frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_residual_sketchAndSolve_haar_real A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarFrameMatrixLaw_of_hasLaw hZ
    (fun Q => frobSq (B-A*sketchAndSolve A Qᴴ B))
    ((measurable_frobSq_sketchAndSolve_residual A B).comp Matrix.measurable_conjTranspose) hi
  exact ⟨hμ,hE.trans hv⟩

/-- The full finite-dimensional complex Haar residual factor on any sample space.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_complex_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (hs : A.rank+1≤ell) (helln : ell≤n) {Z : Ω → Matrix (Fin n) (Fin ell) ℂ}
    (hZ : HasLaw Z (unitaryHaarFrameMatrixLaw ℂ n ell helln) μ) :
    Integrable (fun ω => frobSq (B-A*sketchAndSolve A (Z ω)ᴴ B)) μ ∧
      (∫ ω,frobSq (B-A*sketchAndSolve A (Z ω)ᴴ B) ∂μ)=
        (1+(((n:ℝ)-ell)/((n:ℝ)-A.rank))*((A.rank:ℝ)/((ell:ℝ)-A.rank)))*
          frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_residual_sketchAndSolve_haar_complex A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarFrameMatrixLaw_of_hasLaw hZ
    (fun Q => frobSq (B-A*sketchAndSolve A Qᴴ B))
    ((measurable_frobSq_sketchAndSolve_residual A B).comp Matrix.measurable_conjTranspose) hi
  exact ⟨hμ,hE.trans hv⟩

open scoped Matrix.Norms.L2Operator in
/-- The same real native mean when the random matrix is already the sketch. -/
theorem integrable_and_integral_sketchAndSolve_haar_real_of_adjoint_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (hs : A.rank+2≤ell) (helln : ell≤n) {S : Ω → Matrix (Fin ell) (Fin n) ℝ}
    (hS : HasLaw S (unitaryHaarAdjointSketchLaw ℝ n ell helln) μ) :
    Integrable (fun ω => sketchAndSolve A (S ω) B) μ ∧
      (∫ ω,sketchAndSolve A (S ω) B ∂μ)=moorePenroseInverse A*B := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_sketchAndSolve_haar_real A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarAdjointSketchLaw_of_hasLaw hS
    (fun Q => sketchAndSolve A Q B) (measurable_sketchAndSolve A B) hi
  exact ⟨hμ,hE.trans hv⟩

open scoped Matrix.Norms.L2Operator in
/-- The same complex native mean when the random matrix is already the sketch. -/
theorem integrable_and_integral_sketchAndSolve_haar_complex_of_adjoint_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (hs : A.rank+1≤ell) (helln : ell≤n) {S : Ω → Matrix (Fin ell) (Fin n) ℂ}
    (hS : HasLaw S (unitaryHaarAdjointSketchLaw ℂ n ell helln) μ) :
    Integrable (fun ω => sketchAndSolve A (S ω) B) μ ∧
      (∫ ω,sketchAndSolve A (S ω) B ∂μ)=moorePenroseInverse A*B := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_sketchAndSolve_haar_complex A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarAdjointSketchLaw_of_hasLaw hS
    (fun Q => sketchAndSolve A Q B) (measurable_sketchAndSolve A B) hi
  exact ⟨hμ,hE.trans hv⟩

/-- Real Haar residual expectation when the supplied random matrix is the sketch. -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_real_of_adjoint_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (hs : A.rank+2≤ell) (helln : ell≤n) {S : Ω → Matrix (Fin ell) (Fin n) ℝ}
    (hS : HasLaw S (unitaryHaarAdjointSketchLaw ℝ n ell helln) μ) :
    Integrable (fun ω => frobSq (B-A*sketchAndSolve A (S ω) B)) μ ∧
      (∫ ω,frobSq (B-A*sketchAndSolve A (S ω) B) ∂μ)=
        (1+(((n:ℝ)-ell)/((n:ℝ)-A.rank))*((A.rank:ℝ)/((ell:ℝ)-A.rank-1)))*
          frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_residual_sketchAndSolve_haar_real A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarAdjointSketchLaw_of_hasLaw hS
    (fun Q => frobSq (B-A*sketchAndSolve A Q B)) (measurable_frobSq_sketchAndSolve_residual A B) hi
  exact ⟨hμ,hE.trans hv⟩

/-- Complex Haar residual expectation when the supplied random matrix is the sketch. -/
theorem integrable_and_integral_frobSq_residual_sketchAndSolve_haar_complex_of_adjoint_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d p ell : ℕ}
    (A : Matrix (Fin n) (Fin d) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (hs : A.rank+1≤ell) (helln : ell≤n) {S : Ω → Matrix (Fin ell) (Fin n) ℂ}
    (hS : HasLaw S (unitaryHaarAdjointSketchLaw ℂ n ell helln) μ) :
    Integrable (fun ω => frobSq (B-A*sketchAndSolve A (S ω) B)) μ ∧
      (∫ ω,frobSq (B-A*sketchAndSolve A (S ω) B) ∂μ)=
        (1+(((n:ℝ)-ell)/((n:ℝ)-A.rank))*((A.rank:ℝ)/((ell:ℝ)-A.rank)))*
          frobSq ((1-A*moorePenroseInverse A)*B) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_residual_sketchAndSolve_haar_complex A B hs helln
  obtain ⟨hμ,hE⟩ := integrable_and_integral_comp_unitaryHaarAdjointSketchLaw_of_hasLaw hS
    (fun Q => frobSq (B-A*sketchAndSolve A Q B)) (measurable_frobSq_sketchAndSolve_residual A B) hi
  exact ⟨hμ,hE.trans hv⟩

end NLAlib
