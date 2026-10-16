import NLAlib.Matrix.Structured.FiniteGroupCayleyNorm
import NLAlib.Probability.Gaussian.Basic.ComplexUnitary

/-! # Gaussian finite group Fourier blocks

The actual normalized Fourier blocks have independent circular complex
Gaussian entries across every representation label. The deterministic Fourier
decomposition holds pointwise on the original probability space and therefore
implies the stated block and norm identities in law.
Source: Bandeira--Kunisky--Mixon--Zeng (2024), Section 3, Lemma 7;
`gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]
  [∀ p, Nonempty (D p)] [Fintype P] [DecidableEq P]
  (ρ : ∀ p, Representation ℂ G (D p → ℂ)) [∀ p, Representation.IsIrreducible (ρ p)]

/-- Concatenated entries of the actual normalized Fourier blocks have the full
circular complex Gaussian product law. Every real and imaginary coordinate
has variance one, and all coordinates are jointly independent.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem hasLaw_finiteGroupNormalizedBlocks
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q))) :
    HasLaw (fun z : G → ℂ => fun t : FiniteGroupFourierIndex D =>
      finiteGroupNormalizedBlock ρ z t.1 t.2.1 t.2.2)
      (circularComplexGaussianVector (FiniteGroupFourierIndex D))
      (circularComplexGaussianVector G) := by
  have hF : HasOrthonormalCols (finiteGroupCoefficientTransform ρ)ᴴ := by
    simpa only [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose] using
      finiteGroupCoefficientTransform_mul_conjTranspose ρ hu hne
  simpa only [finiteGroupNormalizedBlock_apply] using
    hasLaw_mulVec_circularComplexGaussianVector_orthonormalRows
      (finiteGroupCoefficientTransform ρ) hF

/-- The full normalized Fourier-block product law transports to arbitrary
sample spaces through the actual joint circular complex coefficient law.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem hasLaw_finiteGroupNormalizedBlocks_of_hasLaw
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → G → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector G) μ) :
    HasLaw (fun ω => fun t : FiniteGroupFourierIndex D =>
      finiteGroupNormalizedBlock ρ (Z ω) t.1 t.2.1 t.2.2)
      (circularComplexGaussianVector (FiniteGroupFourierIndex D)) μ :=
  (hasLaw_finiteGroupNormalizedBlocks ρ hu hne).comp hZ

/-- Every normalized block entry has the same circular complex Gaussian law
as an input coefficient, with no factor `1/sqrt(2)` in the convention. -/
theorem hasLaw_finiteGroupNormalizedBlock_entry_of_hasLaw
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → G → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector G) μ) (p : P) (a b : D p) :
    HasLaw (fun ω => finiteGroupNormalizedBlock ρ (Z ω) p a b)
      circularComplexGaussian μ :=
  (hasLaw_finiteGroupNormalizedBlocks_of_hasLaw ρ hu hne hZ).hasLaw_eval_circularComplexGaussian
    ⟨p, a, b⟩

/-- All entries, including entries from different representation blocks, are
independent as complex-valued random variables.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem iIndepFun_finiteGroupNormalizedBlocks_of_hasLaw
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → G → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector G) μ) :
    iIndepFun (fun (t : FiniteGroupFourierIndex D) ω =>
      finiteGroupNormalizedBlock ρ (Z ω) t.1 t.2.1 t.2.2) μ :=
  (hasLaw_finiteGroupNormalizedBlocks_of_hasLaw ρ hu hne hZ).iIndepFun_eval_of_circularComplexGaussianVector

/-- Every real and imaginary block entry together has the joint independent
standard-real-Gaussian law, certifying the circular normalization exactly.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem hasLaw_realify_finiteGroupNormalizedBlocks_of_hasLaw
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → G → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector G) μ) :
    HasLaw (fun ω => realifyVector (fun t : FiniteGroupFourierIndex D =>
      finiteGroupNormalizedBlock ρ (Z ω) t.1 t.2.1 t.2.2))
      (gaussianVector (FiniteGroupFourierIndex D ⊕ FiniteGroupFourierIndex D)) μ :=
  hasLaw_realifyVector_circularComplexGaussianVector.comp
    (hasLaw_finiteGroupNormalizedBlocks_of_hasLaw ρ hu hne hZ)

/-- There are deterministic unitary Fourier coordinates and actual independent
circular complex Gaussian blocks on the original sample space. The Cayley
matrix and its norm satisfy the source decomposition pointwise, which is
stronger than both requested identities in law. Multiplicity and representation
coordinates are distinct, and the factors are exactly `sqrt(N/d)`.
Source: Bandeira--Kunisky--Mixon--Zeng (2024), Section 3, Lemma 7.
atlas: gaussian-cayley-fourier-block-law -/
theorem exists_finiteGroupCayley_fourier_gaussian_blocks [Nonempty P]
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → G → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector G) μ) :
    ∃ (U : Matrix G (FiniteGroupFourierIndex D) ℂ)
      (B : Ω → ∀ p, Matrix (D p) (D p) ℂ),
      HasOrthonormalCols U ∧ HasOrthonormalCols Uᴴ ∧
      HasLaw (fun ω => fun t : FiniteGroupFourierIndex D => B ω t.1 t.2.1 t.2.2)
        (circularComplexGaussianVector (FiniteGroupFourierIndex D)) μ ∧
      (∀ ω, finiteGroupCayleyMatrix (Z ω) = U *
        Matrix.blockDiagonal' (fun p => (1 : Matrix (D p) (D p) ℂ) ⊗ₖ
          (Real.sqrt ((Fintype.card G : ℝ) / Fintype.card (D p)) • B ω p)) * Uᴴ) ∧
      (∀ ω, specNorm (finiteGroupCayleyMatrix (Z ω)) =
        Finset.univ.sup' Finset.univ_nonempty (fun p =>
          Real.sqrt ((Fintype.card G : ℝ) / Fintype.card (D p)) * specNorm (B ω p))) := by
  refine ⟨finiteGroupFourierMatrix ρ, (fun ω => finiteGroupNormalizedBlock ρ (Z ω)),
    finiteGroupFourierMatrix_hasOrthonormalCols ρ hu hne, ?_,
    hasLaw_finiteGroupNormalizedBlocks_of_hasLaw ρ hu hne hZ, ?_, ?_⟩
  · simpa only [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose] using
      finiteGroupFourierMatrix_mul_conjTranspose ρ hu hne hcomplete
  · intro ω
    exact finiteGroupCayleyMatrix_eq_fourier_normalized_blocks ρ hu hne hcomplete (Z ω)
  · intro ω
    exact specNorm_finiteGroupCayleyMatrix_eq_max_normalized_blocks ρ hu hne hcomplete (Z ω)

end NLAlib
