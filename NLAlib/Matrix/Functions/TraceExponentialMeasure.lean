import NLAlib.ForMathlib.MeasureTheory.ExponentialAtomic
import NLAlib.Matrix.Functions.TraceExpBounds
import NLAlib.Matrix.Spectral.CommutingHermitian

/-!
# Positive exponential measures for commuting Hermitian pencils

For commuting Hermitian `A,H`, simultaneous diagonalization constructs the
positive finite measure explicitly. This is a specialization of Stahl's BMV
theorem, not a proof of the noncommuting case. Generic derivative consequences
live in `ForMathlib/MeasureTheory/CompactExponential`.

Source: Stahl, *Proof of the BMV conjecture*, §1.3.1, formula (1.3).
Atlas: `trace-exponential-stahl` (partial: commuting matrices).
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In a simultaneous unitary diagonalization the trace pencil is an finite sum of scalar exponentials, for every real parameter.
Source: Stahl, §1.3.1; atlas `trace-exponential-stahl` (helper). -/
theorem traceExp_add_smul_eq_sum_of_diagonalization
    (A H U : Matrix ι ι ℂ) (a b : ι → ℝ) (hU : HasOrthonormalCols U)
    (hA : Uᴴ * A * U = diagonal (fun i => (a i : ℂ)))
    (hH : Uᴴ * H * U = diagonal (fun i => (b i : ℂ))) (t : ℝ) :
    traceExp (A + t • H) = ∑ i, Real.exp (a i + t * b i) := by
  let V : unitary (Matrix ι ι ℂ) :=
    ⟨Uᴴ, by simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
      using And.intro hU.mul_conjTranspose_self hU.conjTranspose_mul_self⟩
  have hconj : (V : Matrix ι ι ℂ) * (A + t • H) *
      (V : Matrix ι ι ℂ)ᴴ = diagonal (fun i => ((a i + t * b i : ℝ) : ℂ)) := by
    change Uᴴ * (A + t • H) * Uᴴᴴ = _
    rw [conjTranspose_conjTranspose, mul_add, add_mul, Matrix.mul_smul,
      Matrix.smul_mul, hA, hH]
    ext i j
    by_cases hij : i = j <;> simp [hij, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.real_smul]
  rw [← traceExp_unitary_conj V, hconj, traceExp_diagonal_real]

/-- A commuting Hermitian pencil admits a finite positive Borel measure on the
direction's spectral interval representing its trace exponential at every real
parameter. Includes repeated eigenvalues and the empty matrix, whose measure is
zero. This theorem does not cover noncommuting matrices.
Source: Stahl, §1.3.1, formula (1.3); atlas `trace-exponential-stahl` (partial).
atlas: trace-exponential-stahl (partial) -/
theorem exists_isCompactExpRepresentation_traceExp_of_commute
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAH : Commute A H) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => traceExp (A + t • H)) (lambdaMin H) (lambdaMax H) := by
  obtain ⟨U, a, b, hU, hUA, hUH⟩ :=
    exists_unitary_congruence_diagonal_of_commute hA hH hAH
  have hb (i : ι) : b i ∈ Icc (lambdaMin H) (lambdaMax H) := by
    have hi := mem_real_spectrum_of_orthonormal_congruence_diagonal H U b hU hUH i
    have hfin : (spectrum ℝ H).Finite := by
      rw [hH.spectrum_real_eq_range_eigenvalues]
      exact finite_range _
    exact ⟨csInf_le hfin.bddBelow hi, le_csSup hfin.bddAbove hi⟩
  refine ⟨exponentialAtomicMeasure a b, ?_⟩
  have hr := isCompactExpRepresentation_exponentialAtomicMeasure a b hb
  convert hr using 1
  funext t
  exact traceExp_add_smul_eq_sum_of_diagonalization A H U a b hU hUA hUH t

/-- Positive representations on a common compact interval pass to limits of
both matrices in a pencil. The positivity of approximating measures is retained
by compactness; no positivity or representation hypothesis is imposed on the
limiting pencil. Source: Stahl's approximation reduction; atlas
`trace-exponential-stahl` (partial).
atlas: trace-exponential-stahl (partial) -/
theorem exists_isCompactExpRepresentation_traceExp_of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot]
    (Aₙ Hₙ : I → Matrix ι ι ℂ) (A H : Matrix ι ι ℂ) (a b : ℝ)
    (hA : Filter.Tendsto Aₙ l (𝓝 A)) (hH : Filter.Tendsto Hₙ l (𝓝 H))
    (hrep : ∀ᶠ k in l, ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => traceExp (Aₙ k + t • Hₙ k)) a b) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => traceExp (A + t • H)) a b := by
  apply exists_isCompactExpRepresentation_of_tendsto a b _ _ hrep
  intro t
  exact continuous_traceExp.continuousAt.tendsto.comp
    (hA.add (Filter.Tendsto.smul tendsto_const_nhds hH))

end NLAlib
