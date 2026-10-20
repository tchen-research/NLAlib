import NLAlib.Probability.Free.WordChebyshev
import NLAlib.ForMathlib.RingTheory.Polynomial.ChebyshevSequence
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.List.ChainOfFn

/-!
# Genuine alternating centered polynomial moments of the concrete fields

Each arbitrary one-variable polynomial is expanded in the native monic
rescaled Chebyshev basis. Its actual vacuum mean is exactly its zeroth basis
coordinate. Multilinearity therefore reduces every nonempty alternating
product of centered polynomials to the proved positive-degree block identity.

The conclusion quantifies arbitrary centered polynomials in the actual
operators, not merely their first moments. No independence or free-family
property is assumed. Norm-closed single-generator algebras are treated separately.

Source: Nica--Speicher, Lectures on the Combinatorics of Free Probability,
the concrete full-Fock freeness mechanism of Propositions 7.15--7.18.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical

namespace NLAlib

variable {ι : Type*}
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι

private noncomputable def chebyshevWordBasis : Module.Basis ℕ ℂ (Polynomial ℂ) :=
  (Polynomial.Chebyshev.chebyshevSsequence ℂ).basis (fun n => by
    simpa only [Polynomial.Chebyshev.chebyshevSsequence_apply,
      (Polynomial.Chebyshev.monic_S_natCast ℂ n).leadingCoeff] using isUnit_one)

private theorem chebyshevWordBasis_apply (n : ℕ) :
    chebyshevWordBasis n = Polynomial.Chebyshev.S ℂ (n : ℤ) := by
  exact Polynomial.Sequence.basis_eq_self _ _ n

private theorem wordVacuumExpectation_aeval_eq_chebyshev_repr_zero
    (i : ι) (P : Polynomial ℂ) :
    wordVacuumExpectation ι (Polynomial.aeval (wordField i) P) =
      chebyshevWordBasis.repr P 0 := by
  let L : Polynomial ℂ →ₗ[ℂ] ℂ := (wordVacuumExpectation ι).toLinearMap.comp
    (Polynomial.aeval (wordField i)).toLinearMap
  let C : Polynomial ℂ →ₗ[ℂ] ℂ := (Finsupp.lapply 0).comp chebyshevWordBasis.repr.toLinearMap
  have hLC : L = C := by
    apply chebyshevWordBasis.ext
    intro n
    change wordVacuumExpectation ι (Polynomial.aeval (wordField i) (chebyshevWordBasis n)) =
      chebyshevWordBasis.repr (chebyshevWordBasis n) 0
    rw [Module.Basis.repr_self_apply, chebyshevWordBasis_apply,
      wordVacuumExpectation_aeval_chebyshevS_wordField]
  exact congrArg (fun f : Polynomial ℂ →ₗ[ℂ] ℂ => f P) hLC

private noncomputable def wordPolynomialMoment {m : ℕ} (color : Fin m → ι) :
    MultilinearMap ℂ (fun _ : Fin m => Polynomial ℂ) ℂ :=
  (wordVacuumExpectation ι).toLinearMap.compMultilinearMap
    ((MultilinearMap.mkPiAlgebraFin ℂ m B).compLinearMap
      (fun j => (Polynomial.aeval (wordField (color j))).toLinearMap))

/-- Every genuine nonempty alternating product of arbitrary centered
one-variable polynomials in the concrete fields has zero vacuum expectation.
Centering is with the actual vacuum functional; no freeness premise is supplied. -/
theorem wordVacuumExpectation_ofFn_prod_aeval_eq_zero
    {m : ℕ} (hm : 0 < m) (color : Fin m → ι)
    (hchain : (List.ofFn color).IsChain (· ≠ ·)) (P : Fin m → Polynomial ℂ)
    (hCenter : ∀ j, wordVacuumExpectation ι (Polynomial.aeval (wordField (color j)) (P j)) = 0) :
    wordVacuumExpectation ι
      ((List.ofFn (fun j => Polynomial.aeval (wordField (color j)) (P j))).prod) = 0 := by
  let c : Fin m → ℕ →₀ ℂ := fun j => chebyshevWordBasis.repr (P j)
  let F := wordPolynomialMoment color
  have hZero (j : Fin m) : c j 0 = 0 := by
    change chebyshevWordBasis.repr (P j) 0 = 0
    rw [← wordVacuumExpectation_aeval_eq_chebyshev_repr_zero (color j) (P j)]
    exact hCenter j
  have hExpansion (j : Fin m) :
      (∑ n ∈ (c j).support, c j n • chebyshevWordBasis n) = P j := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      chebyshevWordBasis.linearCombination_repr (P j)
  change F P = 0
  have hP : P = fun j => ∑ n ∈ (c j).support, c j n • chebyshevWordBasis n := by
    funext j
    exact (hExpansion j).symm
  rw [hP, F.map_sum_finset]
  apply Finset.sum_eq_zero
  intro degree hDegree
  rw [F.map_smul_univ]
  have hPos (j : Fin m) : 0 < degree j := by
    have hMem := (Fintype.mem_piFinset.mp hDegree) j
    have hCoeff := Finsupp.mem_support_iff.mp hMem
    by_contra hNot
    have hDeg : degree j = 0 := Nat.eq_zero_of_not_pos hNot
    exact hCoeff (by simpa only [hDeg] using hZero j)
  have hBlocksNe : List.ofFn (fun j => (color j, degree j)) ≠ [] := by
    intro h
    have hLen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hLen
    omega
  have hBlocksPos : ∀ b ∈ List.ofFn (fun j => (color j, degree j)), 0 < b.2 := by
    intro b hb
    rcases List.mem_ofFn.mp hb with ⟨j, rfl⟩
    exact hPos j
  have hBlocksChain : (List.ofFn (fun j => (color j, degree j))).IsChain
      (fun b d => b.1 ≠ d.1) := by
    apply List.isChain_ofFn.mpr
    intro k hk
    exact (List.isChain_ofFn.mp hchain) k hk
  have hBlock := wordVacuumExpectation_list_prod_aeval_chebyshevS_wordField_eq_zero
    (List.ofFn (fun j => (color j, degree j))) hBlocksNe hBlocksPos hBlocksChain
  have hF : F (fun j => chebyshevWordBasis (degree j)) = 0 := by
    change wordVacuumExpectation ι ((List.ofFn (fun j =>
      Polynomial.aeval (wordField (color j)) (chebyshevWordBasis (degree j)))).prod) = 0
    simp_rw [chebyshevWordBasis_apply]
    simpa only [List.map_ofFn, Function.comp_def] using hBlock
  simp only [hF, smul_zero]

end NLAlib
