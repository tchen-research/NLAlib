import NLAlib.Matrix.Functions.OperatorCapacityCertificate
import NLAlib.Matrix.Functions.OperatorCapacityAdjoint

/-!
# Unital near-balance certificate for Kraus families

For a finite Kraus family `A` with unital normalization
`∑ i, A i * (A i)† = 1` (equivalently `krausMap A 1 = 1`), the adjoint
family `A†` is trace preserving.  Applying the trace-preserving balance
certificate `frobSq_krausMap_defect_le_of_exp_neg_le_operatorCapacity` to the
adjoint family `A†`, together with equality of the two operator capacities,
yields the unital counterpart: if the operator capacity of `krausMap A` is at
least `exp (-eps)` with `eps ≤ 1/6`, then the sum of the squared Frobenius
defects of the primal and adjoint normalizations is at most `6 * eps`.

This is the unital branch of Garg--Gurvits--Oliveira--Wigderson (2015),
Lemma 3.6.  It does **not** claim the full near-balance card: the lower capacity
bound and the rank-nondecrease converse remain separate results.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unital near-balance certificate for a finite Kraus family `A` with
`∑ i, A i * (A i)† = 1` (equivalently `krausMap A 1 = 1`): if the operator
capacity of the original family `A` is at least `exp (-eps)` with
`eps ≤ 1 / 6`, then the squared Frobenius defect `frobSq (krausMap A 1 - 1)`
plus the adjoint defect is at most `6 * eps`.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.6.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem frobSq_krausMap_unital_defect_le_of_exp_neg_le_operatorCapacity
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap A 1 = 1)
    {eps : ℝ} (heps : eps ≤ 1 / 6)
    (hcap : Real.exp (-eps) ≤ operatorCapacity (krausMap A)) :
    frobSq (krausMap A 1 - 1) +
      frobSq (krausMap (fun i => (A i).conjTranspose) 1 - 1) ≤ 6 * eps := by
  have hA' : krausMap (fun i => ((A i).conjTranspose).conjTranspose) 1 = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hA
  have hcap' : Real.exp (-eps) ≤
      operatorCapacity (krausMap (fun i => (A i).conjTranspose)) := by
    rw [← operatorCapacity_krausMap_conjTranspose A]
    exact hcap
  have h := frobSq_krausMap_defect_le_of_exp_neg_le_operatorCapacity
    (fun i => (A i).conjTranspose) hA' heps hcap'
  simpa only [Matrix.conjTranspose_conjTranspose, add_comm] using h

end NLAlib
