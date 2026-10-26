import NLAlib.Matrix.Functions.OperatorCapacitySpectral
import NLAlib.ForMathlib.Analysis.Convex.StochasticProducts
import NLAlib.Matrix.Functions.OperatorCapacityUnitalCertificate

/-!
# Lower capacity bounds near doubly stochasticity

The spectral transition matrix reduces the lower bound for a normalized Kraus
map to the finite nonnegative matrix bound. This proves the capacity clause of
Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.4, in both normalization
orientations, without assuming that capacity is attained.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

private theorem re_det_eq_prod_eigenvalues {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M.det.re = ∏ i, hM.eigenvalues i := by
  rw [hM.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  rfl

/-- An adjoint-normalized Kraus family whose squared Frobenius defect is at
most `ε ≤ 1/(card n + 1)` has capacity at least
`(1 - sqrt (card n * ε)) ^ card n`. The infimum need not be attained.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.4.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_adjoint_normalized
    (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun a => (A a)ᴴ) 1 = 1)
    {ε : ℝ} (hε : frobSq (krausMap A 1 - 1) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1)) :
    (1 - Real.sqrt ((Fintype.card n : ℝ) * ε)) ^ Fintype.card n ≤
      operatorCapacity (krausMap A) := by
  apply le_csInf (operatorCapacity_attainable_nonempty (krausMap A))
  rintro d ⟨X, hX, hXdet, rfl⟩
  obtain ⟨W, hW, hcol, hrow, heig⟩ := exists_krausTransition_eigenvalues A hA hX.posSemidef
  have hprod : ∏ i, hX.isHermitian.eigenvalues i = 1 := by
    rw [← re_det_eq_prod_eigenvalues hX.isHermitian, hXdet]
    rfl
  have hbound := Matrix.mul_prod_le_prod_mulVec_of_col_sum_one
    W hW hcol (hrow.trans hε) hεsmall hX.isHermitian.eigenvalues
      (fun i => hX.eigenvalues_pos i)
  rw [hprod, mul_one, heig] at hbound
  simpa only [re_det_eq_prod_eigenvalues
    (krausMap_posSemidef A X hX.posSemidef).isHermitian] using hbound

/-- A unital Kraus family satisfies the same quantitative lower capacity
bound, with the adjoint Frobenius defect. The proof uses exact equality of
the capacities of a Kraus family and its adjoint.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.4.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap A 1 = 1)
    {ε : ℝ} (hε : frobSq (krausMap (fun a => (A a)ᴴ) 1 - 1) ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1)) :
    (1 - Real.sqrt ((Fintype.card n : ℝ) * ε)) ^ Fintype.card n ≤
      operatorCapacity (krausMap A) := by
  rw [operatorCapacity_krausMap_conjTranspose A]
  apply pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_adjoint_normalized
    (fun a => (A a)ᴴ) ?_ hε hεsmall
  simpa only [Matrix.conjTranspose_conjTranspose] using hA

end NLAlib
