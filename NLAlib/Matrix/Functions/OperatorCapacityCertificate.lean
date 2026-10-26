import NLAlib.Matrix.Functions.OperatorCapacity
import NLAlib.Matrix.Functions.DeterminantBalance
import NLAlib.Matrix.Functions.DeterminantTraceVariational

/-!
# Capacity trial points and a normalized balance certificate

The identity is an admissible trial point in the operator-capacity infimum.
Consequently, capacity at least `exp (-eps)` and trace normalization of the
image of the identity imply a Frobenius balance certificate.

For a finite Kraus family with adjoint normalization, trace preservation is
proved by cyclicity of trace. This gives the trace-preserving converse in the
atlas card `operator-capacity-near-balanced-certificate`. The unital branch,
the lower capacity bound, and the rank certificate are separate results.
No minimizer of the capacity objective is assumed.
-/

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every normalized positive definite test matrix bounds operator capacity
from above, for a positive real-linear map. -/
theorem operatorCapacity_le_det_apply
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    {X : Matrix n n ℂ} (hX : X.PosDef) (hdet : X.det = 1) :
    operatorCapacity T ≤ (T X).det.re := by
  exact csInf_le (operatorCapacity_attainable_bddBelow T hT) ⟨X, hX, hdet, rfl⟩

/-- The identity matrix supplies an upper bound on operator capacity. -/
theorem operatorCapacity_le_det_apply_one
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    operatorCapacity T ≤ (T 1).det.re :=
  operatorCapacity_le_det_apply T hT Matrix.PosDef.one Matrix.det_one

/-- A positive map whose image of the identity has normalized trace and whose
capacity is at least `exp (-eps)` has squared Frobenius imbalance at most
`6 * eps`, provided `eps ≤ 1 / 6`. -/
theorem frobSq_apply_one_sub_one_le_of_exp_neg_le_operatorCapacity
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (htr : (T 1).trace.re = (Fintype.card n : ℝ))
    {eps : ℝ} (heps : eps ≤ 1 / 6)
    (hcap : Real.exp (-eps) ≤ operatorCapacity T) :
    frobSq (T 1 - 1) ≤ 6 * eps := by
  have hdet : Real.exp (-eps) ≤ (T 1).det.re :=
    hcap.trans (operatorCapacity_le_det_apply_one T hT)
  have hdetpos : 0 < (T 1).det.re := (Real.exp_pos _).trans_le hdet
  have hne : (T 1).det ≠ 0 := by
    intro h
    simp [h] at hdetpos
  have hpos : (T 1).PosDef :=
    (hT 1 Matrix.PosSemidef.one).posDef_iff_det_ne_zero.mpr hne
  exact hpos.frobSq_sub_one_le_six_mul_of_exp_neg_le_det eps htr heps hdet

/-- Adjoint normalization of a finite Kraus family implies trace preservation
of its actual Kraus map. -/
theorem trace_krausMap_eq_of_adjoint_normalized
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun i => (A i)ᴴ) 1 = 1) (X : Matrix n n ℂ) :
    (krausMap A X).trace = X.trace := by
  have hsum : ∑ i, (A i)ᴴ * A i = 1 := by
    simpa only [krausMap_apply, Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
      using hA
  calc
    (krausMap A X).trace = ∑ i, (A i * X * (A i)ᴴ).trace := by
      rw [krausMap_apply, Matrix.trace_sum]
    _ = ∑ i, ((A i)ᴴ * A i * X).trace :=
      Finset.sum_congr rfl fun i _ => Matrix.trace_mul_cycle _ _ _
    _ = ((∑ i, (A i)ᴴ * A i) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [hsum, Matrix.one_mul]

/-- The capacity-to-balance converse for an adjoint-normalized Kraus family.
Both terms of the double-stochasticity defect are explicit; the adjoint term
vanishes by normalization. This is the trace-preserving branch of
Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.6.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem frobSq_krausMap_defect_le_of_exp_neg_le_operatorCapacity
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun i => (A i)ᴴ) 1 = 1)
    {eps : ℝ} (heps : eps ≤ 1 / 6)
    (hcap : Real.exp (-eps) ≤ operatorCapacity (krausMap A)) :
    frobSq (krausMap A 1 - 1) +
      frobSq (krausMap (fun i => (A i)ᴴ) 1 - 1) ≤ 6 * eps := by
  rw [hA, sub_self, frobSq_zero, add_zero]
  apply frobSq_apply_one_sub_one_le_of_exp_neg_le_operatorCapacity
    (krausMap A) (krausMap_posSemidef A) _ heps hcap
  rw [trace_krausMap_eq_of_adjoint_normalized A hA 1]
  simp

/-- A positive map whose image of the identity has trace equal to the matrix
dimension has capacity at most one. The proof uses the identity trial point
and the PSD arithmetic-geometric mean inequality.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Proposition 2.8. -/
theorem operatorCapacity_le_one_of_trace_apply_one
    (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (htr : (T 1).trace.re = (Fintype.card n : ℝ)) :
    operatorCapacity T ≤ 1 := by
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    operatorCapacity T ≤ (T 1).det.re := operatorCapacity_le_det_apply_one T hT
    _ ≤ ((T 1).trace.re / (Fintype.card n : ℝ)) ^ Fintype.card n :=
      (hT 1 Matrix.PosSemidef.one).re_det_le_pow_re_trace_div_card hN
    _ = 1 := by rw [htr, div_self hcard, one_pow]

/-- A unital Kraus family has capacity at most one, since the identity is
an admissible test matrix. Source: Garg--Gurvits--Oliveira--Wigderson (2015),
Proposition 2.8.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem operatorCapacity_krausMap_le_one_of_unital
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap A 1 = 1) :
    operatorCapacity (krausMap A) ≤ 1 := by
  simpa only [hA, Matrix.det_one, Complex.one_re] using
    operatorCapacity_le_det_apply_one (krausMap A) (krausMap_posSemidef A)

/-- An adjoint-normalized Kraus family has capacity at most one.
Source: Garg--Gurvits--Oliveira--Wigderson (2015), Proposition 2.8.
atlas: operator-capacity-near-balanced-certificate (partial) -/
theorem operatorCapacity_krausMap_le_one_of_adjoint_normalized
    (hN : 0 < Fintype.card n)
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : krausMap (fun a => (A a)ᴴ) 1 = 1) :
    operatorCapacity (krausMap A) ≤ 1 := by
  apply operatorCapacity_le_one_of_trace_apply_one hN
    (krausMap A) (krausMap_posSemidef A)
  rw [trace_krausMap_eq_of_adjoint_normalized A hA 1]
  simp

end NLAlib
