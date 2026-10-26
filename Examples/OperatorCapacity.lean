import NLAlib.Matrix.Functions.OperatorCapacityNearBalanced
import NLAlib.Matrix.Functions.OperatorCapacityRankCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Downstream use of the near-balanced capacity certificate

The two Kraus matrices below define a trace-preserving, nonunital map on
complex two-by-two matrices. Its nonzero normalization defect is exactly
`162 / 625`. The certificate applies to every positive semidefinite input,
and supplies the explicit capacity lower bound `49 / 625`.
-/

noncomputable section

open NLAlib Matrix
open scoped BigOperators ComplexOrder MatrixOrder

private def damping : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, (4 : ℂ) / 5], !![0, (3 : ℂ) / 5; 0, 0]]

private theorem damping_adjoint_normalized :
    krausMap (fun a => (damping a)ᴴ) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [krausMap_apply, damping, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply,
      Complex.star_def, map_ofNat]

private theorem damping_apply_one :
    krausMap damping 1 = !![(34 : ℂ) / 25, 0; 0, (16 : ℂ) / 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [krausMap_apply, damping, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply,
      Complex.star_def, map_ofNat]

private theorem damping_defect : frobSq (krausMap damping 1 - 1) = 162 / 625 := by
  rw [damping_apply_one]
  rw [frobSq_eq_sum_norm_sq]
  simp_rw [← Complex.normSq_eq_norm_sq]
  norm_num [Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply, Complex.normSq]

example {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosSemidef) :
    X.rank ≤ (krausMap damping X).rank := by
  exact rank_le_rank_krausMap_of_adjoint_normalized (ε := 162 / 625) damping damping_adjoint_normalized
    (by rw [damping_defect]) (by norm_num) hX

example : (49 : ℝ) / 625 ≤ operatorCapacity (krausMap damping) ∧
    operatorCapacity (krausMap damping) ≤ 1 := by
  constructor
  · have h := pow_one_sub_sqrt_le_operatorCapacity_krausMap_of_adjoint_normalized
      (ε := 162 / 625) damping damping_adjoint_normalized (by rw [damping_defect]) (by norm_num)
    have hsqrt : Real.sqrt ((324 : ℝ) / 625) = 18 / 25 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
      norm_num
    norm_num only [Fintype.card_fin] at h
    rw [hsqrt] at h
    norm_num at h ⊢
    exact h
  · exact operatorCapacity_krausMap_le_one_of_adjoint_normalized (by decide)
      damping damping_adjoint_normalized
