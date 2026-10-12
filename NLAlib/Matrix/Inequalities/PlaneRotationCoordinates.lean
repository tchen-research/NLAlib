import NLAlib.Matrix.Inequalities.PlaneRotation
/-!
# Coordinate plane rotations and exact diagonal error

The exact two-coordinate diagonal and squared-error formulas used in Schur–Horn
stationarity. Source: variational rederivation, equation (1); supports atlas
`schur-horn`.
-/
noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem planeRotation_single_row (i j k : n) (hij : i ≠ j) (c s : ℝ) :
    planeRotation (Pi.single i 1) (Pi.single j 1) c s k =
      if k = i then c • Pi.single i 1 + s • Pi.single j 1
      else if k = j then (-s) • Pi.single i 1 + c • Pi.single j 1
      else Pi.single k 1 := by
  ext l
  by_cases hki : k = i <;> by_cases hkj : k = j
  · exact (hij (hki.symm.trans hkj)).elim
  · subst k
    simp [planeRotation, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.one_apply, hij, eq_comm]
    split_ifs <;> ring
  · subst k
    simp [planeRotation, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.one_apply, hij, eq_comm]
    split_ifs <;> ring
  · simp [planeRotation, Matrix.vecMulVec_apply, Pi.single_apply, hki, hkj,
      Matrix.one_apply, eq_comm]

/-- A coordinate plane rotation changes the two selected diagonal entries by
opposite increments and fixes every other diagonal entry. Schur–Horn variational
rederivation, equation (1). -/
theorem planeRotation_single_conjugation_diag
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (i j : n) (hij : i ≠ j)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (k : n) :
    let Δ := 2 * c * s * A i j + s ^ 2 * (A j j - A i i)
    (planeRotation (Pi.single i 1) (Pi.single j 1) c s * A *
      (planeRotation (Pi.single i 1) (Pi.single j 1) c s)ᵀ) k k =
      A k k + if k = i then Δ else if k = j then -Δ else 0 := by
  dsimp only
  rw [Matrix.mul_mul_apply, Matrix.transpose_transpose,
    planeRotation_single_row i j k hij c s]
  have hji : A j i = A i j := congrArg (fun M => M i j) hA
  by_cases hki : k = i
  · subst k
    simp only [ite_true, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, single_dotProduct, Matrix.mulVec_single_one,
      one_mul, smul_eq_mul, Matrix.col_apply, hji]
    linear_combination A i i * hcs
  · by_cases hkj : k = j
    · subst k
      simp only [if_neg hki, ite_true, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, single_dotProduct, Matrix.mulVec_single_one,
        one_mul, smul_eq_mul, Matrix.col_apply, hji]
      linear_combination A j j * hcs
    · simp [hki, hkj, single_dotProduct]

/-- The exact squared-diagonal-error change of a coordinate rotation is
`2(rᵢ-rⱼ)Δ+2Δ²`. Schur–Horn variational rederivation, equation (1). -/
theorem sum_sq_diagonal_error_planeRotation_single_eq
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (d : n → ℝ) (i j : n) (hij : i ≠ j)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    let Δ := 2 * c * s * A i j + s ^ 2 * (A j j - A i i)
    (∑ k, ((planeRotation (Pi.single i 1) (Pi.single j 1) c s * A *
      (planeRotation (Pi.single i 1) (Pi.single j 1) c s)ᵀ) k k - d k) ^ 2) -
      (∑ k, (A k k - d k) ^ 2) =
      2 * ((A i i - d i) - (A j j - d j)) * Δ + 2 * Δ ^ 2 := by
  dsimp only
  let Δ := 2 * c * s * A i j + s ^ 2 * (A j j - A i i)
  rw [← Finset.sum_sub_distrib]
  simp_rw [planeRotation_single_conjugation_diag A hA i j hij c s hcs]
  have hpoint (k : n) :
      (A k k + (if k = i then Δ else if k = j then -Δ else 0) - d k) ^ 2 -
        (A k k - d k) ^ 2 =
        (if k = i then 2 * (A i i - d i) * Δ + Δ ^ 2 else 0) +
        (if k = j then -2 * (A j j - d j) * Δ + Δ ^ 2 else 0) := by
    by_cases hki : k = i <;> by_cases hkj : k = j
    · exact (hij (hki.symm.trans hkj)).elim
    · subst k; simp [hij]; ring
    · subst k; simp [Ne.symm hij]; ring
    · simp [hki, hkj]
  change (∑ k, ((A k k + (if k = i then Δ else if k = j then -Δ else 0) - d k) ^ 2 -
    (A k k - d k) ^ 2)) = _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end NLAlib
