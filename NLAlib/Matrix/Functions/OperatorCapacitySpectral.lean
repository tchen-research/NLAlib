import NLAlib.Matrix.Functions.OperatorCapacityCertificate
import NLAlib.Matrix.Functions.OperatorCapacityAdjoint
import NLAlib.Matrix.Norms.Frobenius
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral transition matrices for operator capacity

Finite Kraus families induce nonnegative transition matrices between input
and output eigenbases.  These identities provide the spectral reduction in
Garg--Gurvits--Oliveira--Wigderson (2015), Lemma 3.4, for the atlas card
`operator-capacity-near-balanced-certificate`.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [DecidableEq n] in
/-- Simultaneous left and right multiplication of a Kraus family realizes
the corresponding congruence scaling of its Kraus map. -/
theorem krausMap_mul_mul_apply (A : ι → Matrix n n ℂ) (B C X : Matrix n n ℂ) :
    krausMap (fun a => B * A a * C) X =
      B * krausMap A (C * X * Cᴴ) * Bᴴ := by
  simp only [krausMap_apply, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Matrix.mul_assoc]

/-- The nonnegative transition matrix associated with the entries of a finite
Kraus family. In eigenvector coordinates it sends input eigenvalues to output
eigenvalues. -/
def krausTransition (A : ι → Matrix n n ℂ) : Matrix n n ℝ :=
  fun i j => ∑ a, Complex.normSq (A a i j)

omit [Fintype n] [DecidableEq n] in
/-- Every entry of a Kraus transition matrix is nonnegative. -/
theorem krausTransition_nonneg (A : ι → Matrix n n ℂ) (i j : n) :
    0 ≤ krausTransition A i j :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- On a real diagonal input, the real diagonal of a Kraus image is the
transition matrix applied to that input diagonal. -/
theorem re_diag_krausMap_diagonal (A : ι → Matrix n n ℂ) (x : n → ℝ) (i : n) :
    (krausMap A (Matrix.diagonal fun j => (x j : ℂ)) i i).re =
      (krausTransition A *ᵥ x) i := by
  simp only [krausMap_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Matrix.conjTranspose_apply, Complex.re_sum,
    krausTransition, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_right_comm, Complex.star_def, Complex.mul_conj]
  simp

/-- Row sums of the Kraus transition matrix are the real diagonal of the
image of the identity. -/
theorem sum_row_krausTransition (A : ι → Matrix n n ℂ) (i : n) :
    (∑ j, krausTransition A i j) = (krausMap A 1 i i).re := by
  simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.mulVec, dotProduct, mul_one]
    using (re_diag_krausMap_diagonal A (fun _ => 1) i).symm

/-- Column sums of the Kraus transition matrix are the real diagonal of the
adjoint image of the identity. -/
theorem sum_col_krausTransition (A : ι → Matrix n n ℂ) (j : n) :
    (∑ i, krausTransition A i j) =
      (krausMap (fun a => (A a)ᴴ) 1 j j).re := by
  rw [← sum_row_krausTransition]
  simp only [krausTransition, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.normSq_conj]

omit [DecidableEq n] in
private theorem sum_sq_re_diag_le_frobSq (M : Matrix n n ℂ) :
    (∑ i, (M i i).re ^ 2) ≤ frobSq M := by
  rw [frobSq_eq_sum_norm_sq]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (M i i).re ^ 2 ≤ ‖M i i‖ ^ 2 := by
      simpa only [← pow_two, Complex.normSq_eq_norm_sq] using Complex.re_sq_le_normSq (M i i)
    _ ≤ ∑ j, ‖M i j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖M i j‖) (Finset.mem_univ i)

/-- Discarding off-diagonal entries bounds the squared row-sum error of a
Kraus transition matrix by the Frobenius defect of the map at the identity. -/
theorem sum_sq_sum_row_krausTransition_sub_one_le (A : ι → Matrix n n ℂ) :
    (∑ i, (∑ j, krausTransition A i j - 1) ^ 2) ≤ frobSq (krausMap A 1 - 1) := by
  convert sum_sq_re_diag_le_frobSq (krausMap A 1 - 1) using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_row_krausTransition]
  simp

set_option maxHeartbeats 1000000 in
/-- In input and output eigenvector coordinates, a Kraus family induces a
nonnegative matrix taking input eigenvalues to output eigenvalues. Both
marginal errors are bounded by the corresponding Frobenius normalization
defects. Exact normalization gives the corresponding exact marginal sums.
This is the spectral reduction in Garg--Gurvits--Oliveira--Wigderson (2015),
Lemma 3.4. -/
theorem exists_krausTransition_eigenvalues_with_marginals
    (A : ι → Matrix n n ℂ)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ∃ W : Matrix n n ℝ,
      (∀ i j, 0 ≤ W i j) ∧
      (krausMap (fun a => (A a)ᴴ) 1 = 1 → ∀ j, ∑ i, W i j = 1) ∧
      (krausMap A 1 = 1 → ∀ i, ∑ j, W i j = 1) ∧
      (∑ i, (∑ j, W i j - 1) ^ 2) ≤ frobSq (krausMap A 1 - 1) ∧
      (∑ j, (∑ i, W i j - 1) ^ 2) ≤
        frobSq (krausMap (fun a => (A a)ᴴ) 1 - 1) ∧
      W *ᵥ hX.isHermitian.eigenvalues =
        (krausMap_posSemidef A X hX).isHermitian.eigenvalues := by
  let hY := krausMap_posSemidef A X hX
  let u := hX.isHermitian.eigenvectorUnitary
  let v := hY.isHermitian.eigenvectorUnitary
  let U : Matrix n n ℂ := u
  let V : Matrix n n ℂ := v
  let B : ι → Matrix n n ℂ := fun a => Vᴴ * A a * U
  have hUU : U * Uᴴ = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self u
  have hU'U : Uᴴ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self u
  have hVV : V * Vᴴ = 1 := by
    simpa only [V, Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self v
  have hV'V : Vᴴ * V = 1 := by
    simpa only [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self v
  have hB_one : krausMap B 1 = Vᴴ * krausMap A 1 * V := by
    dsimp [B]
    rw [krausMap_mul_mul_apply]
    simp only [Matrix.mul_one, hUU, Matrix.conjTranspose_conjTranspose]
  have hB_adj : krausMap (fun a => (B a)ᴴ) 1 =
      Uᴴ * krausMap (fun a => (A a)ᴴ) 1 * U := by
    have hfamily : (fun a => (B a)ᴴ) = (fun a => Uᴴ * (A a)ᴴ * V) := by
      funext a
      simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [hfamily, krausMap_mul_mul_apply, Matrix.mul_one, hVV,
      Matrix.conjTranspose_conjTranspose]
  have hXspec : X = U * Matrix.diagonal (fun j => (hX.isHermitian.eigenvalues j : ℂ)) * Uᴴ := by
    convert hX.isHermitian.spectral_theorem using 1
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, U, u]
  have hYspec : Vᴴ * krausMap A X * V =
      Matrix.diagonal (fun i => (hY.isHermitian.eigenvalues i : ℂ)) := by
    convert hY.isHermitian.conjStarAlgAut_star_eigenvectorUnitary using 1 <;>
    simp [Matrix.star_eq_conjTranspose,
      Function.comp_def, V, v]
  have hBeig : krausMap B (Matrix.diagonal fun j => (hX.isHermitian.eigenvalues j : ℂ)) =
      Matrix.diagonal (fun i => (hY.isHermitian.eigenvalues i : ℂ)) := by
    rw [show krausMap B (Matrix.diagonal fun j => (hX.isHermitian.eigenvalues j : ℂ)) =
      Vᴴ * krausMap A
        (U * Matrix.diagonal (fun j => (hX.isHermitian.eigenvalues j : ℂ)) * Uᴴ) * V by
          simpa only [B, Matrix.conjTranspose_conjTranspose] using
            krausMap_mul_mul_apply A Vᴴ U
              (Matrix.diagonal fun j => (hX.isHermitian.eigenvalues j : ℂ))]
    rw [← hXspec, hYspec]
  refine ⟨krausTransition B, krausTransition_nonneg B, ?_, ?_, ?_, ?_, ?_⟩
  · intro hA j
    rw [sum_col_krausTransition, hB_adj, hA, Matrix.mul_one, hU'U]
    simp
  · intro hA i
    rw [sum_row_krausTransition, hB_one, hA, Matrix.mul_one, hV'V]
    simp
  · have hdef : krausMap B 1 - 1 = Vᴴ * (krausMap A 1 - 1) * V := by
      rw [hB_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV'V]
    have hV' : (Vᴴ)ᴴ * Vᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hVV
    calc
      _ ≤ frobSq (krausMap B 1 - 1) := sum_sq_sum_row_krausTransition_sub_one_le B
      _ = frobSq (krausMap A 1 - 1) := by
        rw [hdef, Matrix.mul_assoc, frobSq_mul_left_of_orthonormal hV']
        simpa only [Matrix.conjTranspose_conjTranspose] using
          frobSq_mul_right_of_orthonormal hV' (krausMap A 1 - 1)
  · have hdef : krausMap (fun a => (B a)ᴴ) 1 - 1 =
        Uᴴ * (krausMap (fun a => (A a)ᴴ) 1 - 1) * U := by
      rw [hB_adj]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU'U]
    have hU' : (Uᴴ)ᴴ * Uᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hUU
    have hrow := sum_sq_sum_row_krausTransition_sub_one_le (fun a => (B a)ᴴ)
    have hcols : (∑ j, (∑ i, krausTransition B i j - 1) ^ 2) ≤
        frobSq (krausMap (fun a => (B a)ᴴ) 1 - 1) := by
      simpa only [krausTransition, Matrix.conjTranspose_apply, Complex.star_def,
        Complex.normSq_conj] using hrow
    calc
      _ ≤ frobSq (krausMap (fun a => (B a)ᴴ) 1 - 1) := hcols
      _ = frobSq (krausMap (fun a => (A a)ᴴ) 1 - 1) := by
        rw [hdef, Matrix.mul_assoc, frobSq_mul_left_of_orthonormal hU']
        simpa only [Matrix.conjTranspose_conjTranspose] using
          frobSq_mul_right_of_orthonormal hU' (krausMap (fun a => (A a)ᴴ) 1 - 1)
  · funext i
    rw [← re_diag_krausMap_diagonal, hBeig]
    simp

/-- A trace-preserving Kraus family has a nonnegative column-stochastic
spectral transition, with squared row error bounded by its Frobenius defect. -/
theorem exists_krausTransition_eigenvalues
    (A : ι → Matrix n n ℂ) (hA : krausMap (fun a => (A a)ᴴ) 1 = 1)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ∃ W : Matrix n n ℝ, (∀ i j, 0 ≤ W i j) ∧
      (∀ j, ∑ i, W i j = 1) ∧
      (∑ i, (∑ j, W i j - 1) ^ 2) ≤ frobSq (krausMap A 1 - 1) ∧
      W *ᵥ hX.isHermitian.eigenvalues =
        (krausMap_posSemidef A X hX).isHermitian.eigenvalues := by
  obtain ⟨W, hW, hc, _, hr, _, heig⟩ :=
    exists_krausTransition_eigenvalues_with_marginals A hX
  exact ⟨W, hW, hc hA, hr, heig⟩

/-- A unital Kraus family has a nonnegative row-stochastic spectral
transition, with squared column error bounded by its adjoint Frobenius defect. -/
theorem exists_krausTransition_eigenvalues_of_unital
    (A : ι → Matrix n n ℂ) (hA : krausMap A 1 = 1)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ∃ W : Matrix n n ℝ, (∀ i j, 0 ≤ W i j) ∧
      (∀ i, ∑ j, W i j = 1) ∧
      (∑ j, (∑ i, W i j - 1) ^ 2) ≤
        frobSq (krausMap (fun a => (A a)ᴴ) 1 - 1) ∧
      W *ᵥ hX.isHermitian.eigenvalues =
        (krausMap_posSemidef A X hX).isHermitian.eigenvalues := by
  obtain ⟨W, hW, _, hr, _, hc, heig⟩ :=
    exists_krausTransition_eigenvalues_with_marginals A hX
  exact ⟨W, hW, hr hA, hc, heig⟩

end NLAlib
