import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NLAlib.ForMathlib.Analysis.SpecialFunctions.ReciprocalBarrier
import NLAlib.Matrix.Functions.PolynomialCalculus

/-!
# Matrix reciprocal barrier averaging inequalities

The scalar reciprocal-barrier averaging inequalities of
`NLAlib.ForMathlib.Analysis.SpecialFunctions.ReciprocalBarrier` are transferred
to actual symmetric positive definite matrices `M : Matrix n n ℝ` with a finite
nonempty index type `n`.  The transfer route is the real spectral theorem:
`M` is unitarily diagonalized with positive eigenvalues `λ i`, the traces of
`M⁻¹`, `(M ± δ•1)⁻¹` and their squares are computed from the original
diagonalization by cyclic trace, and the displayed upper/lower inequalities
reduce exactly to the scalar `Real.reciprocal_barrier_upper_le` /
`Real.reciprocal_barrier_lower_le`.

The public matrix statements live in `Matrix.PosDef`. The trace identities and
shifted positivity also cover the empty index type; the positive gap and
barrier inequalities below require a nonempty index type.

For `δ > 0`, the upper step uses `RU = (M + δ•1)⁻¹` and
`DU = tr(M⁻¹) - tr(RU) > 0`; the lower step additionally needs the strict
potential bound `δ * tr(M⁻¹) < 1`, from which `δ < λ i` for every eigenvalue
is derived (without assuming shifted positivity), so `M - δ•1` is actually
positive definite, `RL = (M - δ•1)⁻¹` exists, and
`DL = tr(RL) - tr(M⁻¹) > 0`.

Source: Batson--Spielman--Srivastava, *Twice-Ramanujan Sparsifiers* (2008),
Section 3.2 ([arXiv:0808.0163](https://arxiv.org/abs/0808.0163)).  This file
is the matrix transfer of the scalar averaging part: candidate selection and
the full finite BSS induction are out of scope.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

/-- A positive definite matrix shifted up by a positive multiple of the identity
remains positive definite. -/
theorem _root_.Matrix.PosDef.add_smul_one_posDef {n : Type*} [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    (A + δ • (1 : Matrix n n ℝ)).PosDef := by
  exact hA.add (Matrix.PosDef.one.smul (a := δ) hδ)

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma mul_diagonal_mul_mul_diagonal_mul_eq_one {U D D' : Matrix n n ℝ}
    (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) (hDD : D * D' = 1) :
    (U * D * Uᵀ) * (U * D' * Uᵀ) = 1 := by
  calc
    (U * D * Uᵀ) * (U * D' * Uᵀ)
        = U * (D * (Uᵀ * U) * D') * Uᵀ := by
          simp only [Matrix.mul_assoc]
    _ = U * (D * D') * Uᵀ := by
          rw [hU2]
          simp
    _ = U * Uᵀ := by
          rw [hDD]
          simp
    _ = 1 := hU1

private lemma inv_eq_mul_diagonal_mul_transpose {U D D' : Matrix n n ℝ}
    (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) (hDD : D * D' = 1) :
    (U * D * Uᵀ)⁻¹ = U * D' * Uᵀ := by
  apply Matrix.inv_eq_right_inv
  exact mul_diagonal_mul_mul_diagonal_mul_eq_one hU1 hU2 hDD

private lemma mul_diagonal_mul_transpose_pow_two {U D : Matrix n n ℝ}
    (hU2 : Uᵀ * U = 1) :
    (U * D * Uᵀ) ^ 2 = U * D ^ 2 * Uᵀ := by
  rw [pow_two]
  calc
    (U * D * Uᵀ) * (U * D * Uᵀ)
        = U * (D * (Uᵀ * U) * D) * Uᵀ := by
          simp only [Matrix.mul_assoc]
    _ = U * (D * D) * Uᵀ := by
          rw [hU2]
          simp
    _ = U * D ^ 2 * Uᵀ := by
          rw [pow_two]

private lemma add_smul_one_eq_mul_diagonal_mul_transpose {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    A + c • (1 : Matrix n n ℝ) =
      (↑hA.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => hA.eigenvalues i + c) *
        (↑hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  have hd : Matrix.diagonal (fun i => hA.eigenvalues i + c) =
      Matrix.diagonal hA.eigenvalues + c • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
  rw [hd]
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    eigenvectorUnitary_mul_transpose_self hA]

private lemma sub_smul_one_eq_mul_diagonal_mul_transpose {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    A - c • (1 : Matrix n n ℝ) =
      (↑hA.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => hA.eigenvalues i - c) *
        (↑hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  have hd : Matrix.diagonal (fun i => hA.eigenvalues i - c) =
      Matrix.diagonal hA.eigenvalues - c • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
  rw [hd]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    eigenvectorUnitary_mul_transpose_self hA]

private lemma diagonal_mul_diagonal_inv_eq_one_of_pos {A : Matrix n n ℝ}
    (hA : A.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i + δ) *
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i + δ)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [mul_inv_cancel₀ (ne_of_gt (add_pos (hA.eigenvalues_pos i) hδ))]
  · simp [hij]

private lemma diagonal_sub_smul_one_diagonal_inv_eq_one {A : Matrix n n ℝ}
    (hA : A.PosDef) {δ : ℝ} (hδlt : ∀ i, δ < hA.isHermitian.eigenvalues i) :
    Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i - δ) *
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i - δ)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (hδlt i)))]
  · simp [hij]

/-- The trace of the inverse of a real positive definite matrix is the sum of
the reciprocals of its eigenvalues. -/
theorem _root_.Matrix.PosDef.trace_inv_eq_sum_inv_eigenvalues
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    A⁻¹.trace = ∑ i, 1 / hA.isHermitian.eigenvalues i := by
  have hU1 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
    eigenvectorUnitary_mul_transpose_self hA.isHermitian
  have hU2 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    transpose_eigenvectorUnitary_mul_self hA.isHermitian
  have hD : Matrix.diagonal hA.isHermitian.eigenvalues *
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [mul_inv_cancel₀ (ne_of_gt (hA.eigenvalues_pos i))]
    · simp [hij]
  have hinv : A⁻¹ =
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) *
        (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA.isHermitian]
    exact inv_eq_mul_diagonal_mul_transpose hU1 hU2 hD
  rw [hinv, Matrix.trace_mul_cycle]
  simp [hU2, Matrix.trace_diagonal, one_div]

/-- For positive `δ`, the trace of `(A + δ•1)⁻¹` is the sum of
`1/(λ i + δ)` over the eigenvalues `λ i` of a positive definite `A`. -/
theorem _root_.Matrix.PosDef.trace_add_smul_one_inv_eq_sum_inv_add
    {A : Matrix n n ℝ} (hA : A.PosDef)
    {δ : ℝ} (hδ : 0 < δ) :
    ((A + δ • (1 : Matrix n n ℝ))⁻¹).trace =
      ∑ i, 1 / (hA.isHermitian.eigenvalues i + δ) := by
  have hU1 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
    eigenvectorUnitary_mul_transpose_self hA.isHermitian
  have hU2 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    transpose_eigenvectorUnitary_mul_self hA.isHermitian
  have hD := diagonal_mul_diagonal_inv_eq_one_of_pos hA hδ
  have hinv : (A + δ • 1)⁻¹ =
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i + δ)⁻¹) *
        (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [add_smul_one_eq_mul_diagonal_mul_transpose hA.isHermitian δ]
    exact inv_eq_mul_diagonal_mul_transpose hU1 hU2 hD
  rw [hinv, Matrix.trace_mul_cycle]
  simp [hU2, Matrix.trace_diagonal, one_div]

/-- For positive `δ`, the trace of `((A + δ•1)⁻¹)²` is the sum of
`(1/(λ i + δ))²` over the eigenvalues `λ i` of a positive definite `A`. -/
theorem _root_.Matrix.PosDef.trace_add_smul_one_inv_sq_eq_sum_inv_sq_add
    {A : Matrix n n ℝ}
    (hA : A.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    (((A + δ • (1 : Matrix n n ℝ))⁻¹) ^ 2).trace =
      ∑ i, (1 / (hA.isHermitian.eigenvalues i + δ)) ^ 2 := by
  have hU1 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
    eigenvectorUnitary_mul_transpose_self hA.isHermitian
  have hU2 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    transpose_eigenvectorUnitary_mul_self hA.isHermitian
  have hD := diagonal_mul_diagonal_inv_eq_one_of_pos hA hδ
  have hinv : (A + δ • 1)⁻¹ =
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i + δ)⁻¹) *
        (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [add_smul_one_eq_mul_diagonal_mul_transpose hA.isHermitian δ]
    exact inv_eq_mul_diagonal_mul_transpose hU1 hU2 hD
  rw [hinv, mul_diagonal_mul_transpose_pow_two hU2, Matrix.trace_mul_cycle]
  simp [hU2, Matrix.diagonal_pow, Matrix.trace_diagonal, one_div]

/-- If every eigenvalue of a positive definite `A` exceeds `δ`, then the trace
of `(A - δ•1)⁻¹` is the sum of `1/(λ i - δ)` over the eigenvalues `λ i`.
-/
theorem _root_.Matrix.PosDef.trace_sub_smul_one_inv_eq_sum_inv_sub
    {A : Matrix n n ℝ} (hA : A.PosDef)
    {δ : ℝ} (hδlt : ∀ i, δ < hA.isHermitian.eigenvalues i) :
    ((A - δ • (1 : Matrix n n ℝ))⁻¹).trace =
      ∑ i, 1 / (hA.isHermitian.eigenvalues i - δ) := by
  have hU1 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
    eigenvectorUnitary_mul_transpose_self hA.isHermitian
  have hU2 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    transpose_eigenvectorUnitary_mul_self hA.isHermitian
  have hD := diagonal_sub_smul_one_diagonal_inv_eq_one hA hδlt
  have hinv : (A - δ • 1)⁻¹ =
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i - δ)⁻¹) *
        (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [sub_smul_one_eq_mul_diagonal_mul_transpose hA.isHermitian δ]
    exact inv_eq_mul_diagonal_mul_transpose hU1 hU2 hD
  rw [hinv, Matrix.trace_mul_cycle]
  simp [hU2, Matrix.trace_diagonal, one_div]

/-- If every eigenvalue of a positive definite `A` exceeds `δ`, then the trace
of `((A - δ•1)⁻¹)²` is the sum of `(1/(λ i - δ))²` over the eigenvalues
`λ i` of `A`. -/
theorem _root_.Matrix.PosDef.trace_sub_smul_one_inv_sq_eq_sum_inv_sq_sub
    {A : Matrix n n ℝ}
    (hA : A.PosDef) {δ : ℝ} (hδlt : ∀ i, δ < hA.isHermitian.eigenvalues i) :
    (((A - δ • (1 : Matrix n n ℝ))⁻¹) ^ 2).trace =
      ∑ i, (1 / (hA.isHermitian.eigenvalues i - δ)) ^ 2 := by
  have hU1 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
    eigenvectorUnitary_mul_transpose_self hA.isHermitian
  have hU2 : (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ *
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    transpose_eigenvectorUnitary_mul_self hA.isHermitian
  have hD := diagonal_sub_smul_one_diagonal_inv_eq_one hA hδlt
  have hinv : (A - δ • 1)⁻¹ =
      (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i - δ)⁻¹) *
        (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [sub_smul_one_eq_mul_diagonal_mul_transpose hA.isHermitian δ]
    exact inv_eq_mul_diagonal_mul_transpose hU1 hU2 hD
  rw [hinv, mul_diagonal_mul_transpose_pow_two hU2, Matrix.trace_mul_cycle]
  simp [hU2, Matrix.diagonal_pow, Matrix.trace_diagonal, one_div]

/-- A positive definite matrix shifted down by `δ•1` is positive definite as
soon as every eigenvalue exceeds `δ` (the actual shifted positivity derived from
the spectral representation). -/
theorem _root_.Matrix.PosDef.sub_smul_one_posDef_of_eigenvalues_gt {A : Matrix n n ℝ}
    (hA : A.PosDef) {δ : ℝ} (hδlt : ∀ i, δ < hA.isHermitian.eigenvalues i) :
    (A - δ • (1 : Matrix n n ℝ)).PosDef := by
  have hU : IsUnit (↑hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) :=
    Unitary.isUnit_coe (U := hA.isHermitian.eigenvectorUnitary)
  rw [sub_smul_one_eq_mul_diagonal_mul_transpose hA.isHermitian δ]
  have hpos : (Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i - δ)).PosDef := by
    exact Matrix.posDef_diagonal_iff.mpr (fun i => sub_pos.mpr (hδlt i))
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff hU
      (x := Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i - δ))).mpr hpos

/-- A strict reciprocal-potential cap puts the shift below every eigenvalue.
This includes empty matrix shapes, where the conclusion is vacuous. -/
theorem _root_.Matrix.PosDef.lt_eigenvalues_of_mul_trace_inv_lt_one
    {M : Matrix n n ℝ} (hM : M.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hcap : δ * M⁻¹.trace < 1) :
    ∀ i, δ < hM.isHermitian.eigenvalues i := by
  intro i
  have hsingle : 1 / hM.isHermitian.eigenvalues i ≤
      ∑ j, 1 / hM.isHermitian.eigenvalues j := by
    exact Finset.single_le_sum
      (fun j _ => (one_div_pos.mpr (hM.eigenvalues_pos j)).le)
      (Finset.mem_univ i)
  have hδinv : δ * (1 / hM.isHermitian.eigenvalues i) < 1 := by
    have hcap' := hcap
    rw [hM.trace_inv_eq_sum_inv_eigenvalues] at hcap'
    nlinarith [hcap', hsingle, hδ]
  have h := mul_lt_mul_of_pos_left hδinv (hM.eigenvalues_pos i)
  simpa [mul_assoc, mul_comm, mul_left_comm,
    inv_mul_cancel₀ (ne_of_gt (hM.eigenvalues_pos i))] using h

/-- The strict reciprocal-potential cap guarantees positivity after shifting
down, so the shifted matrix and its inverse are positive definite. -/
theorem _root_.Matrix.PosDef.sub_smul_one_posDef_of_mul_trace_inv_lt_one
    {M : Matrix n n ℝ} (hM : M.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hcap : δ * M⁻¹.trace < 1) :
    (M - δ • (1 : Matrix n n ℝ)).PosDef :=
  hM.sub_smul_one_posDef_of_eigenvalues_gt
    (hM.lt_eigenvalues_of_mul_trace_inv_lt_one hδ hcap)

/-- The upper reciprocal-barrier gap `tr(M⁻¹) - tr((M + δ•1)⁻¹)` of a
positive definite matrix is strictly positive. -/
theorem _root_.Matrix.PosDef.trace_inv_sub_trace_add_smul_one_inv_pos
    [Nonempty n] {M : Matrix n n ℝ} (hM : M.PosDef)
    {δ : ℝ} (hδ : 0 < δ) :
    0 < M⁻¹.trace - ((M + δ • (1 : Matrix n n ℝ))⁻¹).trace := by
  rw [hM.trace_inv_eq_sum_inv_eigenvalues,
    hM.trace_add_smul_one_inv_eq_sum_inv_add hδ]
  simpa [Real.reciprocalBarrierGap] using
    (Real.reciprocalBarrierGap_pos hδ (hM.eigenvalues_pos))

/-- The lower reciprocal-barrier gap
`tr((M - δ•1)⁻¹) - tr(M⁻¹)` of a positive definite matrix is strictly
positive under the strict potential bound `δ * tr(M⁻¹) < 1`. -/
theorem _root_.Matrix.PosDef.trace_sub_smul_one_inv_sub_trace_inv_pos
    [Nonempty n] {M : Matrix n n ℝ} (hM : M.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hcap : δ * M⁻¹.trace < 1) :
    0 < ((M - δ • (1 : Matrix n n ℝ))⁻¹).trace - M⁻¹.trace := by
  have hδlt := hM.lt_eigenvalues_of_mul_trace_inv_lt_one hδ hcap
  rw [hM.trace_inv_eq_sum_inv_eigenvalues,
    hM.trace_sub_smul_one_inv_eq_sum_inv_sub hδlt]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  have hlt : hM.isHermitian.eigenvalues i - δ < hM.isHermitian.eigenvalues i :=
    sub_lt_self (hM.isHermitian.eigenvalues i) hδ
  have hdiv : 1 / hM.isHermitian.eigenvalues i <
      1 / (hM.isHermitian.eigenvalues i - δ) :=
    one_div_lt_one_div_of_lt (sub_pos.mpr (hδlt i)) hlt
  linarith

/-- Matrix upper reciprocal-barrier averaging inequality (BSS upper step) for
a real symmetric positive definite `M`: with `RU = (M + δ•1)⁻¹` and
`DU = tr(M⁻¹) - tr(RU) > 0`,
`tr(RU²)/DU + tr(RU) ≤ 1/δ + tr(M⁻¹)`. -/
theorem _root_.Matrix.PosDef.reciprocal_barrier_upper_le
    [Nonempty n] {M : Matrix n n ℝ} (hM : M.PosDef)
    {δ : ℝ} (hδ : 0 < δ) :
    (((M + δ • (1 : Matrix n n ℝ))⁻¹) ^ 2).trace /
        (M⁻¹.trace - ((M + δ • (1 : Matrix n n ℝ))⁻¹).trace) +
      ((M + δ • (1 : Matrix n n ℝ))⁻¹).trace ≤
    1 / δ + M⁻¹.trace := by
  rw [hM.trace_inv_eq_sum_inv_eigenvalues,
    hM.trace_add_smul_one_inv_eq_sum_inv_add hδ,
    hM.trace_add_smul_one_inv_sq_eq_sum_inv_sq_add hδ]
  exact Real.reciprocal_barrier_upper_le (I := n) hδ (hM.eigenvalues_pos)

/-- Matrix lower reciprocal-barrier averaging inequality (BSS lower step) for
a real symmetric positive definite `M` satisfying the strict potential bound
`δ * tr(M⁻¹) < 1`: with
`RL = (M - δ•1)⁻¹` and `DL = tr(RL) - tr(M⁻¹) > 0`,
`1/δ - tr(M⁻¹) ≤ tr(RL²)/DL - tr(RL)`. -/
theorem _root_.Matrix.PosDef.reciprocal_barrier_lower_le
    [Nonempty n] {M : Matrix n n ℝ} (hM : M.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hcap : δ * M⁻¹.trace < 1) :
    1 / δ - M⁻¹.trace ≤
      (((M - δ • (1 : Matrix n n ℝ))⁻¹) ^ 2).trace /
        (((M - δ • (1 : Matrix n n ℝ))⁻¹).trace - M⁻¹.trace) -
      ((M - δ • (1 : Matrix n n ℝ))⁻¹).trace := by
  have hδlt := hM.lt_eigenvalues_of_mul_trace_inv_lt_one hδ hcap
  have hcap_sum : δ * (∑ i, 1 / hM.isHermitian.eigenvalues i) ≤ 1 := by
    have hcap' := hcap
    rw [hM.trace_inv_eq_sum_inv_eigenvalues] at hcap'
    exact le_of_lt hcap'
  rw [hM.trace_inv_eq_sum_inv_eigenvalues,
    hM.trace_sub_smul_one_inv_eq_sum_inv_sub hδlt,
    hM.trace_sub_smul_one_inv_sq_eq_sum_inv_sq_sub hδlt]
  exact Real.reciprocal_barrier_lower_le (I := n) hδ hδlt hcap_sum

end NLAlib
