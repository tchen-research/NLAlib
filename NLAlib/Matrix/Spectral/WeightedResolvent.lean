import NLAlib.Matrix.Spectral.RestrictedInvertibilityScalar
import NLAlib.Matrix.Spectral.Inertia
import NLAlib.Matrix.Basic.PSDDuality

/-!
# Weighted resolvents for restricted invertibility

The weighted lower-barrier potential is evaluated in the spectral coordinates
of the selected Gram matrix. The weight matrix need not commute with that
matrix. A rank bound supplies the kernel mass required by the scalar estimate.
Source: Spielman--Srivastava (2009), proof of Theorem 2.
-/

noncomputable section

open scoped Matrix BigOperators MatrixOrder
open Matrix

namespace NLAlib.RestrictedInvertibility

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted lower-barrier potential `tr(H (A - b I)⁻¹)`.
The inverse is total; its intended use excludes eigenvalues equal to `b`. -/
def lowerPotential (H A : Matrix n n ℝ) (b : ℝ) : ℝ :=
  (H * (A - b • (1 : Matrix n n ℝ))⁻¹).trace

private theorem inv_shift_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (b : ℝ) (hb : ∀ i, hA.eigenvalues i ≠ b) :
    (A - b • (1 : Matrix n n ℝ))⁻¹ =
      (hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (fun i => (hA.eigenvalues i - b)⁻¹) *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hU1 : U * Uᵀ = 1 := eigenvectorUnitary_mul_transpose_self hA
  have hU2 : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA
  have hD : diagonal (fun i => hA.eigenvalues i - b) *
      diagonal (fun i => (hA.eigenvalues i - b)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [mul_inv_cancel₀ (sub_ne_zero.mpr (hb i))]
    · simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [sub_smul_one_eq_transpose_mul_diagonal_mul hA b, transpose_transpose]
  change (U * diagonal (fun i => hA.eigenvalues i - b) * Uᵀ) *
      (U * diagonal (fun i => (hA.eigenvalues i - b)⁻¹) * Uᵀ) = 1
  calc
    _ = U * (diagonal (fun i => hA.eigenvalues i - b) * (Uᵀ * U) *
        diagonal (fun i => (hA.eigenvalues i - b)⁻¹)) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU2, Matrix.mul_one, hD, Matrix.mul_one, hU1]

private theorem weighted_trace_diagonal (H U : Matrix n n ℝ) (d : n → ℝ) :
    (H * (U * diagonal d * Uᵀ)).trace =
      ∑ i, (Uᵀ * H * U) i i * d i := by
  calc
    _ = (H * U * diagonal d * Uᵀ).trace := by simp only [Matrix.mul_assoc]
    _ = (Uᵀ * (H * U) * diagonal d).trace := by rw [Matrix.trace_mul_cycle]
    _ = _ := by simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.mul_assoc]

private theorem trace_inv_shift_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (H : Matrix n n ℝ) (b : ℝ) (hb : ∀ i, hA.eigenvalues i ≠ b) :
    lowerPotential H A b = ∑ i,
      ((hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * H * hA.eigenvectorUnitary) i i /
        (hA.eigenvalues i - b) := by
  rw [lowerPotential, inv_shift_eq hA b hb, weighted_trace_diagonal]
  simp only [div_eq_mul_inv]

private theorem trace_sq_inv_shift_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (H : Matrix n n ℝ) (b : ℝ) (hb : ∀ i, hA.eigenvalues i ≠ b) :
    (H * ((A - b • (1 : Matrix n n ℝ))⁻¹) ^ 2).trace = ∑ i,
      ((hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * H * hA.eigenvectorUnitary) i i /
        (hA.eigenvalues i - b) ^ 2 := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA
  rw [inv_shift_eq hA b hb]
  have hp : (U * diagonal (fun i => (hA.eigenvalues i - b)⁻¹) * Uᵀ) ^ 2 =
      U * diagonal (fun i => (hA.eigenvalues i - b)⁻¹ ^ 2) * Uᵀ := by
    rw [pow_two]
    calc
      _ = U * (diagonal (fun i => (hA.eigenvalues i - b)⁻¹) * (Uᵀ * U) *
          diagonal (fun i => (hA.eigenvalues i - b)⁻¹)) * Uᵀ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, diagonal_mul_diagonal]; simp only [pow_two]
  change (H * (U * _ * Uᵀ) ^ 2).trace = _
  rw [hp, weighted_trace_diagonal]
  simp only [div_eq_mul_inv, inv_pow, U]

/-- The shifted lower barrier is invertible whenever every eigenvalue is zero
or strictly above a positive barrier. -/
theorem isUnit_shift_of_eigenvalues_gap {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {b : ℝ} (hb : 0 < b) (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i) :
    IsUnit (A - b • (1 : Matrix n n ℝ)) := by
  have hn : ∀ i, hA.eigenvalues i ≠ b := by
    intro i
    rcases hgap i with hi | hi <;> linarith
  have hright : (A - b • (1 : Matrix n n ℝ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℝ) *
        diagonal (fun i => (hA.eigenvalues i - b)⁻¹) *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ) = 1 := by
    rw [← inv_shift_eq hA b hn]
    apply Matrix.mul_nonsing_inv
    rw [sub_smul_one_eq_transpose_mul_diagonal_mul hA b,
      Matrix.det_mul, Matrix.det_mul]
    apply IsUnit.mul
    · apply IsUnit.mul
      · exact (Matrix.isUnit_iff_isUnit_det _).mp
          (by simpa using isUnit_transpose_eigenvectorUnitary hA)
      · rw [Matrix.det_diagonal]
        exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
          fun i _ => sub_ne_zero.mpr (hn i))
    · exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose_eigenvectorUnitary hA)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hright)

/-- A rank bound gives enough kernel mass for the weighted lower-barrier
inequality. No commutation of `A` with `H` is assumed.
Source: Spielman--Srivastava (2009), Theorem 2, weighted resolvent step. -/
theorem lowerPotential_gap_pos_and_trace_sq_le
    {A H : Matrix n n ℝ} (hA : A.IsHermitian) (hH : H.PosSemidef)
    {b δ Λ : ℝ} (hδ : 0 < δ) (hb : δ < b) (hΛ : 0 < Λ)
    (hHle : H ≤ Λ • (1 : Matrix n n ℝ))
    (hgap : ∀ i, hA.eigenvalues i = 0 ∨ b < hA.eigenvalues i)
    (hkernel : b * Λ ≤ δ * (H.trace - (A.rank : ℝ) * Λ)) :
    let Δ := lowerPotential H A b - lowerPotential H A (b - δ)
    0 < Δ ∧
      Λ * (H * ((A - (b - δ) • (1 : Matrix n n ℝ))⁻¹) ^ 2).trace ≤
        Δ * (Λ / δ + Δ) := by
  classical
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let w : n → ℝ := fun i => (Uᵀ * H * U) i i
  have hU : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA
  have hw : ∀ i, 0 ≤ w i := by
    have hp : (Uᵀ * H * U).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hH.conjTranspose_mul_mul_same U
    intro i
    exact hp.diag_nonneg
  have hwle : ∀ i, w i ≤ Λ := by
    have hp := (Matrix.le_iff.mp hHle).conjTranspose_mul_mul_same U
    have hh : Uᵀ * (Λ • (1 : Matrix n n ℝ) - H) * U =
        Λ • (1 : Matrix n n ℝ) - Uᵀ * H * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hU]
    have hp' : (Λ • (1 : Matrix n n ℝ) - Uᵀ * H * U).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hh] using hp
    intro i
    have hi := hp'.diag_nonneg (i := i)
    simpa [w] using hi
  have hsum : ∑ i, w i = H.trace := by
    change (Uᵀ * H * U).trace = H.trace
    rw [Matrix.trace_mul_cycle, eigenvectorUnitary_mul_transpose_self hA, Matrix.one_mul]
  have hq : H.trace - (A.rank : ℝ) * Λ ≤ ∑ i, if hA.eigenvalues i = 0 then w i else 0 := by
    have hs : (∑ i, if hA.eigenvalues i ≠ 0 then w i else 0) ≤ (A.rank : ℝ) * Λ := by
      rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      calc
        _ = ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0), w i := by
          rw [Finset.sum_filter]
        _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0), Λ :=
          Finset.sum_le_sum fun i _ => hwle i
        _ = _ := by simp
    have heq : (∑ i, if hA.eigenvalues i = 0 then w i else 0) +
        (∑ i, if hA.eigenvalues i ≠ 0 then w i else 0) = H.trace := by
      rw [← hsum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : hA.eigenvalues i = 0 <;> simp [hi]
    linarith
  have hn (c : ℝ) (hc : 0 < c) (hcb : c ≤ b) : ∀ i, hA.eigenvalues i ≠ c := by
    intro i
    rcases hgap i with hi | hi <;> linarith
  have hh := weighted_reciprocal_sq_le hA.eigenvalues w hδ hb hΛ hw hgap
    (hkernel.trans (mul_le_mul_of_nonneg_left hq hδ.le))
  have hΔ : lowerPotential H A b - lowerPotential H A (b - δ) =
      ∑ i, w i * (1 / (hA.eigenvalues i - b) - 1 / (hA.eigenvalues i - (b - δ))) := by
    rw [trace_inv_shift_eq_sum hA H b (hn b (lt_trans hδ hb) le_rfl),
      trace_inv_shift_eq_sum hA H (b - δ) (hn (b - δ) (sub_pos.mpr hb) (by linarith)),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w, U]
    ring
  dsimp only at hh ⊢
  rw [hΔ, trace_sq_inv_shift_eq_sum hA H (b - δ)
    (hn (b - δ) (sub_pos.mpr hb) (by linarith))]
  exact hh

end NLAlib.RestrictedInvertibility
