import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Rank-one inverse and weighted trace identities

This file provides the Sherman–Morrison style formula for the inverse of a
rank-one update `M + vecMulVec u v` over a field, together with the
`t`-weighted specialization and the trace identity used by BSS-type
spectral-selection arguments.

The only scalar nonvanishing hypothesis is `1 + v ⬝ᵥ (M⁻¹ *ᵥ u) ≠ 0`;
the interaction `v ⬝ᵥ (M⁻¹ *ᵥ u)` itself is allowed to be zero, so the
empty-index and zero-vector cases are covered.  No symmetry or positivity is
assumed.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]

/-- The inverse of a rank-one update: Sherman–Morrison.
Source: standard Sherman–Morrison formula, `u = 0` / `v = 0` / empty index
cases included because only `1 + q ≠ 0` is required (`q` itself may vanish). -/
theorem inv_add_vecMulVec (M : Matrix n n K) (u v : n → K)
    (hM : IsUnit M.det) (hd : 1 + v ⬝ᵥ (M⁻¹ *ᵥ u) ≠ 0) :
    (M + vecMulVec u v)⁻¹ =
      M⁻¹ - ((1 + v ⬝ᵥ (M⁻¹ *ᵥ u))⁻¹ : K) •
        (M⁻¹ * vecMulVec u v * M⁻¹) := by
  let q : K := v ⬝ᵥ (M⁻¹ *ᵥ u)
  let c : K := (1 + q)⁻¹
  let U : Matrix n n K := vecMulVec u v
  have hcq : c * (1 + q) = 1 := by
    dsimp [c]
    exact inv_mul_cancel₀ hd
  have hUinv : U * M⁻¹ * U = q • U := by
    dsimp [U, q]
    rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, dotProduct_mulVec, vecMulVec_smul]
  have hMP : M * (M⁻¹ * U * M⁻¹) = U * M⁻¹ := by
    calc
      M * (M⁻¹ * U * M⁻¹) = (M * M⁻¹) * U * M⁻¹ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = U * M⁻¹ := by
        rw [Matrix.mul_nonsing_inv M hM]
        simp
  have hUU : U * (M⁻¹ * U * M⁻¹) = q • (U * M⁻¹) := by
    calc
      U * (M⁻¹ * U * M⁻¹) = (U * M⁻¹ * U) * M⁻¹ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = (q • U) * M⁻¹ := by
        rw [hUinv]
      _ = q • (U * M⁻¹) := by
        rw [Matrix.smul_mul]
  have hsum : (M + U) * (M⁻¹ * U * M⁻¹) = (1 + q) • (U * M⁻¹) := by
    calc
      (M + U) * (M⁻¹ * U * M⁻¹)
          = M * (M⁻¹ * U * M⁻¹) + U * (M⁻¹ * U * M⁻¹) := by
            rw [Matrix.add_mul]
      _ = U * M⁻¹ + U * (M⁻¹ * U * M⁻¹) := by
            rw [hMP]
      _ = U * M⁻¹ + q • (U * M⁻¹) := by
            rw [hUU]
      _ = (1 + q) • (U * M⁻¹) := by
            rw [add_smul]
            simp
  have hright : (M + U) * (M⁻¹ - c • (M⁻¹ * U * M⁻¹)) = 1 := by
    rw [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_nonsing_inv M hM,
      Matrix.mul_smul, hsum, smul_smul]
    rw [hcq, one_smul]
    abel
  exact inv_eq_right_inv hright

/-- The `t`-weighted rank-one inverse, `u = t • v`.
Source: weighted Sherman–Morrison used in BSS/stable-rank restricted
invertibility arguments; `q = v ⬝ᵥ (M⁻¹ *ᵥ v)` may vanish. -/
theorem inv_add_smul_vecMulVec_self (M : Matrix n n K) (v : n → K) (t : K)
    (hM : IsUnit M.det)
    (hd : 1 + t * (v ⬝ᵥ (M⁻¹ *ᵥ v)) ≠ 0) :
    (M + t • vecMulVec v v)⁻¹ =
      M⁻¹ - (t / (1 + t * (v ⬝ᵥ (M⁻¹ *ᵥ v)))) •
        (M⁻¹ * vecMulVec v v * M⁻¹) := by
  have hq : v ⬝ᵥ (M⁻¹ *ᵥ (t • v)) = t * (v ⬝ᵥ (M⁻¹ *ᵥ v)) := by
    rw [mulVec_smul, dotProduct_smul]
    rfl
  have hd' : 1 + v ⬝ᵥ (M⁻¹ *ᵥ (t • v)) ≠ 0 := by
    simpa [hq] using hd
  have hmain := inv_add_vecMulVec M (t • v) v hM hd'
  have hU : vecMulVec (t • v) v = t • vecMulVec v v := by
    rw [smul_vecMulVec]
  rw [hU, hq] at hmain
  have hP : M⁻¹ * (t • vecMulVec v v) * M⁻¹ =
      t • (M⁻¹ * vecMulVec v v * M⁻¹) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hP] at hmain
  have hscalar :
      ((1 + t * (v ⬝ᵥ (M⁻¹ *ᵥ v)))⁻¹ : K) •
          (t • (M⁻¹ * vecMulVec v v * M⁻¹)) =
        (t / (1 + t * (v ⬝ᵥ (M⁻¹ *ᵥ v)))) •
          (M⁻¹ * vecMulVec v v * M⁻¹) := by
    rw [smul_smul]
    rw [mul_comm, ← div_eq_mul_inv]
  rw [hscalar] at hmain
  exact hmain

/-- Trace of `H` times the `t`-weighted rank-one inverse.
No symmetry or positivity of `M` or `H` is required; the identity is purely
algebraic.  Source: BSS/stable-rank restricted invertibility trace step. -/
theorem trace_mul_inv_add_smul_vecMulVec_self (M H : Matrix n n K)
    (v : n → K) (t : K) (hM : IsUnit M.det)
    (hd : 1 + t * (v ⬝ᵥ (M⁻¹ *ᵥ v)) ≠ 0) :
    (H * (M + t • vecMulVec v v)⁻¹).trace =
      (H * M⁻¹).trace -
        (t / (1 + t * (v ⬝ᵥ (M⁻¹ *ᵥ v)))) *
          (v ⬝ᵥ ((M⁻¹ * H * M⁻¹) *ᵥ v)) := by
  rw [inv_add_smul_vecMulVec_self M v t hM hd]
  have htrace : (H * (M⁻¹ * vecMulVec v v * M⁻¹)).trace =
      v ⬝ᵥ ((M⁻¹ * H * M⁻¹) *ᵥ v) := by
    calc
      (H * (M⁻¹ * vecMulVec v v * M⁻¹)).trace
          = (H * M⁻¹ * vecMulVec v v * M⁻¹).trace := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = (M⁻¹ * (H * M⁻¹) * vecMulVec v v).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (M⁻¹ * H * M⁻¹ * vecMulVec v v).trace := by
            rw [← Matrix.mul_assoc]
      _ = ((M⁻¹ * H * M⁻¹) * vecMulVec v v).trace := by
            rfl
      _ = (vecMulVec ((M⁻¹ * H * M⁻¹) *ᵥ v) v).trace := by
            rw [Matrix.mul_vecMulVec]
      _ = ((M⁻¹ * H * M⁻¹) *ᵥ v) ⬝ᵥ v := by
            rw [Matrix.trace_vecMulVec]
      _ = v ⬝ᵥ ((M⁻¹ * H * M⁻¹) *ᵥ v) := by
            rw [dotProduct_comm]
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, htrace]
  rfl

end Matrix

end
