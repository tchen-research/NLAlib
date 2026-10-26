import NLAlib.Krylov.Solvers.CG
import NLAlib.Krylov.Solvers.GMRES
import NLAlib.Krylov.Processes.Lanczos
/-!
# GMRES and FOM through the Arnoldi decomposition

`IsGMRESIterate` (`NLAlib.Krylov.Solvers.GMRES`) is a predicate; this file is its computational form
(Trefethen–Bau Alg. 35.1): for an Arnoldi decomposition `D : ArnoldiDecomp A r₀ (q + 1)` with
`Q_q = (D.restrict _).Q` and the `(q+1) × q` Hessenberg matrix `H̲_q = Q_{q+1}ᵀ A Q_q`
(`ArnoldiDecomp.Hbar`), the iterate `x₀ + Q_q y` is a GMRES iterate iff `y` solves the small
least-squares problem `min_y ‖Q_{q+1}ᵀ r₀ − H̲_q y‖` (with `Q_{q+1}ᵀ r₀ = ‖r₀‖ e₁` for the
canonical sign), and the residual norms agree.

## Main results

* `ArnoldiDecomp.dotProduct_sub_mulVec_add_mulVec_eq`: the residual identity
  `‖c − A(x₀ + Q_q y)‖² = ‖Q_{q+1}ᵀ r₀ − H̲_q y‖²` for every `y` (no hypothesis on `A`).
* `ArnoldiDecomp.isGMRESIterate_add_mulVec_iff`: GMRES ⟺ Arnoldi least squares;
  `IsGMRESIterate.exists_eq_add_mulVec`: every GMRES iterate has this form;
  `ArnoldiDecomp.isLeast_dotProduct_of_isGMRESIterate`: `‖r_q‖² = min_y ‖Q_{q+1}ᵀ r₀ − H̲_q y‖²`.
* `ArnoldiDecomp.transpose_Q_mulVec_eq_sqrt_smul_single` and
  `ArnoldiDecomp.isGMRESIterate_add_mulVec_iff_of_pos`: the textbook `‖r₀‖ e₁` form for a
  decomposition with `q₁ᵀ r₀ > 0` (e.g. `arnoldiDecomp`).
* FOM ingredients (`fom-def`): `ArnoldiDecomp.forall_dotProduct_sub_mulVec_eq_zero_iff`
  (Galerkin condition ⟺ the square system `H_q y = Q_qᵀ r₀`) and
  `ArnoldiDecomp.isCGIterate_add_mulVec_of_mulVec_eq` (for SPD `A` the FOM iterate is the CG
  iterate). The full FOM predicate, inverse formula, existence criterion and residual API
  are in `NLAlib.Krylov.Solvers.FOM`.

Source: Saad–Schultz (1986) [`ss86`], §3; Trefethen–Bau (1997) [`tb97`], Lect. 35, Alg. 35.1;
Saad (2011) [`saad11`], §6.5.3, Prop. 6.9 and §6.4.1. Atlas: `gmres-arnoldi-form`,
`fom-def` (partial).
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace ArnoldiDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- `Q_q Q_qᵀ b = b` for the starting vector (`b ∈ K_q`, `q ≥ 1`). Source: Saad (2011)
[`saad11`], §6.5.3 (`r₀ = β v₁`). Atlas: `gmres-arnoldi-form`. -/
theorem mulVec_transpose_Q_mulVec_self (D : ArnoldiDecomp A b q) (hq : 0 < q) :
    D.Q *ᵥ (D.Qᵀ *ᵥ b) = b := by
  refine mulVec_conjTranspose_mulVec_of_mem_range D.hasOrthonormalCols ?_
  rw [D.range_Q]
  simpa using pow_mulVec_mem_krylovSpace A b (i := 0) hq

/-- `Q_qᵀ b = (q₁ᵀ b) e₁`: the starting vector has a single nonzero Arnoldi coordinate.
Source: Saad (2011) [`saad11`], §6.5.3 (`r₀ = β v₁`). Atlas: `gmres-arnoldi-form`. -/
theorem transpose_Q_mulVec_eq_smul_single (D : ArnoldiDecomp A b q) (hq : 0 < q) :
    D.Qᵀ *ᵥ b = (D.Q.col ⟨0, hq⟩ ⬝ᵥ b) • Pi.single (⟨0, hq⟩ : Fin q) 1 := by
  ext i
  by_cases hi : (i : ℕ) = 0
  · have : i = ⟨0, hq⟩ := Fin.ext hi
    subst this
    simp [Matrix.mulVec, dotProduct, Matrix.col]
  · rw [D.transpose_Q_mulVec_apply_eq_zero (Nat.pos_of_ne_zero hi), Pi.smul_apply,
      Pi.single_eq_of_ne (fun h => hi (by rw [h])), smul_zero]

/-- **The textbook right-hand side** `Q_qᵀ b = ‖b‖ e₁` when `q₁ᵀ b > 0` (the sign convention of
`arnoldiDecomp`, `arnoldiBasis_zero_dotProduct_pos`). Source: Trefethen–Bau (1997) [`tb97`],
Lect. 35; Saad (2011) [`saad11`], §6.5.3. Atlas: `gmres-arnoldi-form`. -/
theorem transpose_Q_mulVec_eq_sqrt_smul_single (D : ArnoldiDecomp A b q) (hq : 0 < q)
    (hD : 0 < D.Q.col ⟨0, hq⟩ ⬝ᵥ b) :
    D.Qᵀ *ᵥ b = ‖WithLp.toLp 2 b‖ • Pi.single (⟨0, hq⟩ : Fin q) 1 := by
  rw [norm_toLp_eq_sqrt_dotProduct_self, D.transpose_Q_mulVec_eq_smul_single hq]
  congr 1
  have h := D.sq_transpose_Q_mulVec_apply_zero hq
  have h1 : (D.Qᵀ *ᵥ b) ⟨0, hq⟩ = D.Q.col ⟨0, hq⟩ ⬝ᵥ b := by
    simp [Matrix.mulVec, dotProduct, Matrix.col]
  rw [h1] at h
  rw [← h, Real.sqrt_sq hD.le]

variable {c x₀ : n → ℝ}

/-- **The GMRES residual identity**: for `D : ArnoldiDecomp A r₀ (q + 1)`, `r₀ = c − A x₀`, and
every `y`, `‖c − A (x₀ + Q_q y)‖² = ‖Q_{q+1}ᵀ r₀ − H̲_q y‖²`. No hypothesis on `A`.
Source: Trefethen–Bau (1997) [`tb97`], Lect. 35 (eq. (35.3)–(35.4)); Saad (2011) [`saad11`],
§6.5.3, eq. (6.27). Proof: `r₀ = Q_{q+1} Q_{q+1}ᵀ r₀`, `A Q_q = Q_{q+1} H̲_q`, and `Q_{q+1}`
preserves norms.
atlas: gmres-arnoldi-form -/
theorem dotProduct_sub_mulVec_add_mulVec_eq (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1))
    (y : Fin q → ℝ) :
    (c - A *ᵥ (x₀ + (D.restrict q.le_succ).Q *ᵥ y)) ⬝ᵥ
        (c - A *ᵥ (x₀ + (D.restrict q.le_succ).Q *ᵥ y)) =
      (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y) ⬝ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y) := by
  have hres : c - A *ᵥ (x₀ + (D.restrict q.le_succ).Q *ᵥ y) =
      D.Q *ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y) := by
    rw [Matrix.mulVec_sub, D.mulVec_transpose_Q_mulVec_self (Nat.succ_pos q),
      Matrix.mulVec_mulVec, ← D.mul_restrict_Q_eq_mul, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_add]
    abel
  rw [hres]
  simpa only [star_trivial] using
    star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols D.hasOrthonormalCols _

/-- Every vector of `K_q(A, b)` is `Q_q y` for some `y` (`range Q_q = K_q`). Source:
Trefethen–Bau (1997) [`tb97`], Lect. 35. Atlas: `gmres-arnoldi-form`. -/
theorem exists_eq_mulVec_of_mem (D : ArnoldiDecomp A b (q + 1)) {z : n → ℝ}
    (hz : z ∈ krylovSpace A b q) : ∃ y, z = (D.restrict q.le_succ).Q *ᵥ y := by
  rw [← (D.restrict q.le_succ).range_Q] at hz
  obtain ⟨y, rfl⟩ := hz
  exact ⟨y, rfl⟩

/-- `Q_q y ∈ K_q(A, b)`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 35.
Atlas: `gmres-arnoldi-form`. -/
theorem restrict_Q_mulVec_mem (D : ArnoldiDecomp A b (q + 1)) (y : Fin q → ℝ) :
    (D.restrict q.le_succ).Q *ᵥ y ∈ krylovSpace A b q := by
  rw [← (D.restrict q.le_succ).range_Q]
  exact ⟨y, rfl⟩

/-- **GMRES is Arnoldi least squares**: for `D : ArnoldiDecomp A r₀ (q + 1)` (`r₀ = c − A x₀`,
which needs `q < ν(A, r₀)`), `x₀ + Q_q y` is a GMRES iterate iff `y` minimises
`‖Q_{q+1}ᵀ r₀ − H̲_q y‖²`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 35, Alg. 35.1;
Saad (2011) [`saad11`], §6.5.3, Prop. 6.9; Saad–Schultz (1986) [`ss86`], §3. Deviation: the
right-hand side is `Q_{q+1}ᵀ r₀` (`= ±‖r₀‖ e₁` for any decomposition,
`transpose_Q_mulVec_eq_smul_single`); the `‖r₀‖ e₁` form is
`isGMRESIterate_add_mulVec_iff_of_pos`. Uses atlas `gmres-def`, `arnoldi-relation`.
atlas: gmres-arnoldi-form -/
theorem isGMRESIterate_add_mulVec_iff (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1))
    (y : Fin q → ℝ) :
    IsGMRESIterate A c x₀ q (x₀ + (D.restrict q.le_succ).Q *ᵥ y) ↔
      ∀ y' : Fin q → ℝ,
        (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y) ⬝ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y) ≤
          (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y') ⬝ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y') := by
  rw [IsGMRESIterate, IsAffineMinimizer, add_sub_cancel_left]
  simp only [D.restrict_Q_mulVec_mem y, true_and, star_trivial, RCLike.re_to_real]
  constructor
  · intro h y'
    have := h _ (D.restrict_Q_mulVec_mem y')
    rwa [D.dotProduct_sub_mulVec_add_mulVec_eq, D.dotProduct_sub_mulVec_add_mulVec_eq] at this
  · intro h z hz
    obtain ⟨y', rfl⟩ := D.exists_eq_mulVec_of_mem hz
    rw [D.dotProduct_sub_mulVec_add_mulVec_eq, D.dotProduct_sub_mulVec_add_mulVec_eq]
    exact h y'

/-- **GMRES is Arnoldi least squares, `‖r₀‖ e₁` form**: as `isGMRESIterate_add_mulVec_iff` for
a decomposition with `q₁ᵀ r₀ > 0` (e.g. the canonical `arnoldiDecomp`), `x₀ + Q_q y` is a GMRES
iterate iff `y` minimises `‖ ‖r₀‖ e₁ − H̲_q y ‖²`. Source: Trefethen–Bau (1997) [`tb97`],
Lect. 35, Alg. 35.1; Saad (2011) [`saad11`], Prop. 6.9.
atlas: gmres-arnoldi-form -/
theorem isGMRESIterate_add_mulVec_iff_of_pos (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1))
    (hD : 0 < D.Q.col 0 ⬝ᵥ (c - A *ᵥ x₀)) (y : Fin q → ℝ) :
    IsGMRESIterate A c x₀ q (x₀ + (D.restrict q.le_succ).Q *ᵥ y) ↔
      ∀ y' : Fin q → ℝ,
        (√((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) • Pi.single 0 1 - D.Hbar *ᵥ y) ⬝ᵥ
            (√((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) • Pi.single 0 1 - D.Hbar *ᵥ y) ≤
          (√((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) • Pi.single 0 1 - D.Hbar *ᵥ y') ⬝ᵥ
            (√((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) • Pi.single 0 1 - D.Hbar *ᵥ y') := by
  rw [isGMRESIterate_add_mulVec_iff,
    D.transpose_Q_mulVec_eq_sqrt_smul_single (Nat.succ_pos q) hD,
    norm_toLp_eq_sqrt_dotProduct_self]
  rfl

/-- **Every GMRES iterate is of Arnoldi form**: if `x` is a GMRES iterate then
`x = x₀ + Q_q y` for some `y`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 35.
Atlas: `gmres-arnoldi-form`. -/
theorem exists_eq_add_mulVec_of_isGMRESIterate (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1))
    {x : n → ℝ} (hx : IsGMRESIterate A c x₀ q x) :
    ∃ y, x = x₀ + (D.restrict q.le_succ).Q *ᵥ y := by
  obtain ⟨y, hy⟩ := D.exists_eq_mulVec_of_mem hx.1
  exact ⟨y, by rw [← hy, add_sub_cancel]⟩

/-- **The GMRES residual norm is the small least-squares minimum**: for every GMRES iterate `x`,
`‖c − A x‖² = min_y ‖Q_{q+1}ᵀ r₀ − H̲_q y‖²` (as `IsLeast`). Source: Trefethen–Bau (1997)
[`tb97`], Lect. 35; Saad (2011) [`saad11`], Prop. 6.9 (the residual norm is computed without
forming `x_q`).
atlas: gmres-arnoldi-form -/
theorem isLeast_dotProduct_of_isGMRESIterate (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1))
    {x : n → ℝ} (hx : IsGMRESIterate A c x₀ q x) :
    IsLeast (Set.range fun y : Fin q → ℝ =>
        (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y) ⬝ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.Hbar *ᵥ y))
      ((c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x)) := by
  obtain ⟨y, rfl⟩ := D.exists_eq_add_mulVec_of_isGMRESIterate hx
  rw [D.dotProduct_sub_mulVec_add_mulVec_eq]
  refine ⟨⟨y, rfl⟩, ?_⟩
  rintro _ ⟨y', rfl⟩
  exact (D.isGMRESIterate_add_mulVec_iff y).1 hx y'

/-! ### FOM: the square Galerkin system -/

/-- **FOM is the square system**: for `D : ArnoldiDecomp A r₀ q`, the residual of `x₀ + Q_q y` is
orthogonal to `K_q(A, r₀)` (the Galerkin / FOM condition) iff `H_q y = Q_qᵀ r₀` (`= ±‖r₀‖ e₁`).
No hypothesis on `A`. Source: Saad (2011) [`saad11`], §6.4.1 (Alg. 6.4, `y_m = H_m⁻¹ (β e₁)`);
Saad (2003) [`saad03`], §6.4.1. This identity states the Galerkin condition directly;
the full FOM predicate and its inverse and residual formulas are in
`NLAlib.Krylov.Solvers.FOM`.
atlas: fom-def (partial) -/
theorem forall_dotProduct_sub_mulVec_eq_zero_iff (D : ArnoldiDecomp A (c - A *ᵥ x₀) q)
    (y : Fin q → ℝ) :
    (∀ z ∈ krylovSpace A (c - A *ᵥ x₀) q, z ⬝ᵥ (c - A *ᵥ (x₀ + D.Q *ᵥ y)) = 0) ↔
      D.H *ᵥ y = D.Qᵀ *ᵥ (c - A *ᵥ x₀) := by
  have hr : D.Qᵀ *ᵥ (c - A *ᵥ (x₀ + D.Q *ᵥ y)) = D.Qᵀ *ᵥ (c - A *ᵥ x₀) - D.H *ᵥ y := by
    rw [Matrix.mulVec_add, ← sub_sub, Matrix.mulVec_sub (D.Qᵀ), H_def, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  constructor
  · intro h
    rw [← sub_eq_zero, ← neg_sub, neg_eq_zero, ← hr]
    ext i
    have := h _ (D.graded.col_mem i |> krylovSpace_mono A _ (by have := i.isLt; omega))
    simpa [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply] using this
  · intro h z hz
    rw [← D.range_Q] at hz
    obtain ⟨y', rfl⟩ := hz
    rw [Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hr, h, sub_self, zero_dotProduct]

/-- **For SPD `A` the FOM iterate is the CG iterate**: if `H_q y = Q_qᵀ r₀` then `x₀ + Q_q y`
satisfies `IsCGIterate A c x₀ q`. Source: Saad (2003) [`saad03`], §6.7 (CG as the symmetric
FOM / Lanczos method); Saad (2011) [`saad11`], §6.7.1. Uses atlas `cg-convergence`.
atlas: fom-def (partial) -/
theorem isCGIterate_add_mulVec_of_mulVec_eq (hA : A.PosDef) (D : ArnoldiDecomp A (c - A *ᵥ x₀) q)
    {y : Fin q → ℝ} (hy : D.H *ᵥ y = D.Qᵀ *ᵥ (c - A *ᵥ x₀)) :
    IsCGIterate A c x₀ q (x₀ + D.Q *ᵥ y) := by
  refine isCGIterate_of_forall_dotProduct_eq_zero hA.isHermitian
    (fun i => (hA.eigenvalues_pos i).le) ?_ ((D.forall_dotProduct_sub_mulVec_eq_zero_iff y).2 hy)
  rw [add_sub_cancel_left, ← D.range_Q]
  exact ⟨y, rfl⟩

end ArnoldiDecomp

end NLAlib
