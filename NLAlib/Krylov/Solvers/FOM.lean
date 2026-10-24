import NLAlib.Krylov.Solvers.GMRESArnoldi
import NLAlib.Krylov.Processes.ArnoldiProcess

/-!
# Full orthogonalization and the Arnoldi Galerkin iterate

The FOM condition is residual orthogonality in the affine Krylov space. The
actual Arnoldi coordinates give its square system, existence and uniqueness
criterion, inverse formula, rank-one residual, and exact terminal-grade case.
Positive Arnoldi signs give the usual residual norm formula. On SPD systems
the same variational iterate is the native conjugate-gradient iterate.

Source: Saad (2003), §6.4.1 and §6.7; supports atlas `fom-def`.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A FOM iterate lies in the affine Krylov space and has residual orthogonal
to that Krylov space. This predicate imposes no unnecessary nonsingularity
assumption on the original system. Saad (2003), §6.4.1.
atlas: fom-def (partial) -/
def IsFOMIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) (x : n → ℝ) : Prop :=
  x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q ∧
    ∀ z ∈ krylovSpace A (c - A *ᵥ x₀) q, z ⬝ᵥ (c - A *ᵥ x) = 0

namespace ArnoldiDecomp

variable {A : Matrix n n ℝ} {b c x₀ : n → ℝ} {q : ℕ}

/-- The total inverse formula for the Arnoldi FOM iterate. It is a FOM iterate
when `D.H` is invertible; otherwise the total matrix inverse is zero and the
formula returns the initial vector. Saad (2003), Algorithm 6.4.
atlas: fom-def (partial) -/
def fomIterate (D : ArnoldiDecomp A b q) (x₀ : n → ℝ) : n → ℝ :=
  x₀ + D.Q *ᵥ (D.H⁻¹ *ᵥ (D.Qᵀ *ᵥ b))

/-- FOM in an actual Arnoldi basis is exactly the square Galerkin system.
The affine-space membership follows from the basis range identity.
Saad (2003), §6.4.1.
atlas: fom-def (partial) -/
theorem isFOMIterate_add_mulVec_iff (D : ArnoldiDecomp A (c - A *ᵥ x₀) q)
    (y : Fin q → ℝ) :
    IsFOMIterate A c x₀ q (x₀ + D.Q *ᵥ y) ↔
      D.H *ᵥ y = D.Qᵀ *ᵥ (c - A *ᵥ x₀) := by
  constructor
  · intro h
    exact (D.forall_dotProduct_sub_mulVec_eq_zero_iff y).1 h.2
  · intro h
    refine ⟨?_, (D.forall_dotProduct_sub_mulVec_eq_zero_iff y).2 h⟩
    rw [add_sub_cancel_left, ← D.range_Q]
    exact ⟨y, rfl⟩

/-- Every FOM iterate has coordinates in the actual Arnoldi basis.
This includes the zero-dimensional Krylov space. Saad (2003), §6.4.1. -/
theorem exists_eq_add_mulVec_of_isFOMIterate
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) q) {x : n → ℝ}
    (hx : IsFOMIterate A c x₀ q x) : ∃ y, x = x₀ + D.Q *ᵥ y := by
  have hm := hx.1
  rw [← D.range_Q] at hm
  obtain ⟨y, hy⟩ := hm
  refine ⟨y, ?_⟩
  change D.Q *ᵥ y = x - x₀ at hy
  rw [hy, add_sub_cancel]

/-- The explicit inverse formula satisfies the FOM Galerkin equations when
the small Hessenberg matrix is invertible. Saad (2003), Algorithm 6.4.
atlas: fom-def (partial) -/
theorem isFOMIterate_fomIterate (D : ArnoldiDecomp A (c - A *ᵥ x₀) q)
    (hH : IsUnit D.H) : IsFOMIterate A c x₀ q (D.fomIterate x₀) := by
  apply (D.isFOMIterate_add_mulVec_iff _).2
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hH), Matrix.one_mulVec]

/-- A FOM iterate exists uniquely exactly when the actual Hessenberg
compression is invertible. Uniqueness for one right-hand side already forces
injectivity of its linear system. Saad (2003), §6.4.1.
atlas: fom-def (partial) -/
theorem existsUnique_isFOMIterate_iff_isUnit
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) q) :
    (∃! x, IsFOMIterate A c x₀ q x) ↔ IsUnit D.H := by
  have hQ : Function.Injective D.Q.mulVec :=
    Matrix.mulVec_injective_iff.mpr D.hasOrthonormalCols.linearIndependent_col
  constructor
  · rintro ⟨x, hx, huniq⟩
    obtain ⟨y, rfl⟩ := D.exists_eq_add_mulVec_of_isFOMIterate hx
    have hy := (D.isFOMIterate_add_mulVec_iff y).1 hx
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro v w hvw
    have hshift : D.H *ᵥ (y + (v - w)) = D.Qᵀ *ᵥ (c - A *ᵥ x₀) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_sub, hvw, sub_self, add_zero]
      exact hy
    have heq := huniq (x₀ + D.Q *ᵥ (y + (v - w)))
      ((D.isFOMIterate_add_mulVec_iff _).2 hshift)
    have hc : y + (v - w) = y := hQ (add_left_cancel heq)
    exact sub_eq_zero.mp (add_left_cancel (hc.trans (add_zero y).symm))
  · intro hH
    refine ⟨D.fomIterate x₀, D.isFOMIterate_fomIterate hH, ?_⟩
    intro x hx
    obtain ⟨y, rfl⟩ := D.exists_eq_add_mulVec_of_isFOMIterate hx
    have hy := (D.isFOMIterate_add_mulVec_iff y).1 hx
    have hy₀ := (D.isFOMIterate_add_mulVec_iff _).1 (D.isFOMIterate_fomIterate hH)
    have heq : y = D.H⁻¹ *ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀)) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hH (hy.trans hy₀.symm)
    simp only [fomIterate, heq]

/-- The FOM existence-and-uniqueness criterion in determinant form.
Saad (2003), §6.4.1.
atlas: fom-def (partial) -/
theorem existsUnique_isFOMIterate_iff_det_ne_zero
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) q) :
    (∃! x, IsFOMIterate A c x₀ q x) ↔ D.H.det ≠ 0 := by
  rw [D.existsUnique_isFOMIterate_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

/-- Every FOM iterate equals the explicit inverse-Hessenberg iterate when
the compression is invertible. Saad (2003), Algorithm 6.4.
atlas: fom-def (partial) -/
theorem eq_fomIterate_of_isFOMIterate (D : ArnoldiDecomp A (c - A *ᵥ x₀) q)
    (hH : IsUnit D.H) {x : n → ℝ} (hx : IsFOMIterate A c x₀ q x) :
    x = D.fomIterate x₀ := by
  obtain ⟨y, hy, huniq⟩ := D.existsUnique_isFOMIterate_iff_isUnit.mpr hH
  exact (huniq x hx).trans (huniq _ (D.isFOMIterate_fomIterate hH)).symm

/-- Under the positive initial Arnoldi orientation, the inverse formula uses
the textbook right-hand side `‖r₀‖ e₁`. Saad (2003), Algorithm 6.4.
atlas: fom-def (partial) -/
theorem fomIterate_eq_of_pos (D : ArnoldiDecomp A b q) (hq : 0 < q)
    (hD : 0 < D.Q.col ⟨0, hq⟩ ⬝ᵥ b) (x₀ : n → ℝ) :
    D.fomIterate x₀ = x₀ + ‖WithLp.toLp 2 b‖ •
      (D.Q *ᵥ (D.H⁻¹ *ᵥ Pi.single (⟨0, hq⟩ : Fin q) 1)) := by
  rw [fomIterate, D.transpose_Q_mulVec_eq_sqrt_smul_single hq hD,
    Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- A solved Arnoldi Galerkin system has residual in the next basis direction,
with the signed last Hessenberg coefficient. Saad (2003), Proposition 6.7.
atlas: fom-def (partial) -/
theorem sub_mulVec_add_mulVec_eq_neg_smul
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1)) (hq : 0 < q)
    {y : Fin q → ℝ}
    (hy : (D.restrict q.le_succ).H *ᵥ y =
      (D.restrict q.le_succ).Qᵀ *ᵥ (c - A *ᵥ x₀)) :
    c - A *ᵥ (x₀ + (D.restrict q.le_succ).Q *ᵥ y) =
      -(D.H (Fin.last q) ⟨q - 1, by omega⟩ * y ⟨q - 1, by omega⟩) •
        D.Q.col (Fin.last q) := by
  let E := D.restrict q.le_succ
  let j : Fin q := ⟨q - 1, by omega⟩
  have hfit : E.Q *ᵥ (E.H *ᵥ y) = c - A *ᵥ x₀ := by
    rw [hy, E.mulVec_transpose_Q_mulVec_self hq]
  have hrel : A * E.Q = E.Q * E.H +
      D.H (Fin.last q) j.castSucc • vecMulVec (D.Q.col (Fin.last q)) (Pi.single j 1) :=
    D.mul_restrict_Q_eq_add_smul hq
  have hout : vecMulVec (D.Q.col (Fin.last q)) (Pi.single j 1) *ᵥ y =
      y j • D.Q.col (Fin.last q) := by
    ext i
    change (∑ k, D.Q.col (Fin.last q) i * (Pi.single j 1 : Fin q → ℝ) k * y k) =
      y j * D.Q.col (Fin.last q) i
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change D.Q.col (Fin.last q) i * (Pi.single j 1 ⬝ᵥ y) = _
    rw [single_one_dotProduct, mul_comm]
  change c - A *ᵥ (x₀ + E.Q *ᵥ y) =
    -(D.H (Fin.last q) j.castSucc * y j) • D.Q.col (Fin.last q)
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hrel, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hfit, Matrix.smul_mulVec, hout]
  simp only [sub_add_eq_sub_sub, sub_self, zero_sub, smul_smul, neg_smul]

/-- The FOM residual vector in the textbook positive initial orientation.
The next Arnoldi coefficient is signed here; its nonnegative orientation is
used only when taking the norm. Saad (2003), Proposition 6.7.
atlas: fom-def (partial) -/
theorem sub_mulVec_fomIterate_eq_neg_smul_of_pos
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1)) (hq : 0 < q)
    (hD : 0 < (D.restrict q.le_succ).Q.col ⟨0, hq⟩ ⬝ᵥ (c - A *ᵥ x₀))
    (hH : IsUnit (D.restrict q.le_succ).H) :
    c - A *ᵥ (D.restrict q.le_succ).fomIterate x₀ =
      -(D.H (Fin.last q) ⟨q - 1, by omega⟩ *
        ((D.restrict q.le_succ).H⁻¹ *ᵥ Pi.single (⟨0, hq⟩ : Fin q) 1)
          ⟨q - 1, by omega⟩ * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖) •
        D.Q.col (Fin.last q) := by
  have hy := ((D.restrict q.le_succ).isFOMIterate_add_mulVec_iff _).1
    ((D.restrict q.le_succ).isFOMIterate_fomIterate hH)
  have hr := D.sub_mulVec_add_mulVec_eq_neg_smul hq hy
  simpa only [fomIterate,
    (D.restrict q.le_succ).transpose_Q_mulVec_eq_sqrt_smul_single hq hD,
    Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using hr

/-- The FOM residual norm is the nonnegative Arnoldi subdiagonal times the
last inverse-Hessenberg coordinate and the initial residual norm. The sign
conditions are exactly the positive Arnoldi orientation. Saad (2003),
Proposition 6.7.
atlas: fom-def (partial) -/
theorem norm_sub_mulVec_fomIterate_eq_of_pos
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) (q + 1)) (hq : 0 < q)
    (hD : 0 < (D.restrict q.le_succ).Q.col ⟨0, hq⟩ ⬝ᵥ (c - A *ᵥ x₀))
    (hs : 0 ≤ D.H (Fin.last q) ⟨q - 1, by omega⟩)
    (hH : IsUnit (D.restrict q.le_succ).H) :
    ‖WithLp.toLp 2 (c - A *ᵥ (D.restrict q.le_succ).fomIterate x₀)‖ =
      D.H (Fin.last q) ⟨q - 1, by omega⟩ *
        |((D.restrict q.le_succ).H⁻¹ *ᵥ Pi.single (⟨0, hq⟩ : Fin q) 1)
          ⟨q - 1, by omega⟩| * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  have hunit : ‖WithLp.toLp 2 (D.Q.col (Fin.last q))‖ = 1 := by
    rw [norm_toLp_eq_sqrt_dotProduct_self, D.hasOrthonormalCols.col_dotProduct_col,
      if_pos rfl, Real.sqrt_one]
  rw [D.sub_mulVec_fomIterate_eq_neg_smul_of_pos hq hD hH,
    WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, hunit, mul_one,
    abs_neg, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg (norm_nonneg _)]

/-- The actual canonical Arnoldi construction supplies both sign conditions
in the FOM residual norm formula. Thus only the native dimension and small
Hessenberg invertibility hypotheses remain. Saad (2003), Algorithm 6.4 and
Proposition 6.7.
atlas: fom-def (partial) -/
theorem norm_sub_mulVec_fomIterate_eq_arnoldiDecomp
    (A : Matrix n n ℝ) (c x₀ : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hgrade : q + 1 ≤ krylovGrade A (c - A *ᵥ x₀))
    (hH : IsUnit ((arnoldiDecomp A (c - A *ᵥ x₀) (q + 1) hgrade).restrict
      q.le_succ).H) :
    let D := arnoldiDecomp A (c - A *ᵥ x₀) (q + 1) hgrade
    ‖WithLp.toLp 2 (c - A *ᵥ (D.restrict q.le_succ).fomIterate x₀)‖ =
      D.H (Fin.last q) ⟨q - 1, by omega⟩ *
        |((D.restrict q.le_succ).H⁻¹ *ᵥ Pi.single (⟨0, hq⟩ : Fin q) 1)
          ⟨q - 1, by omega⟩| * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  let D := arnoldiDecomp A (c - A *ᵥ x₀) (q + 1) hgrade
  apply D.norm_sub_mulVec_fomIterate_eq_of_pos hq ?_ ?_ hH
  · change 0 < arnoldiBasis A (c - A *ᵥ x₀) 0 ⬝ᵥ (c - A *ᵥ x₀)
    exact arnoldiBasis_zero_dotProduct_pos A (c - A *ᵥ x₀)
      (lt_of_lt_of_le (Nat.succ_pos q) hgrade)
  · have hp := arnoldiDecomp_H_subdiag_pos A (c - A *ᵥ x₀) hgrade
      (j := q - 1) (by omega)
    have heq : q - 1 + 1 = q := by omega
    simpa only [D, heq, Fin.last] using hp.le

/-- At the terminal grade, every solvable FOM square system gives the exact
linear-system solution. No symmetry assumption is needed. Saad (2003), §6.4.1.
atlas: fom-def (partial) -/
theorem sub_mulVec_fomIterate_eq_zero_of_krylovGrade_le
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) q) (hq : 0 < q)
    (hgrade : krylovGrade A (c - A *ᵥ x₀) ≤ q) (hH : IsUnit D.H) :
    c - A *ᵥ D.fomIterate x₀ = 0 := by
  have hy : D.H *ᵥ (D.H⁻¹ *ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀))) =
      D.Qᵀ *ᵥ (c - A *ᵥ x₀) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hH), Matrix.one_mulVec]
  have hfit : A *ᵥ (D.Q *ᵥ (D.H⁻¹ *ᵥ (D.Qᵀ *ᵥ (c - A *ᵥ x₀)))) =
      c - A *ᵥ x₀ := by
    rw [Matrix.mulVec_mulVec, D.mul_Q_eq_of_krylovGrade_le hgrade,
      ← Matrix.mulVec_mulVec, hy, D.mulVec_transpose_Q_mulVec_self hq]
  rw [fomIterate, Matrix.mulVec_add, hfit]
  abel

/-- Every SPD system has a unique FOM iterate in each actual Arnoldi space,
since orthonormal compression preserves positive definiteness.
Saad (2003), §6.7.
atlas: fom-def (partial) -/
theorem existsUnique_isFOMIterate_of_posDef
    (D : ArnoldiDecomp A (c - A *ᵥ x₀) q) (hA : A.PosDef) :
    ∃! x, IsFOMIterate A c x₀ q x := by
  apply D.existsUnique_isFOMIterate_iff_isUnit.mpr
  have hQ : Function.Injective D.Q.mulVec :=
    Matrix.mulVec_injective_iff.mpr D.hasOrthonormalCols.linearIndependent_col
  have hH : D.H.PosDef := by
    simpa only [H_def, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.conjTranspose_mul_mul_same hQ
  exact hH.isUnit

end ArnoldiDecomp

/-- On SPD systems, the FOM Galerkin condition is the native CG variational
condition. Saad (2003), §6.7.
atlas: fom-def (partial) -/
theorem IsFOMIterate.isCGIterate {A : Matrix n n ℝ} {c x₀ x : n → ℝ} {q : ℕ}
    (hx : IsFOMIterate A c x₀ q x) (hA : A.PosDef) : IsCGIterate A c x₀ q x :=
  isCGIterate_of_forall_dotProduct_eq_zero hA.isHermitian
    (fun i => (hA.eigenvalues_pos i).le) hx.1 hx.2

/-- The concrete inverse-Hessenberg FOM formula is the native CG iterate
for every SPD system. Its small compression is automatically invertible.
Saad (2003), §6.7.
atlas: fom-def (partial) -/
theorem ArnoldiDecomp.isCGIterate_fomIterate {A : Matrix n n ℝ}
    {c x₀ : n → ℝ} {q : ℕ} (D : ArnoldiDecomp A (c - A *ᵥ x₀) q)
    (hA : A.PosDef) : IsCGIterate A c x₀ q (D.fomIterate x₀) := by
  have hH := D.existsUnique_isFOMIterate_iff_isUnit.mp
    (D.existsUnique_isFOMIterate_of_posDef hA)
  exact (D.isFOMIterate_fomIterate hH).isCGIterate hA

end NLAlib
