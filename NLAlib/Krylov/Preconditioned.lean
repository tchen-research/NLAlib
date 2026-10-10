import Mathlib.Analysis.Matrix.Order
import NLAlib.Krylov.CG
import NLAlib.Krylov.GaussQuadrature

/-!
# Preconditioned CG and CGLS/LSQR

Two minimising Krylov methods that reduce to CG by a change of variables.

**Preconditioned CG.** For symmetric positive definite `A` and preconditioner `P`, the PCG
iterate minimises `φ(x) = ½ xᵀAx − cᵀx` over `x₀ + K_q(P⁻¹A, P⁻¹r₀)` (`IsPCGIterate`). For any
`W` with `Wᵀ P W = I` (e.g. the symmetric `W = P^{-1/2}`, or `W = L⁻ᵀ` for `P = LLᵀ`),
`K_q(P⁻¹A, P⁻¹r₀) = W K_q(WᵀAW, Wᵀr₀)` (`krylovSpace_mul_mulVec_eq_map`) and PCG is CG on
`WᵀAW` in the variable `W⁻¹x` (`isPCGIterate_iff_isCGIterate`). Under the Loewner sandwich
`a P ≼ A ≼ b P` the spectrum of `WᵀAW` lies in `[a, b]`, and the CG bound (through the class
theorem `quadForm_sub_le_of_isAffineMinimiser`) gives the `√(b/a)` rate
(`quadForm_sub_le_of_isPCGIterate`).

**CGLS/LSQR.** For rectangular `A`, the iterate minimising `‖b − Ay‖²` over
`x₀ + K_q(AᵀA, Aᵀ(b − Ax₀))` (`IsCGLSIterate`) is the CG iterate for the normal equations
(`isCGLSIterate_iff_isCGIterate`); with the singular values of `A` in `[σ_lo, σ_hi]`,
`‖A(x_q − x⋆)‖ ≤ 2((σ_hi − σ_lo)/(σ_hi + σ_lo))^q ‖A(x₀ − x⋆)‖`
(`dotProduct_mulVec_sub_le_of_isCGLSIterate`), and the residual splits as
`‖b − Ax‖² = ‖b − Ax⋆‖² + ‖A(x − x⋆)‖²`.

Source: Saad (2003) [`saad03`], §8.3 (CGNR) and §9.2 (PCG); Greenbaum (1997) [`greenbaum97`],
Ch. 8; Paige–Saunders (1982) [`ps82`] (LSQR).
Atlas: `preconditioned-cg`, `cgls-lsqr-bound`; uses `cg-convergence`, `krylov-subspace`.
-/

noncomputable section

open scoped Matrix Polynomial MatrixOrder
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Change of variables -/

/-- `(W B)^i W = W (B W)^i`. Helper for `preconditioned-cg`. -/
theorem mul_pow_mul_eq_mul_mul_pow (W B : Matrix n n ℝ) (i : ℕ) :
    (W * B) ^ i * W = W * (B * W) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, pow_succ', ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc W B W]

/-- **Krylov spaces under a change of variables:** `K_q(WB, Wv) = W K_q(BW, v)`. With
`P⁻¹ = WWᵀ` and `B = WᵀA` this is `K_q(P⁻¹A, P⁻¹r) = W K_q(WᵀAW, Wᵀr)`, the identity behind
split preconditioning. Source: Saad (2003) [`saad03`], §9.2.1.
atlas: preconditioned-cg (partial) -/
theorem krylovSpace_mul_mulVec_eq_map (W B : Matrix n n ℝ) (v : n → ℝ) (q : ℕ) :
    krylovSpace (W * B) (W *ᵥ v) q = (krylovSpace (B * W) v q).map W.mulVecLin := by
  rw [krylovSpace, krylovSpace, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  simp only [Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    mul_pow_mul_eq_mul_mul_pow]

/-- **Affine minimisers under an invertible change of variables:** `x` minimises `E` over
`x₀ + W S` iff `W⁻¹x` minimises `E ∘ W` over `W⁻¹x₀ + S`. Helper for `preconditioned-cg`
(belongs in `NLAlib.Krylov.Minimiser`). -/
theorem isAffineMinimiser_map_iff {W : Matrix n n ℝ} (hW : IsUnit W) {E : (n → ℝ) → ℝ}
    {x₀ x : n → ℝ} {S : Submodule ℝ (n → ℝ)} :
    IsAffineMinimiser E x₀ (S.map W.mulVecLin) x ↔
      IsAffineMinimiser (fun y => E (W *ᵥ y)) (W⁻¹ *ᵥ x₀) S (W⁻¹ *ᵥ x) := by
  have hd := (Matrix.isUnit_iff_isUnit_det W).1 hW
  have hWW : ∀ v, W *ᵥ (W⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hd, Matrix.one_mulVec]
  have hWW' : ∀ v, W⁻¹ *ᵥ (W *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul W hd, Matrix.one_mulVec]
  have hmem : ∀ v, v ∈ S.map W.mulVecLin ↔ W⁻¹ *ᵥ v ∈ S := fun v => by
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [hWW'] using hs
    · intro hv
      exact ⟨_, hv, by simp [hWW]⟩
  unfold IsAffineMinimiser
  rw [hmem, Matrix.mulVec_sub]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · have := h (W *ᵥ y) ((hmem _).2 (by rwa [hWW']))
    simpa [hWW, Matrix.mulVec_add] using this
  · have := h (W⁻¹ *ᵥ y) ((hmem _).1 hy)
    simpa [hWW, Matrix.mulVec_add] using this

omit [DecidableEq n] in
/-- `quadForm (WᵀAW) v = quadForm A (Wv)`. Helper for `preconditioned-cg` (belongs in
`NLAlib.Matrix.QuadForm`). -/
theorem quadForm_transpose_mul_mul (A W : Matrix n n ℝ) (v : n → ℝ) :
    quadForm (Wᵀ * A * W) v = quadForm A (W *ᵥ v) := by
  simp only [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Wᵀ,
    Matrix.vecMul_transpose]

omit [DecidableEq n] in
/-- The CG objective under a change of variables: `φ_{A,c}(Wy) = φ_{WᵀAW, Wᵀc}(y)`.
Helper for `preconditioned-cg`. -/
theorem cgObjective_mulVec (A W : Matrix n n ℝ) (c y : n → ℝ) :
    cgObjective A c (W *ᵥ y) = cgObjective (Wᵀ * A * W) (Wᵀ *ᵥ c) y := by
  rw [cgObjective, cgObjective, quadForm_transpose_mul_mul, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]

/-! ### Preconditioned CG -/

/-- `x` is a `q`-th preconditioned-CG iterate for `A x = c` with preconditioner `P`, started at
`x₀`: it minimises `cgObjective A c` (equivalently the `A`-norm error) over
`x₀ + K_q(P⁻¹A, P⁻¹(c − A x₀))`. Source: Saad (2003) [`saad03`], §9.2 (Alg. 9.1 computes it);
Greenbaum (1997) [`greenbaum97`], Ch. 8. Deviation: a predicate, not the recurrence.
atlas: preconditioned-cg -/
def IsPCGIterate (A P : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) (x : n → ℝ) : Prop :=
  IsAffineMinimiser (cgObjective A c) x₀ (krylovSpace (P⁻¹ * A) (P⁻¹ *ᵥ (c - A *ᵥ x₀)) q) x

/-- If `Wᵀ P W = I` then `W` is invertible. Helper for `preconditioned-cg`. -/
theorem isUnit_of_transpose_mul_mul_eq_one {P W : Matrix n n ℝ} (hW : Wᵀ * P * W = 1) :
    IsUnit W :=
  (Matrix.isUnit_iff_isUnit_det W).2 (Matrix.isUnit_det_of_left_inverse hW)

/-- If `Wᵀ P W = I` then `P⁻¹ = W Wᵀ`. Helper for `preconditioned-cg`. -/
theorem inv_eq_mul_transpose_of_transpose_mul_mul_eq_one {P W : Matrix n n ℝ}
    (hW : Wᵀ * P * W = 1) : P⁻¹ = W * Wᵀ := by
  refine Matrix.inv_eq_left_inv ?_
  have h : W * (Wᵀ * P) = 1 := mul_eq_one_comm.1 hW
  rwa [← Matrix.mul_assoc] at h

/-- A positive definite `P` has a symmetric inverse square root: some `W = Wᵀ` with
`Wᵀ P W = I` (`W = P^{-1/2} = U diag(λ^{-1/2}) Uᵀ`). Source: Horn–Johnson (2013), Thm 7.2.6.
Helper for `preconditioned-cg` (belongs in `NLAlib.Matrix`). -/
theorem exists_isSymm_transpose_mul_mul_eq_one {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ W : Matrix n n ℝ, W.IsSymm ∧ Wᵀ * P * W = 1 := by
  set U : Matrix n n ℝ := (hP.1.eigenvectorUnitary : Matrix n n ℝ)
  set D : Matrix n n ℝ := Matrix.diagonal fun i => 1 / √(hP.1.eigenvalues i)
  have hUU : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hP.1
  have hUU' : U * Uᵀ = 1 := eigenvectorUnitary_mul_transpose_self hP.1
  have hP' := eq_eigenvectorUnitary_mul_diagonal_mul_transpose hP.1
  have hD : Dᵀ = D := Matrix.diagonal_transpose _
  have hsym : (U * D * Uᵀ)ᵀ = U * D * Uᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD,
      Matrix.mul_assoc]
  refine ⟨U * D * Uᵀ, hsym, ?_⟩
  have hdiag : D * Matrix.diagonal hP.1.eigenvalues * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    have hpos := hP.eigenvalues_pos i
    have hs : √(hP.1.eigenvalues i) ^ 2 = hP.1.eigenvalues i := Real.sq_sqrt hpos.le
    have hs0 : 0 < √(hP.1.eigenvalues i) := Real.sqrt_pos.2 hpos
    field_simp
    linarith [hs]
  rw [hsym, hP']
  calc U * D * Uᵀ * (U * Matrix.diagonal hP.1.eigenvalues * Uᵀ) * (U * D * Uᵀ)
      = U * (D * (Uᵀ * U) * Matrix.diagonal hP.1.eigenvalues * (Uᵀ * U) * D) * Uᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, hdiag, Matrix.mul_one, hUU']

/-- **PCG is CG on the split-preconditioned system.** If `Wᵀ P W = I` (so `P⁻¹ = WWᵀ`), then `x`
is a PCG iterate for `(A, P, c, x₀)` iff `W⁻¹x` is a CG iterate for `WᵀAW ŷ = Wᵀc` from
`W⁻¹x₀`. With `W = P^{-1/2}` this is CG on `P^{-1/2} A P^{-1/2}`; with `W = L⁻ᵀ`, `P = LLᵀ`,
CG on `L⁻¹AL⁻ᵀ`. Source: Saad (2003) [`saad03`], §9.2.1 (split preconditioning).
atlas: preconditioned-cg (partial) -/
theorem isPCGIterate_iff_isCGIterate {A P W : Matrix n n ℝ} (hW : Wᵀ * P * W = 1)
    {c x₀ x : n → ℝ} {q : ℕ} :
    IsPCGIterate A P c x₀ q x ↔
      IsCGIterate (Wᵀ * A * W) (Wᵀ *ᵥ c) (W⁻¹ *ᵥ x₀) q (W⁻¹ *ᵥ x) := by
  have hU := isUnit_of_transpose_mul_mul_eq_one hW
  have hd := (Matrix.isUnit_iff_isUnit_det W).1 hU
  have hK : krylovSpace (P⁻¹ * A) (P⁻¹ *ᵥ (c - A *ᵥ x₀)) q =
      (krylovSpace (Wᵀ * A * W) (Wᵀ *ᵥ c - (Wᵀ * A * W) *ᵥ (W⁻¹ *ᵥ x₀)) q).map W.mulVecLin := by
    have hr : Wᵀ *ᵥ c - (Wᵀ * A * W) *ᵥ (W⁻¹ *ᵥ x₀) = Wᵀ *ᵥ (c - A *ᵥ x₀) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv W hd, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]
    rw [hr, inv_eq_mul_transpose_of_transpose_mul_mul_eq_one hW, Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, krylovSpace_mul_mulVec_eq_map]
  rw [IsPCGIterate, hK, isAffineMinimiser_map_iff hU, IsCGIterate]
  simp only [cgObjective_mulVec]

/-- **Preconditioned CG bound under a Loewner sandwich.** Let `P` be positive definite, `A` with
`a P ≼ A ≼ b P` for `0 < a ≤ b` (so `A` is symmetric positive definite and `κ(P⁻¹A) ≤ b/a`),
`A x⋆ = c`, and `x` a `q`-th PCG iterate from `x₀`. Then
`‖x − x⋆‖_A² ≤ (2((√b − √a)/(√b + √a))^q)² ‖x₀ − x⋆‖_A²`.
Proof: CG on `P^{-1/2} A P^{-1/2}`, whose spectrum lies in `[a, b]`
(`isPCGIterate_iff_isCGIterate`, `quadForm_sub_le_of_isCGIterate_of_le`).
Source: Saad (2003) [`saad03`], §9.2; Greenbaum (1997) [`greenbaum97`], Ch. 8.
Deviation: squared `A`-norms.
atlas: preconditioned-cg -/
theorem quadForm_sub_le_of_isPCGIterate {A P : Matrix n n ℝ} (hP : P.PosDef) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlow : a • P ≤ A) (hup : A ≤ b • P) {c x₀ xs x : n → ℝ}
    (hxs : A *ᵥ xs = c) {q : ℕ} (hx : IsPCGIterate A P c x₀ q x) :
    quadForm A (x - xs) ≤ (2 * ((√b - √a) / (√b + √a)) ^ q) ^ 2 * quadForm A (x₀ - xs) := by
  obtain ⟨W, -, hW⟩ := exists_isSymm_transpose_mul_mul_eq_one hP
  have hU := isUnit_of_transpose_mul_mul_eq_one hW
  have hd := (Matrix.isUnit_iff_isUnit_det W).1 hU
  have hWW : ∀ v, W *ᵥ (W⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hd, Matrix.one_mulVec]
  -- `A` is symmetric: `A = b P − (b P − A)`
  have hAh : A.IsHermitian := by
    have h1 : (b • P - A).IsHermitian := (Matrix.le_iff.1 hup).1
    have h2 : (b • P).IsHermitian := hP.1.smul (IsSelfAdjoint.all b)
    simpa using h2.sub h1
  set B := Wᵀ * A * W with hBdef
  have hWt : Wᴴ = Wᵀ := Matrix.conjTranspose_eq_transpose_of_trivial W
  have hBh : B.IsHermitian := by
    have := Matrix.isHermitian_conjTranspose_mul_mul W hAh
    rwa [hWt] at this
  -- the congruence `Wᵀ (·) W` maps the sandwich to `a I ≼ B ≼ b I`
  have hcong : ∀ s : ℝ, Wᵀ * (A - s • P) * W = B - s • 1 := fun s => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hW]
  have hcong' : ∀ s : ℝ, Wᵀ * (s • P - A) * W = s • 1 - B := fun s => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hW]
  have hlowB : (B - a • 1).PosSemidef := by
    have := (Matrix.le_iff.1 hlow).conjTranspose_mul_mul_same W
    rwa [hWt, hcong] at this
  have hupB : (b • 1 - B).PosSemidef := by
    have := (Matrix.le_iff.1 hup).conjTranspose_mul_mul_same W
    rwa [hWt, hcong'] at this
  have hspec : ∀ i, hBh.eigenvalues i ∈ Set.Icc a b := fun i => by
    set u : n → ℝ := (hBh.eigenvectorBasis i : n → ℝ)
    have hu : u ⬝ᵥ u = 1 := eigenvectorBasis_dotProduct_self hBh i
    have hval := eigenvalues_eq_dotProduct_mulVec hBh i
    have h1 := hlowB.dotProduct_mulVec_nonneg u
    have h2 := hupB.dotProduct_mulVec_nonneg u
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hu] at h1 h2
    constructor <;> linarith
  have hxs' : B *ᵥ (W⁻¹ *ᵥ xs) = Wᵀ *ᵥ c := by
    rw [hBdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hWW, hxs]
  have hcg := quadForm_sub_le_of_isCGIterate_of_le hBh ha hab hspec hxs'
    ((isPCGIterate_iff_isCGIterate hW).1 hx)
  simpa only [← Matrix.mulVec_sub, quadForm_transpose_mul_mul, hWW, hBdef] using hcg

/-! ### CGLS / LSQR -/

variable {m : Type*} [Fintype m]

/-- `x` is a `q`-th CGLS (equivalently, in exact arithmetic, LSQR) iterate for
`min ‖b − A x‖` from `x₀`: it minimises `‖b − Ay‖²` over `x₀ + K_q(AᵀA, Aᵀ(b − Ax₀))`.
Source: Saad (2003) [`saad03`], §8.3 (CGNR); Paige–Saunders (1982) [`ps82`]. Deviation: a
predicate, not the Golub–Kahan recurrence.
atlas: cgls-lsqr-bound -/
def IsCGLSIterate (A : Matrix m n ℝ) (b : m → ℝ) (x₀ : n → ℝ) (q : ℕ) (x : n → ℝ) : Prop :=
  IsAffineMinimiser (fun y => (b - A *ᵥ y) ⬝ᵥ (b - A *ᵥ y)) x₀
    (krylovSpace (Aᵀ * A) (Aᵀ *ᵥ (b - A *ᵥ x₀)) q) x

omit [DecidableEq n] in
/-- `(Aᵀ A y) ⬝ y = ‖A y‖²`: the quadratic form of the normal-equations matrix.
Helper for `cgls-lsqr-bound` (belongs in `NLAlib.Matrix.QuadForm`). -/
theorem quadForm_transpose_mul_self (A : Matrix m n ℝ) (y : n → ℝ) :
    quadForm (Aᵀ * A) y = (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
  rw [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

omit [DecidableEq n] in
/-- The least-squares objective is twice the CG objective of the normal equations plus a
constant: `‖b − Ay‖² = 2 φ_{AᵀA, Aᵀb}(y) + ‖b‖²`. Source: Saad (2003) [`saad03`], §8.3.
Helper for `cgls-lsqr-bound`. -/
theorem dotProduct_sub_mulVec_self_eq (A : Matrix m n ℝ) (b : m → ℝ) (y : n → ℝ) :
    (b - A *ᵥ y) ⬝ᵥ (b - A *ᵥ y) = 2 * cgObjective (Aᵀ * A) (Aᵀ *ᵥ b) y + b ⬝ᵥ b := by
  rw [cgObjective, quadForm_transpose_mul_self, Matrix.mulVec_transpose,
    ← Matrix.dotProduct_mulVec]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm (A *ᵥ y) b]
  ring

/-- **CGLS is CG on the normal equations.** `x` is a CGLS iterate for `min ‖b − Ax‖` iff it is
a CG iterate for `AᵀA x = Aᵀb` (same starting point, same Krylov space). Source: Saad (2003)
[`saad03`], §8.3 (CGNR).
atlas: cgls-lsqr-bound (partial) -/
theorem isCGLSIterate_iff_isCGIterate {A : Matrix m n ℝ} {b : m → ℝ} {x₀ x : n → ℝ} {q : ℕ} :
    IsCGLSIterate A b x₀ q x ↔ IsCGIterate (Aᵀ * A) (Aᵀ *ᵥ b) x₀ q x := by
  have hr : Aᵀ *ᵥ b - (Aᵀ * A) *ᵥ x₀ = Aᵀ *ᵥ (b - A *ᵥ x₀) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  rw [IsCGLSIterate, IsCGIterate, hr, IsAffineMinimiser, IsAffineMinimiser]
  refine and_congr_right fun _ => forall₂_congr fun y _ => ?_
  rw [dotProduct_sub_mulVec_self_eq, dotProduct_sub_mulVec_self_eq]
  constructor <;> intro h <;> linarith

omit [DecidableEq n] in
/-- **Residual splitting for least squares.** If `x⋆` solves the normal equations
`AᵀA x⋆ = Aᵀb`, then `‖b − Ax‖² = ‖b − Ax⋆‖² + ‖A(x − x⋆)‖²` for every `x`.
Source: Saad (2003) [`saad03`], §8.3; Trefethen–Bau (1997) [`tb97`], Thm 11.1.
atlas: cgls-lsqr-bound (partial) -/
theorem dotProduct_sub_mulVec_self_eq_add {A : Matrix m n ℝ} {b : m → ℝ} {xs : n → ℝ}
    (hxs : Aᵀ *ᵥ (A *ᵥ xs) = Aᵀ *ᵥ b) (x : n → ℝ) :
    (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) =
      (b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs) + (A *ᵥ (x - xs)) ⬝ᵥ (A *ᵥ (x - xs)) := by
  have hcross : (b - A *ᵥ xs) ⬝ᵥ (A *ᵥ (x - xs)) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_sub, hxs, sub_self,
      zero_dotProduct]
  have hsplit : b - A *ᵥ x = (b - A *ᵥ xs) - A *ᵥ (x - xs) := by
    rw [Matrix.mulVec_sub]; abel
  rw [hsplit]
  generalize b - A *ᵥ xs = u at hcross ⊢
  generalize A *ᵥ (x - xs) = w at hcross ⊢
  have h : (u - w) ⬝ᵥ (u - w) = u ⬝ᵥ u - 2 * (u ⬝ᵥ w) + w ⬝ᵥ w := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm w u]; ring
  rw [h, hcross]; ring

/-- **CGLS/LSQR convergence, `κ(A)` rate.** Let `A : ℝ^{m×n}` have all singular values in
`[σ_lo, σ_hi]`, `0 < σ_lo ≤ σ_hi`, stated as `σ_lo² ‖v‖² ≤ ‖Av‖² ≤ σ_hi² ‖v‖²` for all `v` (so `A`
has full column rank), let `x⋆` solve the normal equations `AᵀA x⋆ = Aᵀb`, and `x` be a `q`-th
CGLS iterate from `x₀`. Then
`‖A(x − x⋆)‖² ≤ (2((σ_hi − σ_lo)/(σ_hi + σ_lo))^q)² ‖A(x₀ − x⋆)‖²`.
Proof: CG on `AᵀA` with spectrum in `[σ_lo², σ_hi²]` (`quadForm_sub_le_of_isCGIterate_of_le`).
Source: Saad (2003) [`saad03`], §8.3; Paige–Saunders (1982) [`ps82`].
Deviation: squared norms; the singular-value hypothesis in Rayleigh form.
atlas: cgls-lsqr-bound -/
theorem dotProduct_mulVec_sub_le_of_isCGLSIterate {A : Matrix m n ℝ} {σlo σhi : ℝ}
    (hlo : 0 < σlo) (hlohi : σlo ≤ σhi)
    (hlow : ∀ v, σlo ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (hup : ∀ v, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ σhi ^ 2 * (v ⬝ᵥ v)) {b : m → ℝ} {x₀ xs x : n → ℝ}
    (hxs : Aᵀ *ᵥ (A *ᵥ xs) = Aᵀ *ᵥ b) {q : ℕ} (hx : IsCGLSIterate A b x₀ q x) :
    (A *ᵥ (x - xs)) ⬝ᵥ (A *ᵥ (x - xs)) ≤
      (2 * ((σhi - σlo) / (σhi + σlo)) ^ q) ^ 2 * ((A *ᵥ (x₀ - xs)) ⬝ᵥ (A *ᵥ (x₀ - xs))) := by
  have hG : (Aᵀ * A).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  have hspec : ∀ i, hG.eigenvalues i ∈ Set.Icc (σlo ^ 2) (σhi ^ 2) := fun i => by
    set u : n → ℝ := (hG.eigenvectorBasis i : n → ℝ)
    have hu : u ⬝ᵥ u = 1 := eigenvectorBasis_dotProduct_self hG i
    have hval : hG.eigenvalues i = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      rw [eigenvalues_eq_dotProduct_mulVec hG i, ← quadForm_transpose_mul_self]; rfl
    have h1 := hlow u
    have h2 := hup u
    rw [hu, mul_one] at h1 h2
    exact ⟨hval ▸ h1, hval ▸ h2⟩
  have hxs' : (Aᵀ * A) *ᵥ xs = Aᵀ *ᵥ b := by rw [← Matrix.mulVec_mulVec, hxs]
  have h := quadForm_sub_le_of_isCGIterate_of_le hG (by positivity)
    (pow_le_pow_left₀ hlo.le hlohi 2) hspec hxs' (isCGLSIterate_iff_isCGIterate.1 hx)
  rwa [Real.sqrt_sq (by linarith), Real.sqrt_sq hlo.le, quadForm_transpose_mul_self,
    quadForm_transpose_mul_self] at h

/-- **CGLS/LSQR residual bound.** Under the hypotheses of
`dotProduct_mulVec_sub_le_of_isCGLSIterate`,
`‖b − Ax‖² ≤ ‖b − Ax⋆‖² + (2((σ_hi − σ_lo)/(σ_hi + σ_lo))^q)² ‖A(x₀ − x⋆)‖²`.
Source: Saad (2003) [`saad03`], §8.3.
atlas: cgls-lsqr-bound -/
theorem dotProduct_sub_mulVec_le_of_isCGLSIterate {A : Matrix m n ℝ} {σlo σhi : ℝ}
    (hlo : 0 < σlo) (hlohi : σlo ≤ σhi)
    (hlow : ∀ v, σlo ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (hup : ∀ v, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ σhi ^ 2 * (v ⬝ᵥ v)) {b : m → ℝ} {x₀ xs x : n → ℝ}
    (hxs : Aᵀ *ᵥ (A *ᵥ xs) = Aᵀ *ᵥ b) {q : ℕ} (hx : IsCGLSIterate A b x₀ q x) :
    (b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) ≤ (b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs) +
      (2 * ((σhi - σlo) / (σhi + σlo)) ^ q) ^ 2 * ((A *ᵥ (x₀ - xs)) ⬝ᵥ (A *ᵥ (x₀ - xs))) := by
  rw [dotProduct_sub_mulVec_self_eq_add hxs x]
  linarith [dotProduct_mulVec_sub_le_of_isCGLSIterate hlo hlohi hlow hup hxs hx]

end NLAlib
