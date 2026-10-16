import NLAlib.Matrix.Basic.KernelFrame
import NLAlib.Matrix.Basic.QuadraticMinimization
import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-!+# Null-space solution of saddle-point systems

The reduced Hessian characterizes nonsingularity even when the ambient
Hermitian Hessian is indefinite. The multiplier is recovered by the
ordinary inverse of the full-row-rank constraint Gram matrix.

Source: Benzi–Golub–Liesen (2005), §§3.3, 6; re-derivation §39.
Atlas: `kkt-reduced-hessian`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- The equality-constrained Hermitian saddle-point matrix. -/
def kktMatrix (H : Matrix n n 𝕜) (B : Matrix m n 𝕜) : Matrix (n ⊕ m) (n ⊕ m) 𝕜 :=
  Matrix.fromBlocks H Bᴴ B 0

/-- The Hessian in orthonormal null-space coordinates. -/
def reducedHessian (H : Matrix n n 𝕜) (Z : Matrix n r 𝕜) : Matrix r r 𝕜 := Zᴴ * H * Z

/-- The explicit null-space solver and multiplier formula satisfy both KKT
equations whenever their reduced equation is satisfied.
atlas: kkt-reduced-hessian (partial) -/
theorem IsKernelFrame.kkt_solution {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}
    (hZ : IsKernelFrame B Z) (hB : IsUnit (B * Bᴴ)) (H : Matrix n n 𝕜)
    (f : n → 𝕜) (g : m → 𝕜) (xp : n → 𝕜) (hxp : B *ᵥ xp = g)
    (y : r → 𝕜) (hy : reducedHessian H Z *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp)) :
    let x := xp + Z *ᵥ y
    let l := (B * Bᴴ)⁻¹ *ᵥ (B *ᵥ (f - H *ᵥ x))
    B *ᵥ x = g ∧ H *ᵥ x + Bᴴ *ᵥ l = f := by
  dsimp only
  have hx : B *ᵥ (xp + Z *ᵥ y) = g := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hZ.mul_eq_zero, Matrix.zero_mulVec,
      add_zero, hxp]
  refine ⟨hx, ?_⟩
  have hz : Zᴴ *ᵥ (f - H *ᵥ (xp + Z *ᵥ y)) = 0 := by
    simp only [reducedHessian, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub] at hy
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_add]
    linear_combination -hy
  have he := hZ.eq_conjTranspose_mulVec_of_conjTranspose_mulVec_eq_zero hB hz
  linear_combination -he

/-- The reduced equation obtained by applying null-space coordinates to
the first KKT equation. -/
theorem IsKernelFrame.reduced_equation {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}
    (hZ : IsKernelFrame B Z) (H : Matrix n n 𝕜) (f xp : n → 𝕜)
    (y : r → 𝕜) (l : m → 𝕜)
    (he : H *ᵥ (xp + Z *ᵥ y) + Bᴴ *ᵥ l = f) :
    reducedHessian H Z *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp) := by
  have hz : Zᴴ * Bᴴ = 0 := by
    rw [← Matrix.conjTranspose_mul, hZ.mul_eq_zero, Matrix.conjTranspose_zero]
  have hh := congrArg (fun v => Zᴴ *ᵥ v) he
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec l Zᴴ Bᴴ, hz,
    Matrix.zero_mulVec, add_zero] at hh
  simp only [reducedHessian, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  linear_combination hh

/-- The full saddle-point matrix is nonsingular exactly when its reduced
Hessian is nonsingular. No definiteness of the ambient Hessian is required.
atlas: kkt-reduced-hessian (partial) -/
theorem IsKernelFrame.isUnit_kktMatrix_iff {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}
    (hZ : IsKernelFrame B Z) (hB : IsUnit (B * Bᴴ)) (H : Matrix n n 𝕜) :
    IsUnit (kktMatrix H B) ↔ IsUnit (reducedHessian H Z) := by
  rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.mulVec_injective_iff_isUnit]
  change Function.Injective (kktMatrix H B).mulVecLin ↔
    Function.Injective (reducedHessian H Z).mulVecLin
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot]
  change LinearMap.ker (kktMatrix H B).mulVecLin = ⊥ ↔
    LinearMap.ker (reducedHessian H Z).mulVecLin = ⊥
  rw [LinearMap.ker_eq_bot', LinearMap.ker_eq_bot']
  constructor
  · intro h y hy
    change reducedHessian H Z *ᵥ y = 0 at hy
    have he := hZ.kkt_solution hB H 0 0 0 (by simp) y (by simpa using hy)
    simp only [zero_add] at he
    let l := (B * Bᴴ)⁻¹ *ᵥ (B *ᵥ (0 - H *ᵥ (Z *ᵥ y)))
    have hv : kktMatrix H B *ᵥ Sum.elim (Z *ᵥ y) l = 0 := by
      rw [kktMatrix, Matrix.fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        Matrix.zero_mulVec, add_zero]
      ext i
      cases i with
      | inl i => exact congrFun he.2 i
      | inr i => exact congrFun he.1 i
    have hz := congrArg (fun v => Zᴴ *ᵥ (v ∘ Sum.inl)) (h _ hv)
    change Zᴴ *ᵥ (Z *ᵥ y) = Zᴴ *ᵥ (0 : n → 𝕜) at hz
    simpa only [Matrix.mulVec_mulVec, hZ.orth.conjTranspose_mul_self,
      Matrix.one_mulVec, Matrix.mulVec_zero] using hz
  · intro h v hv
    change kktMatrix H B *ᵥ v = 0 at hv
    have htop : H *ᵥ (v ∘ Sum.inl) + Bᴴ *ᵥ (v ∘ Sum.inr) = 0 := by
      ext i
      simpa only [kktMatrix, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.zero_apply]
        using congrFun hv (Sum.inl i)
    have hbot : B *ᵥ (v ∘ Sum.inl) = 0 := by
      ext i
      simpa only [kktMatrix, Matrix.fromBlocks_mulVec, Sum.elim_inr,
        Matrix.zero_mulVec, add_zero, Pi.zero_apply] using congrFun hv (Sum.inr i)
    have hcoord := hZ.mulVec_conjTranspose_mulVec hbot
    have hred : reducedHessian H Z *ᵥ (Zᴴ *ᵥ (v ∘ Sum.inl)) = 0 := by
      have he := hZ.reduced_equation H 0 0 (Zᴴ *ᵥ (v ∘ Sum.inl)) (v ∘ Sum.inr)
      apply (by simpa only [Matrix.mulVec_zero, sub_zero] using he)
      simpa only [zero_add, hcoord] using htop
    have hx : v ∘ Sum.inl = 0 := by
      have hh := h _ hred
      rw [hh, Matrix.mulVec_zero] at hcoord
      exact hcoord.symm
    have hl : v ∘ Sum.inr = 0 := by
      rw [hx, Matrix.mulVec_zero, zero_add] at htop
      have hh := congrArg (fun w => B *ᵥ w) htop
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hh
      exact Matrix.mulVec_injective_iff_isUnit.mpr hB (by simpa using hh)
    ext i
    cases i with
    | inl i => exact congrFun hx i
    | inr i => exact congrFun hl i

end NLAlib
