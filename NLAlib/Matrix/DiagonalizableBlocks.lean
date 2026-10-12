import NLAlib.Matrix.Diagonalizable
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Direct sums and changes of eigenvector bases

Diagonalizability descends through a surjective intertwiner and therefore
passes to both summands of a direct sum. With an aligned eigenvalue list,
changes of eigenvector bases vanish between different eigenspaces.
Source: Horn–Johnson (2013), Lemma 1.3.10 and Theorem 1.3.27.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {K : Type*} [Field K]

/-- A surjective intertwiner sends a diagonalizable endomorphism to a
diagonalizable endomorphism. Source: Horn–Johnson (2013), Lemma 1.3.10;
the proof maps the spanning eigenspaces. -/
theorem IsDiagonalizable.of_surjective_intertwiner {A : Matrix m m K}
    {B : Matrix n n K} (hB : IsDiagonalizable B)
    (T : (n → K) →ₗ[K] (m → K)) (hT : Function.Surjective T)
    (hcomm : ∀ x, T (B *ᵥ x) = A *ᵥ T x) : IsDiagonalizable A := by
  apply (isDiagonalizable_iff_iSup_eigenspace_eq_top A).mpr
  apply top_le_iff.mp
  have hmap (μ : K) : (Module.End.eigenspace B.toLin' μ).map T ≤
      Module.End.eigenspace A.toLin' μ := by
    rintro _ ⟨x, hx, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change A *ᵥ T x = μ • T x
    have hx' : B *ᵥ x = μ • x := Module.End.mem_eigenspace_iff.mp hx
    rw [← hcomm, hx', map_smul]
  calc
    ⊤ = (⊤ : Submodule K (n → K)).map T := by
      rw [Submodule.map_top, LinearMap.range_eq_top.mpr hT]
    _ = (⨆ μ : K, Module.End.eigenspace B.toLin' μ).map T := by
      rw [(isDiagonalizable_iff_iSup_eigenspace_eq_top B).mp hB]
    _ = ⨆ μ : K, (Module.End.eigenspace B.toLin' μ).map T := Submodule.map_iSup _ _
    _ ≤ ⨆ μ : K, Module.End.eigenspace A.toLin' μ := iSup_mono hmap

/-- A direct sum is diagonalizable exactly when both summands are.
Source: Horn–Johnson (2013), Lemma 1.3.10; arbitrary finite and empty shapes
are allowed, and the theorem holds over every field.
atlas: diagonalizable-def (partial) -/
theorem isDiagonalizable_fromBlocks_zero_zero_iff (A : Matrix m m K) (B : Matrix n n K) :
    IsDiagonalizable (Matrix.fromBlocks A 0 0 B) ↔ IsDiagonalizable A ∧ IsDiagonalizable B := by
  classical
  constructor
  · intro h
    let T₁ : ((m ⊕ n) → K) →ₗ[K] (m → K) :=
      { toFun x := fun i => x (Sum.inl i)
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    let T₂ : ((m ⊕ n) → K) →ₗ[K] (n → K) :=
      { toFun x := fun i => x (Sum.inr i)
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    constructor
    · apply h.of_surjective_intertwiner T₁ (fun x => ⟨Sum.elim x 0, rfl⟩)
      intro x
      ext i
      simp [T₁, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]
    · apply h.of_surjective_intertwiner T₂ (fun x => ⟨Sum.elim 0 x, rfl⟩)
      intro x
      ext i
      simp [T₂, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]
  · rintro ⟨⟨V, d, hV, hAV⟩, ⟨W, e, hW, hBW⟩⟩
    refine ⟨Matrix.fromBlocks V 0 0 W, Sum.elim d e, ?_, ?_⟩
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
      exact (Matrix.isUnit_iff_isUnit_det V).mp hV |>.mul
        ((Matrix.isUnit_iff_isUnit_det W).mp hW)
    · rw [← Matrix.fromBlocks_diagonal]
      simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        zero_add, add_zero, hAV, hBW]

/-- The change of two diagonalizing eigenvector bases with an aligned
eigenvalue list commutes with that diagonal matrix. Source:
Horn–Johnson (2013), Theorem 1.3.27.
atlas: diagonalizable-def (partial) -/
theorem diagonal_mul_change_eigenbasis_eq_change_eigenbasis_mul_diagonal
    {A V W : Matrix n n K} {d : n → K} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hAW : A * W = W * Matrix.diagonal d) :
    Matrix.diagonal d * (V⁻¹ * W) = (V⁻¹ * W) * Matrix.diagonal d := by
  apply hV.mul_left_cancel
  change V * (Matrix.diagonal d * (V⁻¹ * W)) = V * ((V⁻¹ * W) * Matrix.diagonal d)
  rw [← Matrix.mul_assoc V (Matrix.diagonal d), ← hAV,
    Matrix.mul_assoc A V, ← Matrix.mul_assoc V V⁻¹,
    Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.one_mul,
    ← Matrix.mul_assoc V, ← Matrix.mul_assoc V V⁻¹,
    Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.one_mul]
  exact hAW

/-- An aligned change of eigenvector basis vanishes between distinct
eigenvalues, so it is block diagonal on the repeated eigenspaces. Source:
Horn–Johnson (2013), Theorem 1.3.27; the vanishing itself needs only the first
eigenvector matrix to be invertible.
atlas: diagonalizable-def (partial) -/
theorem change_eigenbasis_apply_eq_zero_of_eigenvalues_ne
    {A V W : Matrix n n K} {d : n → K} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hAW : A * W = W * Matrix.diagonal d)
    {i j : n} (hij : d i ≠ d j) : (V⁻¹ * W) i j = 0 := by
  have h := congrArg (fun M : Matrix n n K => M i j)
    (diagonal_mul_change_eigenbasis_eq_change_eigenbasis_mul_diagonal hV hAV hAW)
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  exact (mul_eq_zero.mp (by linear_combination h : (d i - d j) * (V⁻¹ * W) i j = 0)).resolve_left
    (sub_ne_zero.mpr hij)

/-- The invertible change of two aligned diagonalizations is block diagonal
on equal-eigenvalue coordinate classes. Source: Horn–Johnson (2013),
Theorem 1.3.27.
atlas: diagonalizable-def (partial) -/
theorem isUnit_change_eigenbasis_and_apply_eq_zero
    {A V W : Matrix n n K} {d : n → K} (hV : IsUnit V) (hW : IsUnit W)
    (hAV : A * V = V * Matrix.diagonal d) (hAW : A * W = W * Matrix.diagonal d) :
    IsUnit (V⁻¹ * W) ∧ ∀ i j, d i ≠ d j → (V⁻¹ * W) i j = 0 :=
  ⟨(Matrix.isUnit_nonsing_inv_iff.mpr hV).mul hW,
    fun _ _ hij => change_eigenbasis_apply_eq_zero_of_eigenvalues_ne hV hAV hAW hij⟩

end NLAlib
