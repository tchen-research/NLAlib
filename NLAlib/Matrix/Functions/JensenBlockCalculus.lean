import NLAlib.Matrix.Functions.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Functional calculus and spectrum of a block-diagonal Hermitian matrix

Main declaration: `NLAlib.cfc_fromBlocks`.

Atlas: `operator-monotone-convex` (step of the operator Jensen inequality).

Source: Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, proof of Theorem 8.5.2, printed pp. 132–133 (PDF pp. 138–139), block-diagonal functional-calculus identities.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open NLAlib

private def blockHom
    {𝕜 : Type*} [RCLike 𝕜]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] :
    (Matrix ι ι 𝕜 × Matrix κ κ 𝕜) →⋆ₐ[𝕜] Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜 where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  map_zero' := Matrix.fromBlocks_zero
  map_add' p q := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  commutes' r := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.algebraMap_eq_diagonal, Matrix.fromBlocks, Matrix.diagonal]
  map_star' p := by simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

private theorem cfc_eq_aeval_interpolate_on_finset
    {𝕜 τ : Type*} [RCLike 𝕜] [Fintype τ] [DecidableEq τ]
    (M : Matrix τ τ 𝕜) (hM : M.IsHermitian) (s : Finset ℝ) (f : ℝ → ℝ)
    (hm : spectrum ℝ M ⊆ (s : Set ℝ)) :
    cfc f M = Polynomial.aeval M (Lagrange.interpolate s id f) := by
  classical
  rw [← cfc_polynomial _ M hM]
  exact cfc_congr fun x hx => (Lagrange.eval_interpolate_at_node
    (v := id) f (Set.injOn_id _) (hm hx)).symm

/-- A block-diagonal matrix of Hermitian blocks is Hermitian, its spectrum is the union of the block
spectra, and the functional calculus acts blockwise.

Tropp 2015, proof of Thm 8.5.2. Atlas: `operator-monotone-convex`. Ported from the Prove2me
mission *An Introduction to Matrix Concentration Inequalities, Ch 8*.

Auxiliary; not a numbered result in the source. -/
theorem NLAlib.cfc_fromBlocks
    {𝕜 : Type*} [RCLike 𝕜]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι ι 𝕜) (B : Matrix κ κ 𝕜)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.fromBlocks A 0 0 B).IsHermitian ∧
    spectrum ℝ (Matrix.fromBlocks A 0 0 B) = spectrum ℝ A ∪ spectrum ℝ B ∧
    cfc f (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) := by
  have hblock := hA.fromBlocks (B := (0 : Matrix ι κ 𝕜)) (C := 0) (by simp) hB
  have hspec : spectrum ℝ (Matrix.fromBlocks A 0 0 B) = spectrum ℝ A ∪ spectrum ℝ B := by
    ext r
    have heq : algebraMap ℝ (Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜) r -
        Matrix.fromBlocks A 0 0 B =
        Matrix.fromBlocks (algebraMap ℝ (Matrix ι ι 𝕜) r - A) 0 0
          (algebraMap ℝ (Matrix κ κ 𝕜) r - B) := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.algebraMap_eq_diagonal, Matrix.fromBlocks, Matrix.diagonal]
    simp only [Set.mem_union, spectrum.mem_iff, heq, Matrix.isUnit_iff_isUnit_det,
      Matrix.det_fromBlocks_zero₂₁, isUnit_iff_ne_zero, mul_ne_zero_iff, not_and_or]
  refine ⟨hblock, hspec, ?_⟩
  classical
  let s := Finset.univ.image hA.eigenvalues ∪ Finset.univ.image hB.eigenvalues
  let p := Lagrange.interpolate s id f
  have hs : spectrum ℝ A ∪ spectrum ℝ B = (s : Set ℝ) := by
    simp only [s, Finset.coe_union, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, hA.spectrum_real_eq_range_eigenvalues,
      hB.spectrum_real_eq_range_eigenvalues]
  rw [cfc_eq_aeval_interpolate_on_finset _ hblock s f (by rw [hspec, hs]),
    cfc_eq_aeval_interpolate_on_finset A hA s f (by rw [← hs]; exact Set.subset_union_left),
    cfc_eq_aeval_interpolate_on_finset B hB s f (by rw [← hs]; exact Set.subset_union_right)]
  have hp := Polynomial.aeval_algHom_apply
    ((blockHom (𝕜 := 𝕜) (ι := ι) (κ := κ)).toAlgHom.restrictScalars ℝ) (A, B) p
  rw [Polynomial.aeval_prod_apply] at hp
  exact hp
