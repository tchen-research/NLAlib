import NLAlib.Matrix.EigenvectorPairing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Nonunitary left–right eigenvector deflation

An eigenvector with nonzero left pairing is complemented by the kernel of
the left row. The resulting basis isolates its invariant line on both sides,
and its dual row gives the oblique rank-one projector.
Source: Horn–Johnson (2013), Theorem 1.4.7; atlas `left-right-eigenvectors`.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Paired right and left eigenvectors admit a basis isolating their common
eigenvalue on one coordinate, with the exact normalized dual row and oblique
projector. Source: Horn–Johnson (2013), Theorem 1.4.7; the distinguished
coordinate may be relabeled as the first coordinate. For complex columns
`y₀`, take the left row `y = star y₀`; conjugating the displayed inverse row
gives the source's inverse-adjoint column `y₀/(x* y₀)`.
atlas: left-right-eigenvectors (partial) -/
theorem exists_isolated_eigenvector_similarity {A : Matrix n n K} {x y : n → K} {μ : K}
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y) (hpair : y ⬝ᵥ x ≠ 0) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y =
        S * Matrix.diagonal (Pi.single i 1) * S⁻¹ := by
  classical
  let ℓ : (n → K) →ₗ[K] K :=
    { toFun z := y ⬝ᵥ z
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' c z := by rw [dotProduct_smul]; rfl }
  obtain ⟨s, b, j, hx, hcoord⟩ := exists_basis_of_pairing_ne_zero (f := ℓ) (v := x) hpair
  let : Fintype s := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card s = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let e : s ≃ n := Fintype.equivOfCardEq hcard
  let c : Basis n K (n → K) := b.reindex e
  let i : n := e j
  let p := Pi.basisFun K n
  let S : Matrix n n K := p.toMatrix c
  let : Invertible S := Basis.invertibleToMatrix p c
  have hS : IsUnit S := isUnit_of_invertible S
  have hci : c i = x := by
    simpa only [c, i, Basis.reindex_apply, Equiv.symm_apply_apply] using hx.symm
  have hcol : Matrix.col S i = x := by
    funext k
    simpa only [S, p, Matrix.col_apply, Basis.toMatrix_apply, Pi.basisFun_repr] using congrFun hci k
  have hℓ : ℓ = (y ⬝ᵥ x) • c.coord i := by
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun hcoord z
    simpa only [LinearMap.smul_apply, ℓ, LinearMap.coe_mk, AddHom.coe_mk,
      Basis.coord_apply, c, i, Basis.repr_reindex_apply, Equiv.symm_apply_apply] using h
  have hSinv : S⁻¹ = c.toMatrix p :=
    Matrix.inv_eq_left_inv (Basis.toMatrix_mul_toMatrix_flip c p)
  have hrow (k : n) : S⁻¹ i k = y k / (y ⬝ᵥ x) := by
    have h := LinearMap.congr_fun hℓ (p k)
    have hval : y k = (y ⬝ᵥ x) * (c.repr (p k) i) := by
      simpa only [ℓ, p, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply, dotProduct_single,
        mul_one, LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply] using h
    rw [hSinv, Basis.toMatrix_apply]
    apply (eq_div_iff hpair).mpr
    simpa only [mul_comm] using hval.symm
  have hM : S⁻¹ * A * S = A.toLin'.toMatrix c c := by
    have hstd : A.toLin'.toMatrix p p = A := by
      simpa only [p, Matrix.toLin_eq_toLin'] using LinearMap.toMatrix_toLin p p A
    rw [hSinv]
    nth_rw 1 [← hstd]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c p c p A.toLin'
  have hright (k : n) : (S⁻¹ * A * S) k i = if k = i then μ else 0 := by
    rw [hM, LinearMap.toMatrix_apply, hci, Matrix.toLin'_apply, hAx,
      map_smul, ← hci, c.repr_self]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, eq_comm]
  have hleft (z : n → K) : c.coord i (A *ᵥ z) = μ * c.coord i z := by
    have h : ℓ (A *ᵥ z) = μ * ℓ z := by
      change y ⬝ᵥ (A *ᵥ z) = μ * (y ⬝ᵥ z)
      rw [Matrix.dotProduct_mulVec, hyA, smul_dotProduct]
      rfl
    rw [hℓ, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
    apply mul_left_cancel₀ hpair
    convert h using 1
    ring
  have htop (k : n) : (S⁻¹ * A * S) i k = if k = i then μ else 0 := by
    rw [hM, LinearMap.toMatrix_apply]
    change c.coord i (A *ᵥ c k) = _
    rw [hleft, Basis.coord_apply, c.repr_self]
    simp only [Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  refine ⟨S, i, hS, hcol, hrow, hright, htop, ?_⟩
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Pi.single_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hrow]
  have hkl : S k i = x k := congrFun hcol k
  rw [hkl]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end NLAlib
