import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.RCLike.Basic

/-!
# Density of matrices with distinct complex characteristic roots

Along an affine pencil ending at a matrix with separable characteristic
polynomial, nonseparability occurs at only finitely many scalar parameters.
The resultant with the derivative supplies the exceptional polynomial.
Source: Horn–Johnson (2013), §2.3.
-/

noncomputable section
open Polynomial
open scoped Matrix Topology

namespace NLAlib

/-- An affine matrix pencil ending at a separable characteristic polynomial
has only finitely many nonseparable parameters. Source: Horn–Johnson (2013),
§2.3; the resultant of the characteristic polynomial and its derivative
is a nonzero scalar-parameter polynomial. -/
theorem finite_not_separable_charpoly_affine
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [CharZero K]
    (A D : Matrix n n K) (hD : D.charpoly.Separable) :
    Set.Finite {t : K | ¬ (A + t • (D - A)).charpoly.Separable} := by
  classical
  let M : Matrix n n K[X] := A.map (C : K → K[X]) + (X : K[X]) • (D - A).map (C : K → K[X])
  let P := M.charpoly
  let r : K[X] := P.resultant P.derivative (Fintype.card n) (Fintype.card n - 1)
  have hmap (t : K) : P.map (Polynomial.evalRingHom t) = (A + t • (D - A)).charpoly := by
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j
    simp [M, Matrix.map_apply]
  have heval (t : K) : r.eval t =
      (A + t • (D - A)).charpoly.resultant (A + t • (D - A)).charpoly.derivative := by
    have h := Polynomial.resultant_map_map P P.derivative
      (Fintype.card n) (Fintype.card n - 1) (Polynomial.evalRingHom t)
    rw [← Polynomial.derivative_map, hmap] at h
    simpa only [r, Polynomial.coe_evalRingHom, Polynomial.natDegree_derivative,
      Matrix.charpoly_natDegree_eq_dim] using h.symm
  have hsep (t : K) : (A + t • (D - A)).charpoly.Separable ↔ r.eval t ≠ 0 := by
    rw [heval, Polynomial.separable_def,
      ← Polynomial.isUnit_resultant_iff_isCoprime (A + t • (D - A)).charpoly_monic,
      isUnit_iff_ne_zero]
  have hr1 : r.eval 1 ≠ 0 := (hsep 1).mp (by simpa using hD)
  have hr : r ≠ 0 := by intro hzero; simp [hzero] at hr1
  apply (Polynomial.finite_setOfPred_isRoot hr).subset
  intro t ht
  exact not_ne_iff.mp ((hsep t).not.mp ht)

/-- Over the real or complex field, matrices with separable characteristic
polynomial are dense. For real matrices separability means distinct complex
roots after complexification. Source: Horn–Johnson (2013), §2.3; every finite
shape, including the empty shape, is included.
atlas: schur-triangularization (partial) -/
theorem dense_separable_charpoly
    {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K] :
    Dense {A : Matrix n n K | A.charpoly.Separable} := by
  classical
  let d : n → K := fun i => ((Fintype.equivFin n i).val : K)
  have hd : Function.Injective d := by
    intro i j hij
    apply (Fintype.equivFin n).injective
    apply Fin.ext
    dsimp [d] at hij
    exact_mod_cast hij
  let D := Matrix.diagonal d
  have hD : D.charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr hd
  intro A
  apply mem_closure_iff.mpr
  intro U hU hAU
  let g : K → Matrix n n K := fun t => A + t • (D - A)
  have hg : Continuous g := by fun_prop
  have hpre : g ⁻¹' U ∈ nhds (0 : K) :=
    (hg.continuousAt (x := 0)).preimage_mem_nhds (hU.mem_nhds (by simpa [g] using hAU))
  obtain ⟨t, ht, hgood⟩ := (infinite_of_mem_nhds (0 : K) hpre).exists_notMem_finite
    (finite_not_separable_charpoly_affine A D hD)
  exact ⟨g t, ht, not_not.mp hgood⟩

end NLAlib
