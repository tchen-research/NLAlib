import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

/-!
# Complementary right nullities

An invertible map on split coordinates identifies the upper-left kernel with
the lower-right kernel of its inverse. This gives the rectangular law with
its right-nullity orientation and no equal-cardinality premise.
Horn–Johnson 2013, §§0.7.5–0.7.6; atlas `complementary-nullities`.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def firstBlockMap {R E F G H : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (f : (E × F) ≃ₗ[R] (G × H)) : E →ₗ[R] G :=
  (LinearMap.fst R G H).comp (f.toLinearMap.comp (LinearMap.inl R E F))

private def inverseLastBlockMap {R E F G H : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (f : (E × F) ≃ₗ[R] (G × H)) : H →ₗ[R] F :=
  (LinearMap.snd R E F).comp (f.symm.toLinearMap.comp (LinearMap.inr R G H))

private def complementaryKernelEquiv {R E F G H : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (f : (E × F) ≃ₗ[R] (G × H)) :
    LinearMap.ker (firstBlockMap f) ≃ₗ[R] LinearMap.ker (inverseLastBlockMap f) where
  toFun x := ⟨(f (x.val, 0)).2, by
    change (f.symm (0, (f (x.val, 0)).2)).2 = 0
    have hx : (f (x.val, 0)).1 = 0 := x.property
    have hPair : f (x.val, 0) = (0, (f (x.val, 0)).2) := Prod.ext hx rfl
    have h := congrArg (fun y => (f.symm y).2) hPair
    simpa only [LinearEquiv.symm_apply_apply] using h.symm⟩
  invFun y := ⟨(f.symm (0, y.val)).1, by
    change (f ((f.symm (0, y.val)).1, 0)).1 = 0
    have hy : (f.symm (0, y.val)).2 = 0 := y.property
    have hPair : f.symm (0, y.val) = ((f.symm (0, y.val)).1, 0) := Prod.ext rfl hy
    have h := congrArg (fun x => (f x).1) hPair
    simpa only [LinearEquiv.apply_symm_apply] using h.symm⟩
  left_inv x := by
    apply Subtype.ext
    have hx : (f (x.val, 0)).1 = 0 := x.property
    have hPair : (0, (f (x.val, 0)).2) = f (x.val, 0) := Prod.ext hx.symm rfl
    simp only [hPair, LinearEquiv.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    have hy : (f.symm (0, y.val)).2 = 0 := y.property
    have hPair : ((f.symm (0, y.val)).1, 0) = f.symm (0, y.val) := Prod.ext rfl hy.symm
    simp only [hPair, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Subtype.ext
    change (f (x.val + y.val, 0)).2 = (f (x.val, 0)).2 + (f (y.val, 0)).2
    rw [show (x.val + y.val, (0 : F)) = (x.val, 0) + (y.val, 0) by simp, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change (f (c • x.val, 0)).2 = c • (f (x.val, 0)).2
    rw [show (c • x.val, (0 : F)) = c • (x.val, 0) by simp, map_smul]
    rfl

private def coordinateSplit {n : Type*} (p : n → Prop) [DecidablePred p] :
    (n → ℝ) ≃ₗ[ℝ] (({i // p i} → ℝ) × ({i // ¬p i} → ℝ)) where
  toFun x := (fun i => x i.val, fun i => x i.val)
  invFun x := fun i => if h : p i then x.1 ⟨i, h⟩ else x.2 ⟨i, h⟩
  left_inv x := by funext i; dsimp; split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [i.property]
  map_add' x y := rfl
  map_smul' c x := rfl

private theorem firstBlockMap_coordinateSplit {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A.det) (p q : n → Prop)
    [DecidablePred p] [DecidablePred q] :
    firstBlockMap ((coordinateSplit q).symm.trans
      ((A.toLinearEquiv (Pi.basisFun ℝ n) hA).trans (coordinateSplit p))) =
      (A.toBlock p q).mulVecLin := by
  apply LinearMap.ext
  intro x
  funext i
  change (∑ j : n, A i.val j * (if h : q j then x ⟨j, h⟩ else 0)) =
    ∑ j : {j // q j}, A i.val j.val * x j
  have h := Fintype.sum_subtype_add_sum_subtype q
    (fun j => A i.val j * (if h : q j then x ⟨j, h⟩ else 0))
  have hPos : (fun j : {j // q j} => A i.val j.val *
      (if h : q j.val then x ⟨j.val, h⟩ else 0)) = fun j => A i.val j.val * x j := by
    funext j; rw [dif_pos j.property]
  have hNeg : (fun j : {j // ¬q j} => A i.val j.val *
      (if h : q j.val then x ⟨j.val, h⟩ else 0)) = fun _ => (0 : ℝ) := by
    funext j; rw [dif_neg j.property, mul_zero]
  rw [hPos, hNeg, Finset.sum_const_zero, add_zero] at h
  exact h.symm

/-- Rectangular complementary submatrices of an invertible matrix have the
same right nullity. No equal-size condition is required: the inverse minor's
rows complement the original columns and its columns complement the original
rows. Horn–Johnson 2013, §§0.7.5–0.7.6.
atlas: complementary-nullities (partial) -/
theorem finrank_ker_toBlock_eq_finrank_ker_inverse_complement {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : IsUnit A.det)
    (p q : n → Prop) [DecidablePred p] [DecidablePred q] :
    Module.finrank ℝ (LinearMap.ker (A.toBlock p q).mulVecLin) =
      Module.finrank ℝ (LinearMap.ker (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).mulVecLin) := by
  let f := (coordinateSplit q).symm.trans
    ((A.toLinearEquiv (Pi.basisFun ℝ n) hA).trans (coordinateSplit p))
  have hFirst := firstBlockMap_coordinateSplit A hA p q
  have hLast : inverseLastBlockMap f =
      (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).mulVecLin := by
    apply LinearMap.ext
    intro y
    funext i
    change (∑ j : n, A⁻¹ i.val j * (if h : p j then 0 else y ⟨j, h⟩)) =
      ∑ j : {j // ¬p j}, A⁻¹ i.val j.val * y j
    have h := Fintype.sum_subtype_add_sum_subtype p
      (fun j => A⁻¹ i.val j * (if h : p j then 0 else y ⟨j, h⟩))
    have hPos : (fun j : {j // p j} => A⁻¹ i.val j.val *
        (if h : p j.val then 0 else y ⟨j.val, h⟩)) = fun _ => (0 : ℝ) := by
      funext j; rw [dif_pos j.property, mul_zero]
    have hNeg : (fun j : {j // ¬p j} => A⁻¹ i.val j.val *
        (if h : p j.val then 0 else y ⟨j.val, h⟩)) = fun j => A⁻¹ i.val j.val * y j := by
      funext j; rw [dif_neg j.property]
    rw [hPos, hNeg, Finset.sum_const_zero, zero_add] at h
    exact h.symm
  have h := (complementaryKernelEquiv f).finrank_eq
  rwa [hFirst, hLast] at h

end NLAlib
