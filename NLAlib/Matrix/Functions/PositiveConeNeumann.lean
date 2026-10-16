import NLAlib.Matrix.Norms.HermitianFrobenius
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Neumann inverses of maps preserving the Hermitian PSD cone -/
noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual geometric-series inverse of `I-L`. -/
def hermitianNeumannInverse (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n) :
    HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n := ∑' j : ℕ, L^j

omit [DecidableEq n] in
/-- The geometric series is exactly the ring inverse, with no alternate operator.
Source: user derivations (F23).
atlas: matrix-k-transform-stability (partial) -/
theorem hermitianNeumannInverse_eq_inverse
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n) (hL : ‖L‖<1) :
    hermitianNeumannInverse L = Ring.inverse (1-L) := geom_series_eq_inverse L hL

/-- The actual Neumann inverse preserves the PSD cone. -/
theorem posSemidef_hermitianNeumannInverse
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n)
    (hL : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L x)).PosSemidef)
    (hnorm : ‖L‖<1) {x : HermitianFrobenius ℂ n}
    (hx : (hermitianFrobeniusMatrix ℂ n x).PosSemidef) :
    (hermitianFrobeniusMatrix ℂ n (hermitianNeumannInverse L x)).PosSemidef := by
  let Φ := (hermitianFrobeniusMatrixLinear : HermitianFrobenius ℂ n →ₗ[ℝ] Matrix n n ℂ).toContinuousLinearMap
  have hp (j : ℕ) : (Φ ((L^j) x)).PosSemidef := by
    induction j with
    | zero =>
      change (hermitianFrobeniusMatrix ℂ n x).PosSemidef
      exact hx
    | succ j ih =>
      rw [pow_succ']
      exact hL _ ih
  have hsum := (Φ.comp (ContinuousLinearMap.apply' (HermitianFrobenius ℂ n) (RingHom.id ℝ) x)).hasSum
    (summable_geometric_of_norm_lt_one hnorm).hasSum
  have hclosed : IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
    simpa only [Set.Ici,Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix n n ℂ)))
  apply hclosed.mem_of_tendsto hsum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun j => Matrix.posSemidef_sum _ (fun i _ => hp i)

omit [DecidableEq n] in
/-- Applying the Neumann inverse solves the actual equation `(I-L)Y=X`. -/
theorem hermitianNeumannInverse_sub_map
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n) (hnorm : ‖L‖<1)
    (x : HermitianFrobenius ℂ n) :
    hermitianNeumannInverse L x - L (hermitianNeumannInverse L x) = x := by
  exact congrArg (fun A : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n => A x)
    (mul_neg_geom_series L hnorm)

/-- The canonical identity supersolution obtained by the actual Neumann
inverse dominates the identity in Loewner order. -/
theorem one_le_hermitianNeumannInverse_one
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n)
    (hL : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L x)).PosSemidef) (hnorm : ‖L‖<1) :
    let I := toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)
    (1 : Matrix n n ℂ) ≤ hermitianFrobeniusMatrix ℂ n (hermitianNeumannInverse L I) := by
  dsimp only
  let I := toHermitianFrobenius (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)
  let Y := hermitianNeumannInverse L I
  have hY := posSemidef_hermitianNeumannInverse L hL hnorm (x:=I) Matrix.PosSemidef.one
  have he := congrArg (hermitianFrobeniusMatrix ℂ n) (hermitianNeumannInverse_sub_map L hnorm I)
  change hermitianFrobeniusMatrix ℂ n Y-hermitianFrobeniusMatrix ℂ n (L Y)=1 at he
  apply Matrix.le_iff.mpr
  have hh : hermitianFrobeniusMatrix ℂ n Y-1=hermitianFrobeniusMatrix ℂ n (L Y) := by
    exact sub_eq_iff_eq_add.mpr (eq_add_of_sub_eq' he)
  rw [hh]
  exact hL Y hY

/-- Norm below one supplies an actual strictly positive supersolution.
The canonical choice is the Neumann inverse applied to the identity. -/
theorem exists_posDef_supersolution_of_norm_lt_one
    (L : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n)
    (hL : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L x)).PosSemidef)
    (hnorm : ‖L‖<1) :
    ∃ Y : HermitianFrobenius ℂ n,
      (hermitianFrobeniusMatrix ℂ n Y).PosDef ∧
      (hermitianFrobeniusMatrix ℂ n (Y-L Y)).PosDef ∧
      (1 : Matrix n n ℂ) ≤ hermitianFrobeniusMatrix ℂ n Y := by
  let I : HermitianFrobenius ℂ n :=
    (hermitianFrobeniusEquiv ℂ n).symm ⟨1,Matrix.isHermitian_one⟩
  let Y := hermitianNeumannInverse L I
  have hI : hermitianFrobeniusMatrix ℂ n I = 1 := rfl
  have hY := posSemidef_hermitianNeumannInverse L hL hnorm (x:=I)
    (hI ▸ Matrix.PosSemidef.one)
  have hEq : Y-L Y=I := by
    have h := congrArg (fun A : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n => A I)
      (mul_neg_geom_series L hnorm)
    exact h
  have hdiff : hermitianFrobeniusMatrix ℂ n Y - 1 = hermitianFrobeniusMatrix ℂ n (L Y) := by
    have h := congrArg (hermitianFrobeniusMatrix ℂ n) hEq
    change hermitianFrobeniusMatrix ℂ n Y - hermitianFrobeniusMatrix ℂ n (L Y) = 1 at h
    exact sub_eq_iff_eq_add.mpr (eq_add_of_sub_eq' h)
  have hge : (1 : Matrix n n ℂ) ≤ hermitianFrobeniusMatrix ℂ n Y := by
    apply Matrix.le_iff.mpr
    rw [hdiff]
    exact hL Y hY
  refine ⟨Y,?_,?_,hge⟩
  · have hh := Matrix.PosDef.one.add_posSemidef (Matrix.le_iff.mp hge)
    simpa only [add_sub_cancel] using hh
  · rw [hEq,hI]
    exact Matrix.PosDef.one

end NLAlib
