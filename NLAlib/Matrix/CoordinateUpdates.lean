import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# A matrix coordinate update as an affine direction

Updating one flattened matrix coordinate is movement along the corresponding
matrix unit. This bridges coordinate Gaussian Stein identities and the
deterministic Gram resolvent derivative formulas.

Atlas: wishart-lambda-min-tail.
-/

noncomputable section

namespace NLAlib

/-- A flattened coordinate update is a scalar move along one matrix unit.
Source: finite matrix coordinate algebra in the operator hard-edge proof;
atlas wishart-lambda-min-tail (calculus bridge). -/
theorem matrixOf_curry_update_eq_add_single {ι κ R : Type*} [DecidableEq ι]
    [DecidableEq κ] [CommRing R] (x : ι × κ → R) (i : ι) (j : κ) (t : R) :
    Matrix.of (fun a b => Function.update x (i, j) t (a, b)) =
      Matrix.of (fun a b => x (a, b)) + (t - x (i, j)) • Matrix.single i j 1 := by
  ext a b
  change Function.update x (i, j) t (a, b) =
    x (a, b) + (t - x (i, j)) * Matrix.single i j 1 a b
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst a; subst b
    simp
  · subst a
    simp [hb, Ne.symm hb]
  · subst b
    simp [ha, Ne.symm ha]
  · simp [ha, Ne.symm ha]

end NLAlib
