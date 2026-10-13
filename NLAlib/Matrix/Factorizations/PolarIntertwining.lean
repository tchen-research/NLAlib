import NLAlib.Matrix.Factorizations.PolarDecomposition

/-!
# Polar factors preserve adjoint intertwining

An intertwiner that also intertwines adjoints has a Gram matrix commuting with
the domain operator. Its polar factor therefore intertwines the same operators.
The explicit polar-frame formula supplies one common orthogonal matrix for
an arbitrary family of operators. Horn–Johnson §2.5; real-similarity descent.
-/

noncomputable section
open scoped Matrix MatrixOrder
namespace NLAlib

/-- The explicit polar frame of a full-column-rank real intertwiner also
intertwines the operators whenever both the operator and transpose identities
hold. The same `polarFrame T` works for every member of an operator family.
Horn–Johnson 2013, Theorem 2.5.21; supports `real-similarity-descent`. -/
theorem mul_polarFrame_eq_polarFrame_mul_of_intertwining
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ) (T : Matrix m n ℝ)
    (hT : IsUnit (Tᵀ * T)) (hAT : A * T = T * B) (hAdj : Aᵀ * T = T * Bᵀ) :
    A * polarFrame T = polarFrame T * B := by
  let G := Tᵀ * T
  let Q := CFC.sqrt G
  have hAdjT : Tᵀ * A = B * Tᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      congrArg Matrix.transpose hAdj
  have hComm : Commute G B := by
    change (Tᵀ * T) * B = B * (Tᵀ * T)
    calc
      _ = Tᵀ * (T * B) := Matrix.mul_assoc _ _ _
      _ = Tᵀ * (A * T) := by rw [hAT]
      _ = (Tᵀ * A) * T := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hAdjT, Matrix.mul_assoc]
  have hQComm : Commute Q B := hComm.cfcₙ_nnreal NNReal.sqrt
  have hNonneg : 0 ≤ G := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self T).nonneg
  have hQUnit : IsUnit Q := (CFC.isUnit_sqrt_iff _ hNonneg).mpr hT
  have hQDet := (Matrix.isUnit_iff_isUnit_det Q).mp hQUnit
  have hQl : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQDet
  have hQr : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQDet
  have hFrame : polarFrame T * Q = T := by
    change T * Q⁻¹ * Q = T
    rw [Matrix.mul_assoc, hQl, Matrix.mul_one]
  have hEq : (A * polarFrame T) * Q = (polarFrame T * B) * Q := by
    calc
      _ = A * T := by rw [Matrix.mul_assoc, hFrame]
      _ = T * B := hAT
      _ = polarFrame T * (Q * B) :=
        (congrArg (fun M : Matrix m n ℝ => M * B) hFrame).symm.trans (Matrix.mul_assoc _ _ _)
      _ = _ := by rw [hQComm.eq, ← Matrix.mul_assoc]
  have h := congrArg (fun M : Matrix m n ℝ => M * Q⁻¹) hEq
  simpa only [Matrix.mul_assoc, hQr, Matrix.mul_one] using h

end NLAlib
