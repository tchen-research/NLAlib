import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.Matrix.Structured.ProfileBlockNorms

/-!
# The profile masks commute with the actual Gaussian sample

Every mask is symmetric, so copying the canonical lower-triangular Gaussian
coordinate commutes with applying the mask to the profile or the sample.
-/

noncomputable section
namespace NLAlib

/-- Every symmetric deterministic entry mask commutes with the actual
canonical lower-triangular Gaussian sample construction. -/
theorem symmetricGaussianMatrix_mask
    {ι : Type*} [Fintype ι] [LinearOrder ι] (P : ι → ι → Prop)
    [DecidableRel P] (hP : ∀ i j, P i j ↔ P j i) (A G : Matrix ι ι ℝ) :
    symmetricGaussianMatrix (fun i j => if P i j then A i j else 0) G =
      (fun i j => if P i j then symmetricGaussianMatrix A G i j else 0) := by
  ext i j
  have hp : P (max i j) (min i j) ↔ P i j := by
    by_cases hij : i ≤ j
    · simp only [max_eq_right hij, min_eq_left hij]; exact hP j i
    · simp only [max_eq_left (le_of_not_ge hij), min_eq_right (le_of_not_ge hij)]
  simp only [symmetricGaussianMatrix, Matrix.of_apply, hp]
  split_ifs <;> simp

/-- Applying the first profile mask commutes with the actual Gaussian sample. -/
theorem symmetricGaussianMatrix_profileFirstPart {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) :
    symmetricGaussianMatrix (profileFirstPart A) G =
      profileFirstPart (symmetricGaussianMatrix A G) := by
  classical
  exact symmetricGaussianMatrix_mask (fun i j : Fin n => ProfileFirstMask i.val j.val)
    (fun i j => profileFirstMask_comm i.val j.val) A G

/-- Applying the second profile mask commutes with the actual Gaussian sample. -/
theorem symmetricGaussianMatrix_profileSecondPart {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) :
    symmetricGaussianMatrix (profileSecondPart A) G =
      profileSecondPart (symmetricGaussianMatrix A G) := by
  classical
  exact symmetricGaussianMatrix_mask (fun i j : Fin n => ProfileSecondMask i.val j.val)
    (fun i j => profileSecondMask_comm i.val j.val) A G

/-- Applying the residual profile mask commutes with the actual Gaussian sample. -/
theorem symmetricGaussianMatrix_profileRemainderPart {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) :
    symmetricGaussianMatrix (profileRemainderPart A) G =
      profileRemainderPart (symmetricGaussianMatrix A G) := by
  classical
  exact symmetricGaussianMatrix_mask (fun i j : Fin n => ProfileRemainderMask i.val j.val)
    (fun i j => profileRemainderMask_comm i.val j.val) A G

/-- Restricting to a supporting diagonal block commutes with the actual
symmetric Gaussian sample construction. -/
theorem symmetricGaussianMatrix_profileBlockPart {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    symmetricGaussianMatrix (profileBlockPart A t) G =
      profileBlockPart (symmetricGaussianMatrix A G) t := by
  classical
  exact symmetricGaussianMatrix_mask
    (fun i j : Fin n => InProfileBlock t i.val ∧ InProfileBlock t j.val)
    (fun _ _ => and_comm) A G

end NLAlib
