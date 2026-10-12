import NLAlib.Matrix.Inequalities.KyFanSums
import NLAlib.Matrix.Functions.FunctionalCalculusEigenvalues
/-!
# Nuclear norm of positive semidefinite matrices

The actual singular values of a positive semidefinite matrix are its sorted
nonnegative eigenvalues, including zeros and repeats; their sum is its trace.
Source: Horn–Johnson (1991), Corollary 3.4.4; Bhatia (1997), §IV.2.
Atlas: `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

/-- The nuclear norm of a real positive semidefinite matrix is exactly its
trace, including empty dimensions and singular matrices. Together with the
norm, duality, invariance and sharp-rank APIs this completes the Ky Fan/nuclear
norm definition bundle. Horn–Johnson (1991), Corollary 3.4.4.
atlas: ky-fan-norms-def (partial) -/
theorem nuclearNorm_eq_trace_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : nuclearNorm A = A.trace := by
  unfold nuclearNorm kyFanNorm
  rw [min_self, ← Fin.sum_univ_eq_sum_range (fun i => A.toEuclideanLin.singularValues i)]
  calc
    (∑ i : Fin (Fintype.card n), A.toEuclideanLin.singularValues i) =
        ∑ i : Fin (Fintype.card n), hA.isHermitian.eigenvalues₀ i :=
      Finset.sum_congr rfl (fun i _ => toEuclideanLin_singularValues_eq_eigenvalues₀_of_posSemidef hA i)
    _ = A.trace := (trace_eq_sum_eigenvalues₀ hA.isHermitian).symm

end NLAlib
