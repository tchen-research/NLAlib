import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Spectral.SingularValueSpectrum
/-!
# Finite-coordinate transport for the smallest singular value

The variational minimum is invariant under relabeling rows and columns.
This links the arbitrary finite-index variational API to the actual native
singular-value list, including wide and rank-deficient matrices.
Source: Horn--Johnson, Section 2.6; supports `principal-angles-def`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Relabeling finite real matrix indices preserves the variational smallest
singular value, including empty domains. The unit spheres are explicitly
equivalent. Horn--Johnson, Section 2.6; supports `principal-angles-def`. -/
theorem sigmaMin_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    sigmaMin (A.reindex em en) = sigmaMin A := by
  let E : {x : n → ℝ // x ⬝ᵥ x = 1} ≃ {x : q → ℝ // x ⬝ᵥ x = 1} :=
    { toFun x := ⟨fun j => x.val (en.symm j),
        (en.symm.sum_comp (fun j => x.val j * x.val j)).trans x.property⟩
      invFun y := ⟨fun i => y.val (en i),
        (en.sum_comp (fun i => y.val i * y.val i)).trans y.property⟩
      left_inv x := by apply Subtype.ext; funext i; simp
      right_inv y := by apply Subtype.ext; funext j; simp }
  unfold sigmaMin
  rw [← E.surjective.iInf_comp]
  apply iInf_congr
  intro x
  have hMv : (A.reindex em en) *ᵥ (E x).val = (A *ᵥ x.val) ∘ em.symm := by
    funext i
    change (∑ j : q, A (em.symm i) (en.symm j) * x.val (en.symm j)) =
      ∑ j : n, A (em.symm i) j * x.val j
    exact en.symm.sum_comp (fun j : n => A (em.symm i) j * x.val j)
  rw [hMv]
  exact congrArg Real.sqrt (em.symm.sum_comp
    (fun i => (A *ᵥ x.val) i * (A *ᵥ x.val) i))

/-- With nonempty domain, the variational minimum is the last actual
domain-indexed native singular value. Wide matrices include kernel zeros.
Horn--Johnson, Section 2.6; supports `principal-angles-def`. -/
theorem sigmaMin_eq_toEuclideanLin_singularValues_last {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) (hn : 0 < Fintype.card n) :
    sigmaMin A = A.toEuclideanLin.singularValues (Fintype.card n - 1) := by
  rw [← sigmaMin_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    sigmaMin_eq_singularValues_last _ hn, singularValues_reindex, singularValues_eq_linearMap]

end NLAlib
