import NLAlib.Matrix.Spectral.SVD
import Mathlib.Analysis.Complex.Basic

/-!
# Singular values of diagonal matrices

The complete singular-value multiset of a complex diagonal matrix is the
multiset of its diagonal moduli, retaining all zero multiplicities.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The complete domain singular-value multiset of a complex diagonal matrix is
the multiset of the moduli of its diagonal entries, retaining zero multiplicities. -/
theorem multiset_singularValues_diagonal_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) :
    (Finset.univ : Finset (Fin (Fintype.card ι))).val.map
      (fun i : Fin (Fintype.card ι) => singularValues (Matrix.diagonal d) (i : ℕ)) =
    (Finset.univ : Finset ι).val.map (fun i => ‖d i‖) := by
  let G := (Matrix.diagonal d)ᴴ * Matrix.diagonal d
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hdiag : G = Matrix.diagonal (fun i => ((‖d i‖ ^ 2 : ℝ) : ℂ)) := by
    simp only [G, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simpa only [Pi.star_apply, Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' (d i)
  have hroot : G.charpoly.roots =
      (Finset.univ : Finset ι).val.map (fun i => ((‖d i‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hdiag, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _
  have he := congrArg (Multiset.map (fun z : ℂ => Real.sqrt z.re))
    (hG.roots_charpoly_eq_eigenvalues₀.symm.trans hroot)
  simp only [Multiset.map_map, Function.comp_def,
    Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)] at he
  convert he using 1
  congr 1
  funext i
  rw [← sq_singularValues_eq_eigenvalues₀ (Matrix.diagonal d) i]
  change singularValues (Matrix.diagonal d) (i : ℕ) =
    Real.sqrt (singularValues (Matrix.diagonal d) (i : ℕ) ^ 2)
  rw [Real.sqrt_sq (singularValues_nonneg _ _)]


end NLAlib
