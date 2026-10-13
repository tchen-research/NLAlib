import NLAlib.Matrix.Structured.StructuredMatrices
/-!
# Cauchy determinants on arbitrary finite coordinate labels

Simultaneous finite-coordinate transport preserves the Cauchy determinant and
its denominator product. Horn–Johnson §0.9.12; structured-matrices-def.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Cauchy's determinant formula on arbitrary finite labels, with the two
Vandermonde factors in the same finite coordinate ordering. The denominator
product is intrinsic. Empty labels and repeated parameters are included.
Horn–Johnson 2013, §0.9.12.
atlas: structured-matrices-def (partial) -/
theorem det_cauchyMatrix_eq_vandermonde_fintype {n : Type*} [Fintype n] [DecidableEq n]
    (x y : n → ℝ) (hDen : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (Matrix.vandermonde (x ∘ (Fintype.equivFin n).symm)).det *
        (Matrix.vandermonde (y ∘ (Fintype.equivFin n).symm)).det /
          (∏ i : n, ∏ j : n, (x i + y j)) := by
  let e := Fintype.equivFin n
  have hF := det_cauchyMatrix_eq_vandermonde (x ∘ e.symm) (y ∘ e.symm)
    (fun i j => hDen (e.symm i) (e.symm j))
  have hMatrix : cauchyMatrix (x ∘ e.symm) (y ∘ e.symm) = (cauchyMatrix x y).reindex e e := rfl
  rw [hMatrix, Matrix.det_reindex_self] at hF
  have hProd : (∏ i : Fin (Fintype.card n), ∏ j : Fin (Fintype.card n),
      (x (e.symm i) + y (e.symm j))) = ∏ i : n, ∏ j : n, (x i + y j) := by
    rw [e.symm.prod_comp (fun i : n => ∏ j : Fin (Fintype.card n), (x i + y (e.symm j)))]
    exact Finset.prod_congr rfl (fun i _ => e.symm.prod_comp (fun j : n => x i + y j))
  simpa only [Function.comp_apply, hProd] using hF

end NLAlib
