import NLAlib.Matrix.Functions.MixedResolventHessian

/-! # Exact cyclic regrouping of twice-inserted native inverse words

The two formulas are identified with the same actual coordinate Hessian.
This avoids a combinatorial classification of twice-inserted positions and
retains the original matrix order and normalized trace.
Source: arXiv:2108.06312v2, Lemma 6.2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "M" => Matrix d d ℂ
local notation "E" => ((d × d) ⊕ (d × d)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- The actual cyclic Hessian of the normalized mixed moment in one
Hermitian matrix direction. -/
def cyclicMixedResolventHessian (X : M) (ζ : ℂ) (p : ℕ) (H : M) : ℂ :=
  (p : ℝ) • mixedResolventTraceInsertion X H H ζ (star ζ) (p + 1) p +
  (p : ℝ) • mixedResolventTraceInsertion X H H ζ (star ζ) p (p + 1)

open scoped Matrix.Norms.L2Operator in
/-- The literal twice-inserted normalized native word sum equals its cyclic
two-arc Hessian. Both are proved to be the actual second derivative, rather
than assuming a regrouping identity. Empty dimensions and order zero are
included; no matrix norm or commutation estimate is used.
Source: arXiv:2108.06312v2, Lemma 6.2.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem sum_twice_inserted_mixed_resolvent_trace_eq_cyclicHessian
    (X : M) (hX : X.IsHermitian) (H : M) (hH : H.IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    (∑ j : Fin (p + p), ∑ k : Fin (p + p + 1), normalizedTrace
      (((List.ofFn (resolventWordInsert
        (resolventWordInsert (mixedResolventWord (n := d) ζ p) j H) k H)).map
          (fun b => resolvent X b.1 * b.2)).prod)) =
      cyclicMixedResolventHessian X ζ p H := by
  let h : E := matrixRealCoordinates H
  have hh : L h = H := hermitianMatrixFromRealCoordinates_matrixRealCoordinates hH
  let g : E → ℂ := fun y => normalizedTrace
    (resolvent (X + L y) ζ ^ p * resolvent (X + L y) (star ζ) ^ p)
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hw := im_ne_zero_mixedResolventWord (n := d) ζ hζ p
  have hc := contDiff_hermitianCoordinateResolventWord X hX (mixedResolventWord ζ p) hw (r := ⊤)
  have heq : g = T ∘ hermitianCoordinateResolventWord X (mixedResolventWord ζ p) := by
    funext y
    simp only [g, T, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
      hermitianCoordinateResolventWord_mixed]
  have hsum : iteratedFDeriv ℝ 2 g (0 : E) ![h, h] =
      ∑ j : Fin (p + p), ∑ k : Fin (p + p + 1), normalizedTrace
        (((List.ofFn (resolventWordInsert
          (resolventWordInsert (mixedResolventWord (n := d) ζ p) j H) k H)).map
            (fun b => resolvent X b.1 * b.2)).prod) := by
    rw [heq, T.iteratedFDeriv_comp_left hc.contDiffAt (by simp)]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    rw [iteratedFDeriv_two_hermitianCoordinateResolventWord_apply X hX
      (mixedResolventWord ζ p) hw]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hh, map_sum, T,
      ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
      normalizedTraceLinearMap_apply, hermitianCoordinateResolventWord,
      hermitianCoordinateResolvent, map_zero, add_zero]
  have hcyclic : iteratedFDeriv ℝ 2 g (0 : E) ![h, h] =
      cyclicMixedResolventHessian X ζ p H := by
    rw [iteratedFDeriv_two_apply (𝕜 := ℝ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc' := fderiv_fderiv_normalizedTrace_mixed_resolvent_coordinate_cyclic_apply
      X hX ζ (star ζ) hζ (by simpa only [Complex.star_def, Complex.conj_im] using neg_ne_zero.mpr hζ)
      p p (0 : E) h h
    simpa only [g, hh, map_zero, add_zero, cyclicMixedResolventHessian] using hc'
  exact hsum.symm.trans hcyclic

end NLAlib
