import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fubini along an arbitrary finite product coordinate

The insertion map exposes a chosen coordinate of a finite product, retaining
all the other coordinates and their measures in their natural order.
-/

noncomputable section

open MeasureTheory

namespace MeasureTheory

/-- An integrable function on a finite product can first be integrated along
any chosen coordinate. The remaining coordinates use `Fin.succAbove` and the
reconstruction map is `Fin.insertNth`. -/
theorem integral_pi_fin_eq_integral_insertNth
    {n : ℕ} {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Fin (n + 1) → Measure X) [∀ j, SigmaFinite (μ j)]
    (i : Fin (n + 1)) {f : (Fin (n + 1) → X) → E} (hf : Integrable f (Measure.pi μ)) :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ y, ∫ t, f (i.insertNth t y) ∂μ i ∂Measure.pi (fun j => μ (i.succAbove j)) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) i).symm
  have hp := (measurePreserving_piFinSuccAbove μ i).symm
  have hi : Integrable (f ∘ e)
      ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  calc
    _ = ∫ p : X × (Fin n → X), f (e p)
        ∂(μ i).prod (Measure.pi (fun j => μ (i.succAbove j))) :=
      (hp.integral_comp' f).symm
    _ = _ := by
      change (∫ p : X × (Fin n → X), (f ∘ e) p
        ∂(μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) = _
      rw [integral_prod_symm _ hi]
      simp only [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk]

end MeasureTheory
