import Mathlib.MeasureTheory.Measure.Prod

/-!
# Product of push-forward measures along a.e.-measurable maps

`measure_map_prod_map_of_aemeasurable`: the `AEMeasurable` version of Mathlib's
`MeasureTheory.Measure.map_prod_map` (which needs `Measurable` maps). Candidate for
`Mathlib/MeasureTheory/Measure/Prod.lean`.

Moved from the Hanson–Wright proof (ported from HighDimProb commit c0cb8d9) in the dedup round
(2026-10-12).
-/

open MeasureTheory

namespace NLAlib

/-- `(μ.map f).prod (ν.map g) = (μ.prod ν).map (fun p => (f p.1, g p.2))` for a.e.-measurable
`f`, `g` and s-finite `μ`, `ν`; the `AEMeasurable` version of `Measure.map_prod_map`.
Atlas `hanson-wright` (helper). -/
theorem measure_map_prod_map_of_aemeasurable {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → γ} {g : β → δ} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    (μ.map f).prod (ν.map g) =
      (μ.prod ν).map (fun p : α × β => (f p.1, g p.2)) := by
  let f' := hf.mk f
  let g' := hg.mk g
  have hf_map : μ.map f = μ.map f' := Measure.map_congr hf.ae_eq_mk
  have hg_map : ν.map g = ν.map g' := Measure.map_congr hg.ae_eq_mk
  have hpair :
      (fun p : α × β => (f p.1, g p.2)) =ᵐ[μ.prod ν]
        Prod.map f' g' := by
    exact
      ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp hf.ae_eq_mk).prodMk
        ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp hg.ae_eq_mk)
  calc
    (μ.map f).prod (ν.map g)
        = (μ.map f').prod (ν.map g') := by rw [hf_map, hg_map]
    _ = (μ.prod ν).map (Prod.map f' g') :=
        Measure.map_prod_map μ ν hf.measurable_mk hg.measurable_mk
    _ = (μ.prod ν).map (fun p : α × β => (f p.1, g p.2)) :=
        Measure.map_congr hpair.symm

end NLAlib
