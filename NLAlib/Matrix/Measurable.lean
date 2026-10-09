import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.Matrix
import NLAlib.Matrix.Projections
import NLAlib.Matrix.Pseudoinverse

/-!
# Measurability of matrix-valued maps

Mathlib has no `MeasurableSpace (Matrix m n ℝ)`, so measurability of a matrix-valued map
`f : γ → Matrix m n ℝ` is stated entrywise, `∀ i j, Measurable fun z => f z i j`
(STANDARDS §3). This file collects the closure properties of that notion that the
probabilistic files need:

* `measurable_mul_entry_of`: entries of a product of entrywise-measurable maps are measurable;
* `measurable_pinvL_entry_of`: entries of `pinvL (f z)` are measurable (through `det` and
  `adjugate`, both continuous);
* `measurable_frobSq_residual_of`: `z ↦ ‖(I − Q(z)Q(z)ᵀ)A‖_F²` is measurable.

Layer 0: no probability is imported, only the Borel structure of `ℝ`.

Atlas: `gn-expected-error` (measurability helpers).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {γ : Type*} [MeasurableSpace γ]

/-- Entries of a product of entrywise-measurable matrix maps are measurable.
Atlas `gn-expected-error` (measurability helper). -/
theorem measurable_mul_entry_of {a b c : Type*} [Fintype b] {f : γ → Matrix a b ℝ}
    {g : γ → Matrix b c ℝ} (hf : ∀ i j, Measurable fun z => f z i j)
    (hg : ∀ i j, Measurable fun z => g z i j) (i : a) (j : c) :
    Measurable fun z => (f z * g z) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hf i l).mul (hg l j)

/-- Entries of `pinvL (f z)` are measurable when the entries of `f` are.
Atlas `gn-expected-error` (measurability helper). -/
theorem measurable_pinvL_entry_of {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    {f : γ → Matrix a b ℝ} (hf : ∀ i j, Measurable fun z => f z i j) (i : b) (j : a) :
    Measurable fun z => pinvL (f z) i j := by
  have hF : Measurable fun z => (fun i j => f z i j : a → b → ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hf i j
  have hc : Continuous fun G : a → b → ℝ => (Matrix.of G)ᵀ * Matrix.of G :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  have hdet : Measurable fun z => ((f z)ᵀ * f z).det := hc.matrix_det.measurable.comp hF
  have hadj : ∀ a' b', Measurable fun z => ((f z)ᵀ * f z).adjugate a' b' := fun a' b' =>
    (hc.matrix_adjugate.matrix_elem a' b').measurable.comp hF
  simp only [pinvL, Matrix.mul_apply, Matrix.transpose_apply, Matrix.inv_def,
    Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun l _ => ?_
  have h1 := hadj i l
  have h2 := hf j l
  fun_prop

/-- `z ↦ ‖(I − Q(z)Q(z)ᵀ)A‖_F²` is measurable for entrywise-measurable `Q`.
Atlas `gn-expected-error` (measurability helper). -/
theorem measurable_frobSq_residual_of {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    (A : Matrix m n ℝ) {Qf : γ → Matrix m q ℝ} (hQ : ∀ i j, Measurable fun z => Qf z i j) :
    Measurable fun z => frobSq (residual (Qf z) A) := by
  have hQt : ∀ i j, Measurable fun z => (Qf z)ᵀ i j := fun i j => hQ j i
  have hA : ∀ i j, Measurable fun _ : γ => A i j := fun _ _ => measurable_const
  have hD := measurable_mul_entry_of hQ (measurable_mul_entry_of hQt hA)
  have hR : ∀ i j, Measurable fun z => residual (Qf z) A i j := fun i j => by
    simp only [residual, Matrix.sub_apply]
    exact measurable_const.sub (hD i j)
  unfold frobSq frobInner
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hR i j).mul (hR i j)

end NLAlib
