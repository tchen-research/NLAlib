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
* `measurable_frobSq_residual_of`: `z ↦ ‖(I − Q(z)Q(z)ᵀ)A‖_F²` is measurable;
* `measurable_frobSq_of_entries`: `frobSq` of an entrywise-measurable map is measurable;
* on arrays `G : r → k → ℝ` (the space carrying `gaussianMatrix`): the entries of `pinvR G`
  and of `(G Gᵀ)⁻¹` (`measurable_pinvR_entry`, `measurable_inv_self_mul_transpose_apply`) and
  the spectral norms `‖(G Gᵀ)⁻¹‖₂`, `‖G†‖₂` (`measurable_specNorm_inv_self_mul_transpose`,
  `measurable_specNorm_pinvR`).

Layer 0: no probability is imported, only the Borel structure of `ℝ`.

Atlas: `gn-expected-error`, `gaussian-conditioning`, `inverse-wishart-mean`,
`inverse-wishart-spectral-moment`, `pinv-spectral-expectation` (measurability helpers).
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

/-- `frobSq` of a matrix-valued map with measurable entries is measurable. Atlas
`gaussian-conditioning` (helper). -/
theorem measurable_frobSq_of_entries {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : γ → Matrix ι κ ℝ} (hf : ∀ i j, Measurable fun z => f z i j) :
    Measurable fun z => frobSq (f z) := by
  unfold frobSq frobInner
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hf i j).mul (hf i j)

/-! ### Maps of an array `G : r → k → ℝ` -/

/-- Every entry of `G ↦ pinvR G` (on the array view) is measurable. Atlas
`gaussian-conditioning` (helper). Generalised from `Fin k × Fin t` to finite index types. -/
theorem measurable_pinvR_entry {k t : Type*} [Fintype k] [Fintype t] [DecidableEq k] (i : t)
    (j : k) : Measurable fun G : k → t → ℝ => pinvR (Matrix.of G) i j := by
  have hc : Continuous fun G : k → t → ℝ => Matrix.of G * (Matrix.of G)ᵀ :=
    continuous_id.matrix_mul continuous_id.matrix_transpose
  have hdet : Measurable fun G : k → t → ℝ => (Matrix.of G * (Matrix.of G)ᵀ).det :=
    hc.matrix_det.measurable
  have hadj : ∀ a b, Measurable fun G : k → t → ℝ =>
      (Matrix.of G * (Matrix.of G)ᵀ).adjugate a b := fun a b =>
    (hc.matrix_adjugate.matrix_elem a b).measurable
  simp only [pinvR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.inv_def,
    Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun l _ => ?_
  have := hadj l j
  fun_prop

/-- The entries of `(G Gᵀ)⁻¹` are measurable functions of `G` (with Mathlib's convention
`A⁻¹ = 0` for singular `A`).

Helper for the inverse-Wishart moment computations (Tropp–Webber 2023, App. B). Atlas:
`inverse-wishart-mean` (helper). Generalised from `Fin r × Fin k` to finite index types. Ported
from the Prove2me solutions of the inverse Wishart series (`iwd_measurable_inv_entry`). -/
theorem measurable_inv_self_mul_transpose_apply {r k : Type*} [Fintype r] [Fintype k]
    [DecidableEq r] (i j : r) :
    Measurable (fun G : r → k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : r → k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖(G Gᵀ)⁻¹‖₂` is measurable on arrays `G : r → k → ℝ`.

Helper for Tropp–Webber 2023, Lemma B.4. Atlas: `inverse-wishart-spectral-moment` (helper).
Generalised from `Fin r × Fin k` to finite index types. Ported from the Prove2me solution
`Sol_GaussianMatrix_inverse_wishart_spectral_moment` (`iwsm_measurable_specNorm_inv_gram`). -/
theorem measurable_specNorm_inv_self_mul_transpose {r k : Type*} [Fintype r] [Fintype k]
    [DecidableEq r] :
    Measurable (fun G : r → k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
  have h1 : Measurable (fun G : r → k → ℝ =>
      Matrix.of.symm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply]
    exact measurable_inv_self_mul_transpose_apply a b
  have h2 : Continuous (fun M : r → r → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖G†‖₂` is measurable on arrays `G : r → k → ℝ`, with `G† = pinvR G`.

Helper for HMT 2011, Prop A.4. Atlas: `pinv-spectral-expectation` (helper). Generalised from
`Fin r × Fin k` to finite index types. Ported from the Prove2me solution
`Sol_GaussianMatrix_pinv_spectral_expectation` (`measurable_specNorm_pinvR`). -/
theorem measurable_specNorm_pinvR {r k : Type*} [Fintype r] [Fintype k] [DecidableEq r]
    [DecidableEq k] :
    Measurable (fun G : r → k → ℝ => specNorm (pinvR (Matrix.of G))) := by
  have h1 : Measurable (fun G : r → k → ℝ => Matrix.of.symm (pinvR (Matrix.of G))) := by
    refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => ?_
    simp only [Matrix.of_symm_apply, pinvR, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply]
    refine Finset.measurable_sum _ fun a _ => ?_
    refine Measurable.mul ?_ (measurable_inv_self_mul_transpose_apply a i)
    exact (measurable_pi_apply a).eval
  have h2 : Continuous (fun M : k → r → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

end NLAlib
