import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import NLAlib.ForMathlib.MeasureTheory.Matrix
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Basic.Pseudoinverse
/-!
# Measurability of matrix-valued maps

`Matrix m n ℝ` carries the product σ-algebra `Matrix.instMeasurableSpace`
(`NLAlib/ForMathlib/MeasureTheory/Matrix.lean`), and measurability of a matrix-valued map
`f : γ → Matrix m n ℝ` is equivalent to entrywise measurability,
`∀ i j, Measurable fun z => f z i j` (`Matrix.measurable_iff_entries`). This file collects the
entrywise closure properties that the probabilistic files use, as corollaries of that instance:

* `measurable_mul_entry_of`: entries of a product of entrywise-measurable maps are measurable;
  likewise entries of powers and of the total inverse `A⁻¹` (`measurable_pow_entry_of`,
  `measurable_inv_entry_of`), and the trace (`measurable_trace_of_entries`);
* `measurable_pinvL_entry_of`: entries of `pinvL (f z)` are measurable (through `det` and
  `adjugate`, both continuous);
* `measurable_frobSq_residual_of`: `z ↦ ‖(I − Q(z)Q(z)ᵀ)A‖_F²` is measurable;
* `measurable_frobSq_of_entries`: `frobSq` of an entrywise-measurable map is measurable;
* on `G : Matrix r k ℝ` (the space carrying `gaussianMatrix`): the entries of `pinvR G`
  and of `(G Gᵀ)⁻¹` (`measurable_pinvR_entry`, `measurable_inv_self_mul_transpose_apply`) and
  the spectral norms `‖(G Gᵀ)⁻¹‖₂`, `‖G†‖₂` (`measurable_specNorm_inv_self_mul_transpose`,
  `measurable_specNorm_pinvR`).

Layer 0: no probability is imported, only the Borel structures of `ℝ` and of `Matrix`.

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
    Measurable fun z => (f z * g z) i j :=
  (Matrix.measurable_entry i j).comp
    ((Matrix.measurable_iff_entries.mpr hf).matrix_mul (Matrix.measurable_iff_entries.mpr hg))

/-- Entries of a total inverse of an entrywise measurable real matrix map
are measurable, including singular inputs under the zero-inverse convention.
Source: determinant/adjugate inverse formula; atlas `wishart-lambda-min-tail`,
`gn-expected-error` (helper). -/
theorem measurable_inv_entry_of {ι : Type*} [Fintype ι] [DecidableEq ι] {A : γ → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (i j : ι) :
    Measurable fun x => (A x)⁻¹ i j := by
  have hA' : Measurable A := Matrix.measurable_iff_entries.mpr hA
  have hdet : Measurable fun x => (A x).det := continuous_id.matrix_det.measurable.comp hA'
  have hadj : Measurable fun x => (A x).adjugate i j :=
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable.comp hA'
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul hadj

/-- Every finite power of an entrywise measurable matrix map is entrywise
measurable. Source: finite multiplication; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_pow_entry_of {ι : Type*} [Fintype ι] [DecidableEq ι] {A : γ → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (n : ℕ) (i j : ι) :
    Measurable fun x => (A x ^ n) i j := by
  induction n generalizing i j with
  | zero => simpa only [pow_zero] using measurable_const
  | succ n ih =>
    simp only [pow_succ]
    exact measurable_mul_entry_of (fun a b => ih a b) hA i j

/-- The trace of an entrywise measurable matrix map is measurable.
Source: finite diagonal sum; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_trace_of_entries {ι : Type*} [Fintype ι] {A : γ → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) : Measurable fun x => Matrix.trace (A x) :=
  Finset.measurable_sum _ fun i _ => hA i i

/-- Entries of `pinvL (f z)` are measurable when the entries of `f` are.
Atlas `gn-expected-error` (measurability helper). -/
theorem measurable_pinvL_entry_of {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    {f : γ → Matrix a b ℝ} (hf : ∀ i j, Measurable fun z => f z i j) (i : b) (j : a) :
    Measurable fun z => pinvL (f z) i j := by
  have hF : Measurable f := Matrix.measurable_iff_entries.mpr hf
  have hc : Continuous fun G : Matrix a b ℝ => Gᵀ * G :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  have hdet : Measurable fun z => ((f z)ᵀ * f z).det := hc.matrix_det.measurable.comp hF
  have hadj : ∀ a' b', Measurable fun z => ((f z)ᵀ * f z).adjugate a' b' := fun a' b' =>
    (hc.matrix_adjugate.matrix_elem a' b').measurable.comp hF
  simp only [pinvL, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply,
      Matrix.transpose_apply,
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
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
    simp only [residual, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.sub_apply]
    exact measurable_const.sub (hD i j)
  unfold frobSq; simp only [frobInner_eq_sum_mul]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hR i j).mul (hR i j)

/-- `frobSq` of a matrix-valued map with measurable entries is measurable. Atlas
`gaussian-conditioning` (helper). -/
theorem measurable_frobSq_of_entries {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : γ → Matrix ι κ ℝ} (hf : ∀ i j, Measurable fun z => f z i j) :
    Measurable fun z => frobSq (f z) := by
  unfold frobSq; simp only [frobInner_eq_sum_mul]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hf i j).mul (hf i j)

/-! ### Maps of a matrix `G : Matrix r k ℝ` -/

/-- Every entry of `G ↦ pinvR G` is measurable. Atlas
`gaussian-conditioning` (helper). Generalised from `Fin k × Fin t` to finite index types. -/
theorem measurable_pinvR_entry {k t : Type*} [Fintype k] [Fintype t] [DecidableEq k] (i : t)
    (j : k) : Measurable fun G : Matrix k t ℝ => pinvR G i j := by
  have hc : Continuous fun G : Matrix k t ℝ => G * Gᵀ :=
    continuous_id.matrix_mul continuous_id.matrix_transpose
  have hdet : Measurable fun G : Matrix k t ℝ => (G * Gᵀ).det :=
    hc.matrix_det.measurable
  have hadj : ∀ a b, Measurable fun G : Matrix k t ℝ => (G * Gᵀ).adjugate a b := fun a b =>
    (hc.matrix_adjugate.matrix_elem a b).measurable
  simp only [pinvR, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply,
      Matrix.transpose_apply,
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun l _ => ?_
  exact (Matrix.measurable_entry l i).mul (hdet.inv.mul (hadj l j))

/-- The entries of `(G Gᵀ)⁻¹` are measurable functions of `G` (with Mathlib's convention
`A⁻¹ = 0` for singular `A`).

Helper for the inverse-Wishart moment computations (Tropp–Webber 2023, App. B). Atlas:
`inverse-wishart-mean` (helper). Generalised from `Fin r × Fin k` to finite index types. Ported
from the Prove2me solutions of the inverse Wishart series (`iwd_measurable_inv_entry`). -/
theorem measurable_inv_self_mul_transpose_apply {r k : Type*} [Fintype r] [Fintype k]
    [DecidableEq r] (i j : r) :
    Measurable (fun G : Matrix r k ℝ => (G * Gᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Matrix r k ℝ => G * Gᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖(G Gᵀ)⁻¹‖₂` is measurable on `Matrix r k ℝ`.

Helper for Tropp–Webber 2023, Lemma B.4. Atlas: `inverse-wishart-spectral-moment` (helper).
Generalised from `Fin r × Fin k` to finite index types. Ported from the Prove2me solution
`Sol_GaussianMatrix_inverse_wishart_spectral_moment` (`iwsm_measurable_specNorm_inv_gram`). -/
theorem measurable_specNorm_inv_self_mul_transpose {r k : Type*} [Fintype r] [Fintype k]
    [DecidableEq r] :
    Measurable (fun G : Matrix r k ℝ => specNorm (G * Gᵀ)⁻¹) := by
  have h1 : Measurable (fun G : Matrix r k ℝ => (G * Gᵀ)⁻¹) :=
    Matrix.measurable_iff_entries.mpr measurable_inv_self_mul_transpose_apply
  exact continuous_norm.measurable.comp h1

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖G†‖₂` is measurable on `Matrix r k ℝ`, with `G† = pinvR G`.

Helper for HMT 2011, Prop A.4. Atlas: `pinv-spectral-expectation` (helper). Generalised from
`Fin r × Fin k` to finite index types. Ported from the Prove2me solution
`Sol_GaussianMatrix_pinv_spectral_expectation` (`measurable_specNorm_pinvR`). -/
theorem measurable_specNorm_pinvR {r k : Type*} [Fintype r] [Fintype k] [DecidableEq r]
    [DecidableEq k] :
    Measurable (fun G : Matrix r k ℝ => specNorm (pinvR G)) := by
  have h1 : Measurable (fun G : Matrix r k ℝ => pinvR G) :=
    Matrix.measurable_iff_entries.mpr fun j i => measurable_pinvR_entry j i
  exact continuous_norm.measurable.comp h1

end NLAlib
