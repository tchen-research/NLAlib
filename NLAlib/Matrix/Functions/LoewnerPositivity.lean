import NLAlib.Matrix.Functions.DaleckiiKrein
import NLAlib.Matrix.Functions.Monotonicity
import NLAlib.Matrix.Spectral.Complexification
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Positive divided-difference derivatives

Operator monotonicity implies positivity of the actual derivative.
Conversely a positive Löwner matrix gives a positive derivative by the
Schur product theorem. Tropp (2022), Löwner's criterion, Chapter 14.
-/

noncomputable section
open Matrix Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive Löwner matrix makes the Hadamard derivative positive. -/
theorem posSemidef_loewnerDerivative {f : ℝ → ℝ} {ev : n → ℝ}
    (hL : (loewnerMatrix f ev).PosSemidef) (U : unitary (Matrix n n ℂ))
    {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    (loewnerDerivative f ev U H).PosSemidef := by
  have hLc : ((loewnerMatrix f ev).map Complex.ofReal).PosSemidef :=
    (posSemidef_realMatrixComplexification_iff (loewnerMatrix f ev)).mpr hL
  exact (hLc.hadamard (hH.conjTranspose_mul_mul_same (U : Matrix n n ℂ))).mul_mul_conjTranspose_same _

/-- On an open spectral domain, operator monotonicity forces the actual
divided-difference derivative to preserve the positive cone. -/
theorem OperatorMonotoneOn.posSemidef_loewnerDerivative {I : Set ℝ} {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn I f) (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I)
    (ev : n → ℝ) (U : unitary (Matrix n n ℂ))
    (hdiag : A = (U : Matrix n n ℂ) * diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix n n ℂ).conjTranspose)
    {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    (loewnerDerivative f ev U H).PosSemidef := by
  have hfd := hasFDerivWithinAt_cfc_loewner hA
    (fun i => (hf _ (hAI (hA.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩))).differentiableAt
      (hI.mem_nhds (hAI (hA.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)))) ev U hdiag
  have hpath : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A
  have hd : HasDerivAt (fun t : ℝ => cfc f (A + t • H))
      (loewnerDerivative f ev U H) 0 := by
    exact hfd.comp_hasDerivAt_of_eq 0 hpath
      (Filter.Eventually.of_forall fun t => hA.add (hH.isHermitian.smul (IsSelfAdjoint.all t))) (by simp)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, spectrum ℝ (A + t • H) ⊆ I :=
    hpath.continuousAt.preimage_mem_nhds ((isOpen_setOf_real_spectrum_subset hI).mem_nhds (by simpa using hAI))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (t⁻¹ • (cfc f (A + t • H) - cfc f A)).PosSemidef := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    have hm' := hm.cfc_le hA (hA.add (hH.isHermitian.smul (IsSelfAdjoint.all t))) hAI ht
      (by rw [Matrix.le_iff, add_sub_cancel_left]; exact hH.smul (le_of_lt ht0))
    exact (Matrix.le_iff.mp hm').smul (inv_nonneg.mpr (le_of_lt ht0))
  have hclosed : IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
    simpa only [Set.Ici, Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix n n ℂ)))
  apply hclosed.mem_of_tendsto _ hpos
  simpa only [zero_add, zero_smul, add_zero] using hd.tendsto_slope_zero_right

end NLAlib
