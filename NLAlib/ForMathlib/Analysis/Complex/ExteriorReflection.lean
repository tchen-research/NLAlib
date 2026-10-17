import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Schwarz labels for finite exterior families

Real, distinct affine slopes fix the labels of a finite family preserved by
complex conjugation. This separates the asymptotic argument from the spectral
conjugation calculation needed in the planar proof of `trace-exponential-stahl`.
-/

noncomputable section

open Complex Filter
open scoped Topology ComplexConjugate

namespace Complex

private theorem tendsto_conj_cobounded :
    Tendsto (conj : ℂ → ℂ) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa only [norm_conj] using (tendsto_norm_cobounded_atTop (E := ℂ))

private theorem tendsto_affine_ratio {f : ℂ → ℂ} {d c : ℂ}
    (hf : Tendsto (fun u => f u - d * u) (Bornology.cobounded ℂ) (𝓝 c)) :
    Tendsto (fun u => f u * u⁻¹) (Bornology.cobounded ℂ) (𝓝 d) := by
  have hi : Tendsto (fun u : ℂ => u⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have ht : Tendsto (fun u => (f u - d * u) * u⁻¹ + d)
      (Bornology.cobounded ℂ) (𝓝 d) := by
    simpa using (hf.mul hi).add_const d
  apply ht.congr'
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with u hu
  have hune : u ≠ 0 := by intro hzero; norm_num [hzero] at hu
  field_simp
  ring

/-- A finite exterior family preserved as an unlabelled family by conjugation
is eventually Schwarz-symmetric label by label when its affine slopes are real
and pairwise distinct. The constant terms may initially be arbitrary complex numbers. -/
theorem eventually_conj_eq_of_tendsto_affine_of_finite_matching
    {ι : Type*} [Finite ι] (f : ι → ℂ → ℂ) (d : ι → ℝ) (c : ι → ℂ)
    (hd : Function.Injective d)
    (hlim : ∀ i, Tendsto (fun u => f i u - (d i : ℂ) * u)
      (Bornology.cobounded ℂ) (𝓝 (c i)))
    (hmatch : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i,
      ∃ j, conj (f i (conj u)) = f j u) :
    ∀ᶠ u in Bornology.cobounded ℂ, ∀ i, f i (conj u) = conj (f i u) := by
  have hratio (i : ι) : Tendsto (fun u => f i u * u⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (d i : ℂ)) := tendsto_affine_ratio (hlim i)
  have href (i : ι) : Tendsto (fun u => conj (f i (conj u)) * u⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (d i : ℂ)) := by
    have h := continuous_conj.continuousAt.tendsto.comp
      ((hratio i).comp tendsto_conj_cobounded)
    simpa [Function.comp_def] using h
  have hneq : ∀ i j, ∀ᶠ u in Bornology.cobounded ℂ,
      i ≠ j → conj (f i (conj u)) ≠ f j u := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    have hdiff : (d i : ℂ) - (d j : ℂ) ≠ 0 := by
      intro heq
      exact hij (hd (ofReal_injective (sub_eq_zero.mp heq)))
    filter_upwards [((href i).sub (hratio j)).eventually_ne hdiff] with u hu _ heq
    exact hu (by rw [heq]; ring)
  have hneq' : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i j,
      i ≠ j → conj (f i (conj u)) ≠ f j u := by
    simpa only [Filter.eventually_all] using hneq
  filter_upwards [hmatch, hneq'] with u hm hn i
  obtain ⟨j, hj⟩ := hm i
  have hij : i = j := by
    by_contra hne
    exact hn i j hne hj
  subst j
  simpa using congrArg conj hj

end Complex
