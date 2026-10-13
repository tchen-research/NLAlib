import NLAlib.Matrix.Functions.Basic
import Mathlib.Tactic.Ring

/-!
# Generalized Klein inequality

`generalized_klein`: if `∑ᵢ fᵢ(a) gᵢ(h) ≥ 0` for all `a, h ∈ I`, then
`∑ᵢ Re tr (fᵢ(A) gᵢ(H)) ≥ 0` for Hermitian `A`, `H` (over `[RCLike 𝕜]`) with spectra in `I`.
Tropp 2015, Prop. 8.3.5. Atlas: `operator-monotone-convex`.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] [DecidableEq d]

/-- `Re tr (U diag(a) Uᴴ · V diag(b) Vᴴ) = ∑ⱼₖ aⱼ bₖ |(Uᴴ V)ⱼₖ|²`. -/
private theorem re_trace_pair (U V : Matrix d d 𝕜) (a b : d → ℝ) :
    RCLike.re (trace ((U * diagonal (fun j => (a j : 𝕜)) * Uᴴ) *
      (V * diagonal (fun k => (b k : 𝕜)) * Vᴴ))) =
    ∑ j, ∑ k, a j * b k * ‖(Uᴴ * V) j k‖ ^ 2 := by
  let W := Uᴴ * V
  have hw : Vᴴ * U = Wᴴ := by simp [W, conjTranspose_mul]
  calc
    _ = RCLike.re (trace (diagonal (fun j => (a j : 𝕜)) * W *
       diagonal (fun k => (b k : 𝕜)) * Wᴴ)) := by
      simp only [W, ← hw]
      congr 1
      simp only [mul_assoc]
      rw [trace_mul_comm U]
      simp only [mul_assoc]
    _ = _ := by
      change RCLike.re (trace (diagonal (fun j => (a j : 𝕜)) * W *
        diagonal (fun k => (b k : 𝕜)) * Wᴴ)) = ∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2
      simp only [trace, diag_apply, mul_apply, diagonal, of_apply, ite_mul, mul_ite, zero_mul,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        conjTranspose_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [show (a j : 𝕜) * W j k * (b k : 𝕜) * star (W j k)
          = ((a j * b k : ℝ) : 𝕜) * (W j k * star (W j k)) by push_cast; ring,
        RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
        RCLike.ofReal_re, mul_assoc]

/-- **Generalized Klein inequality**: if `∑ i, f i a * g i h ≥ 0` for all `a, h ∈ I`, then
`∑ i, Re tr (f i (A) · g i (H)) ≥ 0` for Hermitian `A`, `H` with spectra in `I`.
Tropp 2015, Prop. 8.3.5. The convexity hypothesis on `I` is not used by the proof; it is kept to
match the source.
atlas: operator-monotone-convex -/
theorem generalized_klein {N : ℕ}
    (I : Set ℝ) (_hI : Convex ℝ I) (f g : Fin N → ℝ → ℝ)
    (hfg : ∀ a ∈ I, ∀ h ∈ I, 0 ≤ ∑ i, f i a * g i h)
    (A H : Matrix d d 𝕜) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hHI : spectrum ℝ H ⊆ I) :
    0 ≤ ∑ i, RCLike.re (Matrix.trace (cfc (f i) A * cfc (g i) H)) := by
  have heq (i : Fin N) :
      RCLike.re (trace (cfc (f i) A * cfc (g i) H)) =
      ∑ j, ∑ k, f i (hA.eigenvalues j) * g i (hH.eigenvalues k) *
        ‖(((hA.eigenvectorUnitary : Matrix d d 𝕜)ᴴ *
          (hH.eigenvectorUnitary : Matrix d d 𝕜)) j k)‖ ^ 2 := by
    simp only [hA.cfc_eq, hH.cfc_eq, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]
    exact re_trace_pair _ _ _ _
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro k _
  rw [← Finset.sum_mul]
  exact mul_nonneg (hfg _ (hAI (hA.eigenvalues_mem_spectrum_real j)) _
    (hHI (hH.eigenvalues_mem_spectrum_real k))) (by positivity)

end NLAlib
