import NLAlib.Matrix.Nonnegative.CollatzWielandt
import NLAlib.Matrix.Nonnegative.PerronIrreducible

/-! # Attainment of irreducible Collatz extrema

Positive Perron eigenvectors make every Collatz ratio identical. This is the
attainment statement that is unavailable for general reducible matrices.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/
noncomputable section
open Matrix Finset
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- In the irreducible nonzero case, one positive unit-sum vector attains both
Collatz extrema, and every ratio equals the complex spectral radius.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem IsIrreducible.exists_attaining_collatz_ratios {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hAne : A ≠ 0) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, (A *ᵥ p) i / p i = (spectralRadius ℂ (A.map Complex.ofReal)).toReal) ∧
      Finset.univ.inf' Finset.univ_nonempty (fun i => (A *ᵥ p) i / p i) =
        (spectralRadius ℂ (A.map Complex.ofReal)).toReal ∧
      Finset.univ.sup' Finset.univ_nonempty (fun i => (A *ᵥ p) i / p i) =
        (spectralRadius ℂ (A.map Complex.ofReal)).toReal := by
  obtain ⟨p, _, _, hp, _, hs, _, he, _⟩ := hA.exists_positive_perron_pair hAne
  have hratio (i : ι) : (A *ᵥ p) i / p i =
      (spectralRadius ℂ (A.map Complex.ofReal)).toReal := by
    rw [he]
    exact mul_div_cancel_right₀ _ (hp i).ne'
  refine ⟨p, hp, hs, hratio, ?_, ?_⟩
  · simp only [hratio, Finset.inf'_const]
  · simp only [hratio, Finset.sup'_const]

end Matrix
