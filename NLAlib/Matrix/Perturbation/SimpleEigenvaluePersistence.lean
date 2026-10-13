import NLAlib.Matrix.Spectral.CharpolySimplicity
import NLAlib.Matrix.Perturbation.SimpleEigenvalueReal
/-!
# Algebraic simplicity along the local eigenvalue branch

The existing continuous, locally unique branch retains all its derivative
properties and has characteristic-root multiplicity exactly one throughout
a neighborhood. Source: Horn--Johnson (2013), Theorem 6.3.12;
the strengthened mathematical source, Section.
-/

noncomputable section
open Filter
open scoped Matrix Topology
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The locally unique complex eigenvalue branch through a simple root
remains algebraically simple, while retaining neighborhood continuity and
the normalized left--right derivative. The left vector is represented by
its conjugate row. Empty dimension is excluded by the eigenvector
and multiplicity hypotheses, without an extra shape restriction.
Source: Horn--Johnson (2013), Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation (partial)
-/
theorem exists_eigenvalue_branch_of_simple_with_multiplicity
    {A : Matrix n n ℂ} (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ ((y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), ContinuousAt φ t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (A + t • E)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), μ), p.2 ∈ spectrum ℂ (A + p.1 • E) ↔ φ p.1 = p.2) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), (A + t • E).charpoly.rootMultiplicity (φ t) = 1) := by
  obtain ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique⟩ :=
    exists_eigenvalue_branch_of_simple E hx hy hAx hyA hμ
  refine ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique, ?_⟩
  exact eventually_rootMultiplicity_eq_one_of_continuous_eigenvalue A E id φ
    continuousAt_id hφcont rfl (by simpa only [hφ₀] using hμ) hφspec

open scoped Matrix.Norms.L2Operator in
/-- The same persistence of algebraic multiplicity holds for real
parameters and complex matrix data, with the original continuous branch,
spectral uniqueness and derivative intact. Source: Horn--Johnson (2013),
Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation (partial)
-/
theorem exists_real_parameter_eigenvalue_branch_of_simple_with_multiplicity
    {A : Matrix n n ℂ} (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℝ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ ((y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ t : ℝ in 𝓝 0, φ t ∈ spectrum ℂ (A + (t : ℂ) • E)) ∧
      (∀ᶠ p : ℝ × ℂ in 𝓝 (0, μ),
        p.2 ∈ spectrum ℂ (A + (p.1 : ℂ) • E) ↔ φ p.1 = p.2) ∧
      (∀ᶠ t : ℝ in 𝓝 0, (A + (t : ℂ) • E).charpoly.rootMultiplicity (φ t) = 1) := by
  obtain ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique⟩ :=
    exists_real_parameter_eigenvalue_branch_of_simple E hx hy hAx hyA hμ
  refine ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique, ?_⟩
  exact eventually_rootMultiplicity_eq_one_of_continuous_eigenvalue A E Complex.ofReal φ
    Complex.continuous_ofReal.continuousAt hφcont Complex.ofReal_zero
    (by simpa only [hφ₀] using hμ) hφspec

open scoped Matrix.Norms.L2Operator in
/-- A real symmetric matrix's simple eigenvalue stays algebraically simple
under every small real perturbation, while its branch has derivative
`xᵀ E x` for a unit eigenvector. Spectra and multiplicities are taken in the
complexification, so arbitrary real perturbations are allowed.
Source: Horn--Johnson (2013), Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation (partial)
-/
theorem exists_eigenvalue_branch_of_simple_of_isHermitian_with_multiplicity
    {A : Matrix n n ℝ} (E : Matrix n n ℝ) (hA : A.IsHermitian)
    {x : n → ℝ} {μ : ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = μ • x)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℝ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ (Complex.ofReal (x ⬝ᵥ (E *ᵥ x))) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ t : ℝ in 𝓝 0, φ t ∈ spectrum ℂ ((A + t • E).map Complex.ofReal)) ∧
      (∀ᶠ p : ℝ × ℂ in 𝓝 (0, (μ : ℂ)),
        p.2 ∈ spectrum ℂ ((A + p.1 • E).map Complex.ofReal) ↔ φ p.1 = p.2) ∧
      (∀ᶠ t : ℝ in 𝓝 0,
        ((A + t • E).map Complex.ofReal).charpoly.rootMultiplicity (φ t) = 1) := by
  obtain ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique⟩ :=
    exists_eigenvalue_branch_of_simple_of_isHermitian E hA hx hAx hμ
  have hmult : (A.map Complex.ofReal).charpoly.rootMultiplicity (φ 0) = 1 := by
    have hchar : (A.map Complex.ofReal).charpoly = Polynomial.map Complex.ofRealHom A.charpoly :=
      Matrix.charpoly_map A Complex.ofRealHom
    rw [hφ₀, hchar]
    simpa only [hμ, Complex.ofRealHom_eq_coe] using
      (Polynomial.eq_rootMultiplicity_map (p := A.charpoly) (f := Complex.ofRealHom)
        Complex.ofReal_injective μ).symm
  have hmap (t : ℝ) : (A + t • E).map Complex.ofReal =
      A.map Complex.ofReal + (t : ℂ) • E.map Complex.ofReal := by
    ext i j
    simp
  refine ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique, ?_⟩
  simpa only [hmap] using
    eventually_rootMultiplicity_eq_one_of_continuous_eigenvalue
      (A.map Complex.ofReal) (E.map Complex.ofReal) Complex.ofReal φ
      Complex.continuous_ofReal.continuousAt hφcont Complex.ofReal_zero hmult
      (by simpa only [hmap] using hφspec)

end NLAlib
