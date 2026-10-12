import NLAlib.Matrix.SimpleEigenvalueReal

/-!
# The simple-eigenvalue perturbation toolkit

Nonzero pairing, the separated normalized similarity, and locally unique
continuous eigenvalue branches with the complex and real symmetric derivative
formulas. Source: Horn–Johnson (2013), Lemma 6.3.10 and Theorem 6.3.12.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The complete original simple-eigenvalue perturbation contract: nonzero
left–right pairing, a separated normalized scalar-block similarity, a locally
unique complex eigenvalue branch continuous on a neighborhood and with
derivative `y*Ex/(y*x)` at zero, and the real symmetric unit-vector formula
`xᵀEx` for real perturbations. The complex left vector is represented by its
row; the real symmetric branch is in the complex spectrum of the real
matrix's complexification. Source: Horn–Johnson (2013), Lemma 6.3.10 and
Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation -/
theorem simple_eigenvalue_perturbation_properties
    {A : Matrix n n ℂ} (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1)
    {Ar : Matrix m m ℝ} (Er : Matrix m m ℝ) (hAr : Ar.IsSymm)
    {xr : m → ℝ} {μr : ℝ} (hxr : xr ⬝ᵥ xr = 1) (hArx : Ar *ᵥ xr = μr • xr)
    (hμr : Ar.charpoly.rootMultiplicity μr = 1) :
    y ⬝ᵥ x ≠ 0 ∧
    (∃ (S : Matrix n n ℂ) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      μ ∉ spectrum ℂ ((S⁻¹ * A * S).submatrix
        (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))) ∧
    (∃ φ : ℂ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ ((y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), ContinuousAt φ t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (A + t • E)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), μ), p.2 ∈ spectrum ℂ (A + p.1 • E) ↔ φ p.1 = p.2)) ∧
    (∃ φ : ℝ → ℂ, φ 0 = μr ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ (Complex.ofReal (xr ⬝ᵥ (Er *ᵥ xr))) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ spectrum ℂ ((Ar + t • Er).map Complex.ofReal)) ∧
      (∀ᶠ p : ℝ × ℂ in 𝓝 (0, (μr : ℂ)),
        p.2 ∈ spectrum ℂ ((Ar + p.1 • Er).map Complex.ofReal) ↔ φ p.1 = p.2)) :=
  ⟨dotProduct_ne_zero_of_simple_eigenvalue hx hy hAx hyA hμ,
    exists_simple_eigenvalue_isolated_similarity hx hy hAx hyA hμ,
    exists_eigenvalue_branch_of_simple E hx hy hAx hyA hμ,
    exists_eigenvalue_branch_of_simple_of_isSymm Er hAr hxr hArx hμr⟩

end NLAlib
