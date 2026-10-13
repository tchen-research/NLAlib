import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Perturbation.SimpleEigenvaluePerturbation

/-!
# Simple eigenvalues of real symmetric matrices

For a real unit eigenvector of a symmetric matrix, the left–right derivative
reduces to the quadratic form in the perturbation. The locally unique branch
is an eigenvalue of the complexification for real parameters.
Source: Horn–Johnson (2013), Theorem 6.3.12.
-/

noncomputable section
open Filter
open scoped Matrix Topology

namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Restricting the complex simple-eigenvalue branch to real parameters
preserves its local spectral uniqueness and its left–right derivative.
Source: Horn–Johnson (2013), Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation (partial) -/
theorem exists_real_parameter_eigenvalue_branch_of_simple
    {A : Matrix n n ℂ} (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℝ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ ((y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ spectrum ℂ (A + (t : ℂ) • E)) ∧
      (∀ᶠ p : ℝ × ℂ in 𝓝 (0, μ),
        p.2 ∈ spectrum ℂ (A + (p.1 : ℂ) • E) ↔ φ p.1 = p.2) := by
  obtain ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique⟩ :=
    exists_eigenvalue_branch_of_simple E hx hy hAx hyA hμ
  have hreal : Tendsto Complex.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto
  have hderiv : HasDerivAt (fun t : ℝ => φ t) ((y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)) 0 := by
    apply HasDerivAt.comp_ofReal
    simpa only [Complex.ofReal_zero] using hφderiv
  refine ⟨fun t => φ t, by simpa using hφ₀, hderiv.continuousAt, hderiv,
    ?_, hreal.eventually hφspec, ?_⟩
  · filter_upwards [hreal.eventually hφnear] with t ht
    exact ht.comp Complex.continuous_ofReal.continuousAt
  ·
    have hmap : Tendsto (fun p : ℝ × ℂ => ((p.1 : ℂ), p.2))
        (𝓝 ((0 : ℝ), μ)) (𝓝 ((0 : ℂ), μ)) := by
      have hcont : Continuous (fun p : ℝ × ℂ => ((p.1 : ℂ), p.2)) := by fun_prop
      simpa using (hcont.continuousAt (x := ((0 : ℝ), μ))).tendsto
    exact hmap.eventually hφunique

open scoped Matrix.Norms.L2Operator in
/-- A real symmetric matrix's simple eigenvalue has derivative `xᵀEx`
along every real perturbation when its eigenvector has unit Euclidean norm.
The real parameter branch is locally unique in the complex spectrum, which
also includes all possible nearby real eigenvalues. Source: Horn–Johnson
(2013), Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation -/
theorem exists_eigenvalue_branch_of_simple_of_isHermitian
    {A : Matrix n n ℝ} (E : Matrix n n ℝ) (hAh : A.IsHermitian)
    {x : n → ℝ} {μ : ℝ} (hxn : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = μ • x)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℝ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ (Complex.ofReal (x ⬝ᵥ (E *ᵥ x))) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ t : ℝ in 𝓝 (0 : ℝ), φ t ∈ spectrum ℂ ((A + t • E).map Complex.ofReal)) ∧
      (∀ᶠ p : ℝ × ℂ in 𝓝 (0, (μ : ℂ)),
        p.2 ∈ spectrum ℂ ((A + p.1 • E).map Complex.ofReal) ↔ φ p.1 = p.2) := by
  have hA : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hAh
  have hx : x ⬝ᵥ x = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hxn, one_pow]
  let z : n → ℂ := Complex.ofReal ∘ x
  have hzz : z ⬝ᵥ z = 1 := by
    simpa [z, hx, Complex.ofRealHom] using (Complex.ofRealHom.map_dotProduct x x).symm
  have hz : z ≠ 0 := by intro h; simp [h] at hzz
  have hAz : (A.map Complex.ofReal) *ᵥ z = (μ : ℂ) • z := by
    funext i
    simpa [z, hAx, Pi.smul_apply, Complex.ofRealHom] using (Complex.ofRealHom.map_mulVec A x i).symm
  have hzA : z ᵥ* (A.map Complex.ofReal) = (μ : ℂ) • z := by
    have htrans : (A.map Complex.ofReal).transpose = A.map Complex.ofReal := by
      ext i j
      exact congrArg Complex.ofReal (congrFun (congrFun hA i) j)
    rw [← htrans, Matrix.vecMul_transpose]
    exact hAz
  have hmult : (A.map Complex.ofReal).charpoly.rootMultiplicity (μ : ℂ) = 1 := by
    have hchar : (A.map Complex.ofReal).charpoly = Polynomial.map Complex.ofRealHom A.charpoly :=
      Matrix.charpoly_map A Complex.ofRealHom
    rw [hchar]
    simpa only [hμ, Complex.ofRealHom_eq_coe] using
      (Polynomial.eq_rootMultiplicity_map (p := A.charpoly) (f := Complex.ofRealHom)
        Complex.ofReal_injective μ).symm
  obtain ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique⟩ :=
    exists_real_parameter_eigenvalue_branch_of_simple (E.map Complex.ofReal) hz hz hAz hzA hmult
  have hentry : (z ⬝ᵥ ((E.map Complex.ofReal) *ᵥ z)) / (z ⬝ᵥ z) =
      Complex.ofReal (x ⬝ᵥ (E *ᵥ x)) := by
    rw [hzz, div_one]
    simp [z, dotProduct, Matrix.mulVec, Complex.ofReal_sum]
  have hmap (t : ℝ) : (A + t • E).map Complex.ofReal =
      A.map Complex.ofReal + (t : ℂ) • E.map Complex.ofReal := by
    ext i j
    simp
  exact ⟨φ, hφ₀, hφcont, hentry ▸ hφderiv, hφnear, by simpa only [hmap] using hφspec,
    by simpa only [hmap] using hφunique⟩

end NLAlib
