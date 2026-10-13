import NLAlib.Matrix.Perturbation.SimpleEigenvalueContinuousBranch
import NLAlib.Matrix.Perturbation.SimpleEigenvalueSchurSpectrum
import NLAlib.Matrix.Spectral.EigenvectorDeflationBlocks
import Mathlib.Analysis.Complex.Polynomial.Basic
/-!
# The local branch of a simple eigenvalue

The scalar implicit branch is transported through a left–right normalized
similarity to an locally unique eigenvalue of the original perturbed
matrix. Its derivative is the normalized left–right perturbation pairing.
Source: Horn–Johnson (2013), Theorem 6.3.12; atlas `simple-eigenvalue-perturbation`.
-/

noncomputable section
open Filter
open scoped Matrix Topology

namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The trailing resolvent remains invertible near a separated scalar
eigenvalue. Source: Horn–Johnson (2013), proof of Theorem 6.3.12. -/
theorem eventually_isUnit_shifted_pencil (μ : ℂ) (B F : Matrix n n ℂ)
    (hμ : μ ∉ spectrum ℂ B) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 0, IsUnit ((μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) := by
  have hunit : IsUnit (μ • (1 : Matrix n n ℂ) - B) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hμ
  have hcont : Continuous (fun p : ℂ × ℂ =>
      (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) := by fun_prop
  exact (hcont.continuousAt (x := 0)).preimage_mem_nhds (by simpa using Units.isOpen.mem_nhds hunit)

open scoped Matrix.Norms.L2Operator in
/-- A separated scalar block has a locally unique eigenvalue branch,
with derivative equal to the leading perturbation entry.
Horn–Johnson (2013), Theorem 6.3.12; the parameter is complex. -/
theorem exists_eigenvalue_branch_of_scalar_block
    {l : Type*} [Unique l] (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧ HasDerivAt φ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), ContinuousAt φ t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ
        (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
          t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
            (Matrix.replicateRow l b) (Matrix.replicateCol l c) F)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), μ), p.2 ∈ spectrum ℂ
        (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
          p.1 • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
            (Matrix.replicateRow l b) (Matrix.replicateCol l c) F) ↔ φ p.1 = p.2) := by
  obtain ⟨ψ, hψ₀, hψcont, hψderiv, hψnear, hψspec, hψunique⟩ :=
    exists_continuous_simpleEigenvalueSchurFunction_branch μ a B F b c hμ
  let φ : ℂ → ℂ := fun t => μ + ψ t
  have hφderiv : HasDerivAt φ a 0 := hψderiv.const_add μ
  have hK := eventually_isUnit_shifted_pencil μ B F hμ
  refine ⟨φ, by simp [φ, hψ₀], hφderiv.continuousAt, hφderiv,
    hψnear.mono (fun t ht => ht.const_add μ), ?_, ?_⟩
  · have hgraph : Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
      change Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 ((0 : ℂ), 0))
      simpa only [hψ₀, id_eq] using (continuousAt_id.prodMk hψcont).tendsto
    filter_upwards [hψspec, hgraph.eventually hK] with t ht hKt
    exact (mem_spectrum_scalar_block_iff_schur_eq_zero μ a t (ψ t) B F b c hKt).mpr ht
  · have hshift : Tendsto (fun p : ℂ × ℂ => (p.1, p.2 - μ))
        (𝓝 ((0 : ℂ), μ)) (𝓝 (0 : ℂ × ℂ)) := by
      have hcont : Continuous (fun p : ℂ × ℂ => (p.1, p.2 - μ)) := by fun_prop
      change Tendsto (fun p : ℂ × ℂ => (p.1, p.2 - μ))
        (𝓝 ((0 : ℂ), μ)) (𝓝 ((0 : ℂ), 0))
      simpa using (hcont.continuousAt (x := ((0 : ℂ), μ))).tendsto
    filter_upwards [hshift.eventually hK, hshift.eventually hψunique] with p hpK hpψ
    have hs := mem_spectrum_scalar_block_iff_schur_eq_zero
      (l := l) μ a p.1 (p.2 - μ) B F b c hpK
    rw [add_sub_cancel] at hs
    exact hs.trans (hpψ.trans (by dsimp [φ]; constructor <;> intro h <;> linear_combination h))

open scoped Matrix.Norms.L2Operator in
/-- A simple eigenvalue has a locally unique continuous branch, complex
differentiable at zero with derivative the normalized left–right pairing.
The left eigenvector is supplied as its row (use the conjugate of a left
column). Source: Horn–Johnson (2013), Theorem 6.3.12.
atlas: simple-eigenvalue-perturbation -/
theorem exists_eigenvalue_branch_of_simple
    {A : Matrix n n ℂ} (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ ContinuousAt φ 0 ∧
      HasDerivAt φ ((y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), ContinuousAt φ t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (A + t • E)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), μ), p.2 ∈ spectrum ℂ (A + p.1 • E) ↔ φ p.1 = p.2) := by
  classical
  obtain ⟨S, i, hS, hcol, hrow, hright, hleft, hsep⟩ :=
    exists_simple_eigenvalue_isolated_similarity hx hy hAx hyA hμ
  let L := {j : n // j = i}
  let R := {j : n // j ≠ i}
  let : Unique L := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  let e : L ⊕ R ≃ n := Equiv.sumCompl (fun j => j = i)
  let M := S⁻¹ * A * S
  let G := S⁻¹ * E * S
  let B : Matrix R R ℂ := M.submatrix Subtype.val Subtype.val
  let F : Matrix R R ℂ := G.submatrix Subtype.val Subtype.val
  let b : R → ℂ := fun j => G i j.val
  let c : R → ℂ := fun j => G j.val i
  have hM : M.submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : L => μ)) 0 0 B :=
    submatrix_eq_fromBlocks_of_isolated_coordinate M i μ hright hleft
  have hG : G.submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : L => G i i))
        (Matrix.replicateRow L b) (Matrix.replicateCol L c) F :=
    submatrix_eq_fromBlocks_scalar_row_col G i
  have hspec (t z : ℂ) : z ∈ spectrum ℂ
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : L => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : L => G i i))
          (Matrix.replicateRow L b) (Matrix.replicateCol L c) F) ↔
        z ∈ spectrum ℂ (A + t • E) := by
    rw [← hM, ← hG]
    change z ∈ spectrum ℂ ((M + t • G).submatrix e e) ↔ _
    have heq : M + t • G = S⁻¹ * (A + t • E) * S := by
      simp only [M, G, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [heq, Matrix.mem_spectrum_iff_isRoot_charpoly]
    have hchar := Matrix.charpoly_reindex e.symm (S⁻¹ * (A + t • E) * S)
    change ((S⁻¹ * (A + t • E) * S).submatrix e e).charpoly = _ at hchar
    rw [hchar, ← Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact mem_spectrum_nonsing_inv_mul_mul_iff (A + t • E) S hS z
  obtain ⟨φ, hφ₀, hφcont, hφderiv, hφnear, hφspec, hφunique⟩ :=
    exists_eigenvalue_branch_of_scalar_block (l := L) μ (G i i) B F b c hsep
  have hentry : G i i = (y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x) :=
    nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div S E i x y hcol hrow
  refine ⟨φ, hφ₀, hφcont, hentry ▸ hφderiv, hφnear, ?_, ?_⟩
  · apply hφspec.mono
    intro t ht
    apply (hspec t (φ t)).mp
    convert! ht using 1
    congr 10 <;> exact Subsingleton.elim _ _
  · apply hφunique.mono
    intro p hp
    apply (hspec p.1 p.2).symm.trans
    convert! hp using 1
    apply Iff.of_eq
    congr 10 <;> exact Subsingleton.elim _ _

end NLAlib
