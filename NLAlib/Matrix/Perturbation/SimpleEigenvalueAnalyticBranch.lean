import NLAlib.Matrix.Perturbation.SimpleEigenvaluePerturbation
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Analytic branches of separated eigenvalues

The scalar Schur equation is analytic near a separated eigenvalue.
The analytic implicit-function theorem therefore supplies a holomorphic
eigenvalue branch, rather than merely a derivative at the base point.
This is local infrastructure for Stahl's trace-exponential representation
(Stahl 2013, Theorem 2); it does not assert positivity of its contour density.
The associated atlas target is `trace-exponential-stahl`.
-/

noncomputable section
open Filter
open scoped Matrix Topology ContDiff

namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The scalar Schur equation is analytic near the origin when the trailing
block excludes the leading eigenvalue. The matrix inverse in the definition
is the Banach-algebra inverse on a neighborhood of the base point.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem analyticAt_simpleEigenvalueSchurFunction (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    AnalyticAt ℂ (simpleEigenvalueSchurFunction μ a B F b c) 0 := by
  have hunit : IsUnit (μ • (1 : Matrix n n ℂ) - B) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hμ
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) 0 :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) 0 :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
  have hK : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) 0 :=
    (((analyticAt_const.add hsnd).smul analyticAt_const).sub
      analyticAt_const).sub (hfst.smul analyticAt_const)
  have hi : AnalyticAt ℂ Ring.inverse
      ((μ + (0 : ℂ × ℂ).2) • (1 : Matrix n n ℂ) - B - (0 : ℂ × ℂ).1 • F) := by
    simpa only [Prod.fst_zero, Prod.snd_zero, add_zero, zero_smul, sub_zero,
      hunit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hunit.unit)
  exact (hsnd.sub (hfst.mul analyticAt_const)).sub
    ((hfst.pow 2).mul (((schurResolventCoupling b c).analyticAt _).comp
      (hi.comp (f := fun p : ℂ × ℂ => (μ + p.2) • (1 : Matrix n n ℂ) - B - p.1 • F) hK)))

open scoped Matrix.Norms.L2Operator in
/-- The separated scalar Schur equation admits an analytic local shift
branch with derivative equal to the leading perturbation entry. This proves
holomorphy on a neighborhood, as needed for exterior spectral branches in
Stahl (2013), Theorem 2.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_analytic_simpleEigenvalueSchurFunction_branch (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ ψ : ℂ → ℂ, ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ HasDerivAt ψ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), simpleEigenvalueSchurFunction μ a B F b c (t, ψ t) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        simpleEigenvalueSchurFunction μ a B F b c p = 0 ↔ ψ p.1 = p.2) := by
  let f := simpleEigenvalueSchurFunction μ a B F b c
  let D : (ℂ × ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hf : HasStrictFDerivAt f D 0 :=
    hasStrictFDerivAt_simpleEigenvalueSchurFunction μ a B F b c hμ
  have hreg : ContDiffAt ℂ ω f 0 :=
    (analyticAt_simpleEigenvalueSchurFunction μ a B F b c hμ).contDiffAt
  have hD₂ : D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ = ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    change z - a * 0 = z
    ring
  have hif : (fderiv ℂ f 0 ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hf.hasFDerivAt.fderiv, hD₂]
    exact ⟨ContinuousLinearEquiv.refl ℂ ℂ, rfl⟩
  let ψ := hreg.implicitFunction (by simp : (ω : ℕ∞ω) ≠ 0) hif
  have hψ₀ : ψ 0 = 0 := hreg.implicitFunction_apply_self (by simp) hif
  have hψanalytic : AnalyticAt ℂ ψ 0 :=
    (hreg.contDiffAt_implicitFunction (by simp) hif).analyticAt
  have hderiv : -(fderiv ℂ f 0 ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).inverse ∘L
      (fderiv ℂ f 0 ∘L ContinuousLinearMap.inl ℂ ℂ ℂ) =
        a • ContinuousLinearMap.id ℂ ℂ := by
    rw [hf.hasFDerivAt.fderiv, hD₂, ContinuousLinearMap.inverse_id]
    apply ContinuousLinearMap.ext
    intro z
    change -(0 - a * z) = a * z
    ring
  have hψderiv : HasDerivAt ψ a 0 := by
    have h := (hreg.hasStrictFDerivAt_implicitFunction (by simp) hif).hasFDerivAt.hasDerivAt
    rw [hderiv] at h
    simpa using h
  have hf₀ : f 0 = 0 := by simp [f, simpleEigenvalueSchurFunction]
  refine ⟨ψ, hψ₀, hψanalytic, hψderiv, ?_, ?_⟩
  · simpa only [hf₀, Prod.fst_zero] using
      hreg.eventually_apply_implicitFunction (by simp) hif
  · simpa only [hf₀] using hreg.eventually_apply_eq_iff_implicitFunction (by simp) hif

open scoped Matrix.Norms.L2Operator in
/-- A separated scalar block has an analytic eigenvalue branch. The
derivative at the base point is its leading perturbation entry.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_analytic_eigenvalue_branch_of_scalar_block
    {l : Type*} [Unique l] (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ AnalyticAt ℂ φ 0 ∧ HasDerivAt φ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ
        (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
          t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
            (Matrix.replicateRow l b) (Matrix.replicateCol l c) F)) := by
  obtain ⟨ψ, hψ₀, hψanalytic, hψderiv, hψeq, _⟩ :=
    exists_analytic_simpleEigenvalueSchurFunction_branch μ a B F b c hμ
  let φ : ℂ → ℂ := fun t => μ + ψ t
  have hgraph : Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    change Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 ((0 : ℂ), 0))
    simpa only [hψ₀, id_eq] using
      (continuousAt_id.prodMk hψderiv.continuousAt).tendsto
  refine ⟨φ, by simp [φ, hψ₀], analyticAt_const.add hψanalytic,
    hψderiv.const_add μ, ?_⟩
  filter_upwards [hψeq,
    hgraph.eventually (eventually_isUnit_shifted_pencil μ B F hμ)] with t ht hKt
  exact (mem_spectrum_scalar_block_iff_schur_eq_zero μ a t (ψ t) B F b c hKt).mpr ht

open scoped Matrix.Norms.L2Operator in
/-- Each distinct diagonal entry of a diagonal pencil extends to a analytic eigenvalue branch, with derivative the corresponding diagonal
entry of the perturbation. This supplies the reciprocal-coordinate branches
near infinity in Stahl (2013), Theorem 2.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_analytic_eigenvalue_branch_of_diagonal
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) (i : n) :
    ∃ φ : ℂ → ℂ, φ 0 = d i ∧ AnalyticAt ℂ φ 0 ∧ HasDerivAt φ (A i i) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (Matrix.diagonal d + t • A)) := by
  classical
  let L := {j : n // j = i}
  let R := {j : n // j ≠ i}
  let : Unique L := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  let e : L ⊕ R ≃ n := Equiv.sumCompl (fun j => j = i)
  let B : Matrix R R ℂ := Matrix.diagonal (fun j => d j.val)
  let F : Matrix R R ℂ := A.submatrix Subtype.val Subtype.val
  let b : R → ℂ := fun j => A i j.val
  let c : R → ℂ := fun j => A j.val i
  have hsep : d i ∉ spectrum ℂ B := by
    rw [spectrum_diagonal]
    rintro ⟨j, hj⟩
    exact j.property (hd hj)
  have hM : (Matrix.diagonal d).submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : L => d i)) 0 0 B := by
    have hB : (Matrix.diagonal d).submatrix (fun j : R => j.val) (fun j : R => j.val) = B := by
      ext j k
      simp only [B, Matrix.submatrix_apply, Matrix.diagonal_apply]
      exact if_congr (Subtype.val_injective.eq_iff) rfl rfl
    have h := submatrix_eq_fromBlocks_of_isolated_coordinate (Matrix.diagonal d) i (d i)
      (fun j => by by_cases hj : j = i <;> simp [hj])
      (fun j => by by_cases hj : j = i <;> simp [hj, Ne.symm])
    convert! h using 1
    congr 1
    exact hB.symm
  have hA : A.submatrix e e =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : L => A i i))
        (Matrix.replicateRow L b) (Matrix.replicateCol L c) F :=
    submatrix_eq_fromBlocks_scalar_row_col A i
  obtain ⟨φ, hφ₀, hφanalytic, hφderiv, hφspec⟩ :=
    exists_analytic_eigenvalue_branch_of_scalar_block (l := L) (d i) (A i i) B F b c hsep
  refine ⟨φ, hφ₀, hφanalytic, hφderiv, ?_⟩
  filter_upwards [hφspec] with t ht
  have ht' : φ t ∈ spectrum ℂ ((Matrix.diagonal d + t • A).submatrix e e) := by
    change φ t ∈ spectrum ℂ ((Matrix.diagonal d).submatrix e e + t • A.submatrix e e)
    rw [hM, hA]
    convert! ht using 1
    congr 10 <;> exact Subsingleton.elim _ _
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at ht' ⊢
  have hc := Matrix.charpoly_reindex e.symm (Matrix.diagonal d + t • A)
  exact hc ▸ ht'

open scoped Matrix.Norms.L2Operator in
/-- The analytic diagonal-pencil branch has its first two Taylor terms with
an analytic quadratic remainder. Unlike a derivative statement alone, this
gives the `O(z⁻¹)` remainder after reciprocal substitution at infinity.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_analytic_eigenvalue_branch_diagonal_expansion
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) (i : n) :
    ∃ φ g : ℂ → ℂ, φ 0 = d i ∧ AnalyticAt ℂ φ 0 ∧ AnalyticAt ℂ g 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t ∈ spectrum ℂ (Matrix.diagonal d + t • A)) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), φ t = d i + t * A i i + t ^ 2 * g t) := by
  obtain ⟨φ, hφ₀, hφanalytic, hφderiv, hφspec⟩ :=
    exists_analytic_eigenvalue_branch_of_diagonal d hd A i
  obtain ⟨g, hga, hg⟩ := hφanalytic.exists_eventuallyEq_sum_add_pow_mul 2
  refine ⟨φ, g, hφ₀, hφanalytic, hga, hφspec, ?_⟩
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    hφ₀, hφderiv.deriv, smul_eq_mul] using hg

open scoped Matrix.Norms.L2Operator in
/-- Distinct diagonal slopes give holomorphic exterior eigenvalue
branches with expansion `z * dᵢ + Aᵢᵢ + O(z⁻¹)`. Equivalently, the branch
has an analytic reciprocal-coordinate remainder. This is the local branch
construction at infinity used by Stahl (2013), Theorem 2, without any
global continuation or spectral-surface positivity hypothesis.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_eigenvalue_branch_of_diagonal
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) (i : n) :
    ∃ lam g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      (∀ᶠ z in Bornology.cobounded ℂ, AnalyticAt ℂ lam z) ∧
      (∀ᶠ z in Bornology.cobounded ℂ,
        lam z ∈ spectrum ℂ (A + z • Matrix.diagonal d)) ∧
      (∀ᶠ z in Bornology.cobounded ℂ,
        lam z = z * d i + A i i + z⁻¹ * g z⁻¹) ∧
      (fun z => lam z - (z * d i + A i i)) =O[Bornology.cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨φ, g, _, hφa, hga, hφspec, hφeq⟩ :=
    exists_analytic_eigenvalue_branch_diagonal_expansion d hd A i
  let lam : ℂ → ℂ := fun z => z * φ z⁻¹
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have hnz : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    intro hzero
    norm_num [hzero] at hz
  have hlameq : ∀ᶠ z in Bornology.cobounded ℂ,
      lam z = z * d i + A i i + z⁻¹ * g z⁻¹ := by
    filter_upwards [hi.eventually hφeq, hnz] with z hz hzne
    dsimp [lam]
    rw [hz]
    field_simp
  refine ⟨lam, g, hga, ?_, ?_, hlameq, ?_⟩
  · filter_upwards [hi.eventually hφa.eventually_analyticAt, hnz] with z hz hzne
    exact analyticAt_id.mul (hz.comp (analyticAt_inv hzne))
  · filter_upwards [hi.eventually hφspec, hnz] with z hz hzne
    have hs := (spectrum.smul_mem_smul_iff (R := ℂ)
      (r := Units.mk0 z hzne) (a := Matrix.diagonal d + z⁻¹ • A) (s := φ z⁻¹)).mpr hz
    simpa only [Units.smul_def, Units.val_mk0, smul_eq_mul, smul_add,
      smul_smul, mul_inv_cancel₀ hzne, one_smul, add_comm] using hs
  · have hgO : (fun z : ℂ => g z⁻¹) =O[Bornology.cobounded ℂ] (fun _ => (1 : ℂ)) :=
      hga.continuousAt.isBigO.comp_tendsto hi
    have hO := (Asymptotics.isBigO_refl (fun z : ℂ => z⁻¹)
      (Bornology.cobounded ℂ)).mul hgO
    apply hO.congr' ?_ (by simp)
    filter_upwards [hlameq] with z hz
    rw [hz]
    ring

end NLAlib
