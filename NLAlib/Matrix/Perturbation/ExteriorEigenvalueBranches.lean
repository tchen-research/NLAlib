import NLAlib.Matrix.Perturbation.SimpleEigenvalueAnalyticBranch

/-!
# Simultaneous exterior branches of a diagonal matrix pencil

Distinct diagonal slopes give all eigenvalue branches on one common exterior
domain. They are holomorphic, pairwise distinct, and have the required affine
asymptotes. This is the exterior branch construction of Stahl (2013), Theorem 2;
it does not construct the global spectral surface or its positive boundary.
The associated atlas target is `trace-exponential-stahl`.
-/

noncomputable section
open Filter
open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Distinct diagonal slopes give a complete indexed collection of distinct
analytic eigenvalue branches outside one common disk. Their affine offsets
converge to the corresponding diagonal entries of the perturbation, as in
Stahl (2013), Theorem 2.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_eigenvalue_branches_of_diagonal
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z - z * d i) (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A + z • Matrix.diagonal d)) ∧
        Function.Injective (fun i => branch i z) := by
  classical
  choose φ g hφ₀ hφa hga hφspec hφeq using
    fun i => exists_analytic_eigenvalue_branch_diagonal_expansion d hd A i
  let branch : n → ℂ → ℂ := fun i z => z * φ i z⁻¹
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have hpair : ∀ᶠ t in 𝓝 (0 : ℂ), Function.Injective (fun i => φ i t) := by
    have hp : ∀ i j, ∀ᶠ t in 𝓝 (0 : ℂ), φ i t = φ j t → i = j := by
      intro i j
      by_cases hij : i = j
      · exact Eventually.of_forall (fun _ _ => hij)
      · have hn : φ i 0 - φ j 0 ≠ 0 := by
          rw [hφ₀, hφ₀]
          exact sub_ne_zero.mpr (hd.ne hij)
        filter_upwards [((hφa i).continuousAt.sub (hφa j).continuousAt).tendsto.eventually_ne hn]
          with t ht heq
        exact False.elim (ht (sub_eq_zero.mpr heq))
    have hp' : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j, φ i t = φ j t → i = j := by
      simpa only [Filter.eventually_all] using hp
    exact hp'
  have hall : ∀ᶠ t in 𝓝 (0 : ℂ),
      ∀ i, AnalyticAt ℂ (φ i) t ∧ φ i t ∈ spectrum ℂ (Matrix.diagonal d + t • A) := by
    simp only [Filter.eventually_all]
    intro i
    exact (hφa i).eventually_analyticAt.and (hφspec i)
  have hnz : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    intro hzero
    norm_num [hzero] at hz
  have hext : ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      (∀ i, AnalyticAt ℂ (branch i) z ∧
        branch i z ∈ spectrum ℂ (A + z • Matrix.diagonal d)) ∧
        Function.Injective (fun i => branch i z) := by
    filter_upwards [hi.eventually hall, hi.eventually hpair, hnz] with z hz hp hzne
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · exact analyticAt_id.mul ((hz i).1.comp (analyticAt_inv hzne))
    · have hs := (spectrum.smul_mem_smul_iff (R := ℂ)
        (r := Units.mk0 z hzne) (a := Matrix.diagonal d + z⁻¹ • A) (s := φ i z⁻¹)).mpr
          (hz i).2
      simpa only [Units.smul_def, Units.val_mk0, smul_eq_mul, smul_add,
        smul_smul, mul_inv_cancel₀ hzne, one_smul, add_comm] using hs
    · intro i j hij
      apply hp
      exact mul_left_cancel₀ hzne hij
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hext
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), branch, ?_, ?_⟩
  · intro i
    refine ⟨fun z hz => ((hR ((le_max_left R 1).trans hz.le)).1 i).1.differentiableAt.differentiableWithinAt,
      ?_⟩
    have hlim : Tendsto (fun z : ℂ => A i i + z⁻¹ * g i z⁻¹)
        (Bornology.cobounded ℂ) (𝓝 (A i i)) := by
      have hg := (hga i).continuousAt.tendsto.comp hi
      simpa using (tendsto_const_nhds.add (hi.mul hg))
    apply hlim.congr'
    filter_upwards [hi.eventually (hφeq i), hnz] with z hz hzne
    dsimp [branch]
    rw [hz]
    field_simp
    ring
  · intro z hz
    have h := hR ((le_max_left R 1).trans hz.le)
    exact ⟨fun i => (h.1 i).2, h.2⟩

open scoped Matrix.Norms.L2Operator in
/-- In Stahl's sign convention, distinct real slopes yield a common exterior
domain of distinct holomorphic eigenvalues of `A - z B`, with
`branchᵢ(z) + bᵢ z → Aᵢᵢ`. Hermitian symmetry is unnecessary for this local
construction at infinity. Source: Stahl (2013), Theorem 2.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_eigenvalue_branches_sub_real_diagonal
    (b : n → ℝ) (hb : Function.Injective b) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i z) := by
  have hd : Function.Injective (fun i => -(b i : ℂ)) :=
    neg_injective.comp (Complex.ofReal_injective.comp hb)
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_of_diagonal (fun i => -(b i : ℂ)) hd A
  refine ⟨R, hR, branch, ?_, ?_⟩
  · intro i
    refine ⟨(hbranch i).1, ?_⟩
    simpa only [mul_neg, sub_neg_eq_add, mul_comm] using (hbranch i).2
  · intro z hz
    have hD : (Matrix.diagonal (fun i => -(b i : ℂ)) : Matrix n n ℂ) =
        -Matrix.diagonal (fun i => (b i : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    simpa only [hD, smul_neg, ← sub_eq_add_neg] using hspec z hz

end NLAlib
