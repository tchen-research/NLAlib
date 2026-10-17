import NLAlib.Matrix.Perturbation.ExteriorEigenvalueBranches
import NLAlib.Matrix.Functions.TraceExponentialSpectrum

/-!
# Schwarz reflection of exterior spectral branches

For Hermitian matrix pencils with real distinct diagonal slopes, conjugation
preserves the spectral equation. The distinct asymptotic labels then force
each exterior branch to satisfy Schwarz reflection. This supplies realness,
but not positivity, of the contour density in Stahl (2013), Theorem 2.
The associated atlas target is `trace-exponential-stahl`.
-/

noncomputable section

open Filter Complex
open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating a spectral point gives a spectral point of the adjoint matrix.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem conj_mem_spectrum_conjTranspose {M : Matrix n n ℂ} {w : ℂ}
    (hw : w ∈ spectrum ℂ M) : conj w ∈ spectrum ℂ Mᴴ := by
  rw [spectrum.mem_iff] at hw ⊢
  have heq : algebraMap ℂ (Matrix n n ℂ) (conj w) - Mᴴ =
      (algebraMap ℂ (Matrix n n ℂ) w - M)ᴴ := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_smul]
  rw [heq, Matrix.isUnit_conjTranspose]
  exact hw

private theorem tendsto_conj_cobounded :
    Tendsto (conj : ℂ → ℂ) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa only [norm_conj] using (tendsto_norm_cobounded_atTop (E := ℂ))

private theorem tendsto_branch_mul_inv {branch : ℂ → ℂ} {a b : ℂ}
    (h : Tendsto (fun z => branch z + b * z) (Bornology.cobounded ℂ) (𝓝 a)) :
    Tendsto (fun z => branch z * z⁻¹) (Bornology.cobounded ℂ) (𝓝 (-b)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have ht : Tendsto (fun z => (branch z + b * z) * z⁻¹ - b)
      (Bornology.cobounded ℂ) (𝓝 (-b)) := by
    simpa using (h.mul hi).sub_const b
  apply ht.congr'
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
  have hzne : z ≠ 0 := by intro hzero; norm_num [hzero] at hz
  field_simp
  ring

open scoped Matrix.Norms.L2Operator in
/-- A complete exterior branch family of a Hermitian pencil is
Schwarz-symmetric outside a possibly larger disk. Distinct real asymptotic
slopes determine the branch label, so no branch symmetry is assumed.
Source: Stahl (2013), §§3–4.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem eventually_exterior_eigenvalue_branches_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) {R : ℝ} {branch : n → ℂ → ℂ}
    (hlim : ∀ i, Tendsto (fun z => branch i z + (b i : ℂ) * z)
      (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hspec : ∀ z, R < ‖z‖ →
      (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i z)) :
    ∀ᶠ z in Bornology.cobounded ℂ, ∀ i, branch i (conj z) = conj (branch i z) := by
  have hnorm (i : n) : Tendsto (fun z => branch i z * z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (-(b i : ℂ))) := tendsto_branch_mul_inv (hlim i)
  have href (i : n) : Tendsto (fun z => conj (branch i (conj z)) * z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (-(b i : ℂ))) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp
      ((hnorm i).comp tendsto_conj_cobounded)
    simpa [Function.comp_def] using h
  have hneq : ∀ i j, ∀ᶠ z in Bornology.cobounded ℂ,
      i ≠ j → conj (branch i (conj z)) ≠ branch j z := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    · have hn : -(b i : ℂ) - -(b j : ℂ) ≠ 0 := by
        intro heq
        exact hij (hb (Complex.ofReal_injective (neg_injective (sub_eq_zero.mp heq))))
      filter_upwards [((href i).sub (hnorm j)).eventually_ne hn] with z hz _ heq
      exact hz (by rw [heq]; ring)
  have hneq' : ∀ᶠ z in Bornology.cobounded ℂ, ∀ i j,
      i ≠ j → conj (branch i (conj z)) ≠ branch j z := by
    simpa only [Filter.eventually_all] using hneq
  filter_upwards [hneq', (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop R]
    with z hz hR i
  have hs := hspec z hR
  have hcR : R < ‖conj z‖ := by simpa using hR
  have hci := conj_mem_spectrum_conjTranspose ((hspec (conj z) hcR).1 i)
  have hstar : (A - conj z • Matrix.diagonal (fun i => (b i : ℂ)))ᴴ =
      A - z • Matrix.diagonal (fun i => (b i : ℂ)) := by
    have hD : (Matrix.diagonal (fun i => (b i : ℂ)) : Matrix n n ℂ).IsHermitian :=
      Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hD.eq]
  rw [hstar, spectrum_eq_range_of_injective_mem_spectrum _ _ hs.2 hs.1] at hci
  obtain ⟨j, hj⟩ := hci
  have hji : i = j := by
    by_contra hij
    exact hz i j hij hj.symm
  subst j
  simpa using (congrArg conj hj).symm

open scoped Matrix.Norms.L2Operator in
/-- Hermitian pencils with distinct real diagonal slopes admit exterior branches satisfying Schwarz reflection on one common exterior
domain. The branches and their symmetry are both constructed, not assumed.
Source: Stahl (2013), §§3–4; realness step toward the contour representation.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_eigenvalue_branches_sub_real_diagonal_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (b : n → ℝ) (hb : Function.Injective b) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      (∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
          Function.Injective (fun i => branch i z)) ∧
      ∀ i z, R < ‖z‖ → branch i (conj z) = conj (branch i z) := by
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_sub_real_diagonal b hb A
  have href := eventually_exterior_eigenvalue_branches_conj_eq hA b hb
    (fun i => (hbranch i).2) hspec
  obtain ⟨S, _, hS⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp href
  refine ⟨max R S, hR.trans_le (le_max_left _ _), branch, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hbranch i).1.mono (fun z hz => (le_max_left R S).trans_lt hz), (hbranch i).2⟩
  · intro z hz
    exact hspec z ((le_max_left R S).trans_lt hz)
  · intro i z hz
    exact hS ((le_max_right R S).trans hz.le) i

end NLAlib
